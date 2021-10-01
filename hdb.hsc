import Foreign
import Foreign.C
import Foreign.Ptr
import System.Environment
import Control.Exception
import Data.IORef
import Data.Bits
import qualified Data.Map as Map
import GHC.Exts.Heap
import GHC.Exts.Heap.InfoTable

main = do
  args <- getArgs
  (withArgs args $ \c_prog_args@(c_prog:_) ->
   withArray0 nullPtr c_prog_args $ \c_prog_args ->
   withCallbacks $ \c_callbacks -> do
     debugger_execv c_prog c_prog_args c_callbacks)
  where
    withArgs []         fn = fn []
    withArgs (arg:args) fn =
      withArgs args $ \c_args ->
      withCString arg $ \c_arg ->
        fn (c_arg:c_args)

    withCallbacks :: (Ptr DebuggerCallbacks -> IO a) -> IO a
    withCallbacks fn = do
      ref <- newIORef Map.empty
      (bracket (wrapRegisterInfo (register_info ref)) freeHaskellFunPtr $ \c_register_info ->
       bracket (wrapBreakpointHit (breakpoint_hit ref)) freeHaskellFunPtr $ \c_breakpoint_hit ->
       allocaBytes (#size DebuggerCallbacks) $ \c_callbacks -> do
         (#poke DebuggerCallbacks, register_info) c_callbacks c_register_info
         (#poke DebuggerCallbacks, breakpoint_hit) c_callbacks c_breakpoint_hit
         fn c_callbacks)

    register_info ref c_name addr save_word c_infoTable = do
      name <- peekCString c_name
      itbl <- peekItbl c_infoTable
      breakpoints <- readIORef ref
      writeIORef ref $! Map.insert addr (name,save_word,itbl) breakpoints

    breakpoint_hit ref addr pclosure p_save_word = do
      breakpoints <- readIORef ref
      case Map.lookup addr breakpoints of
        Just (name,save_word,itbl) -> do poke p_save_word save_word
                                         mb_closure <- peekClosure name itbl pclosure        
                                         print (name,mb_closure)
                                         return 1
        Nothing                    -> do return 0
      where
        peekClosure name itbl pclosure
          | pclosure /= nullPtr =
              case tipe itbl of
                CONSTR        -> constrClosure 
                CONSTR_1_0    -> constrClosure
                CONSTR_0_1    -> constrClosure
                CONSTR_2_0    -> constrClosure
                CONSTR_1_1    -> constrClosure
                CONSTR_0_2    -> constrClosure
                FUN           -> thunkClosure FunClosure
                FUN_1_0       -> thunkClosure FunClosure
                FUN_0_1       -> thunkClosure FunClosure
                FUN_2_0       -> thunkClosure FunClosure
                FUN_1_1       -> thunkClosure FunClosure
                FUN_0_2       -> thunkClosure FunClosure
                THUNK         -> thunkClosure ThunkClosure
                THUNK_1_0     -> thunkClosure ThunkClosure
                THUNK_0_1     -> thunkClosure ThunkClosure
                THUNK_2_0     -> thunkClosure ThunkClosure
                THUNK_1_1     -> thunkClosure ThunkClosure
                THUNK_0_2     -> thunkClosure ThunkClosure
                THUNK_STATIC  -> thunkClosure ThunkClosure
                THUNK_SELECTOR-> ptr1Closure SelectorClosure
                AP            -> papClosure APClosure
                PAP           -> papClosure PAPClosure
                AP_STACK      -> apStackClosure
                IND           -> ptr1Closure IndClosure
                IND_STATIC    -> ptr1Closure IndClosure
                BLOCKING_QUEUE-> blockingQueueClosure
                BLACKHOLE     -> ptr1Closure BlackholeClosure
                MVAR_CLEAN    -> mvarClosure
                MVAR_DIRTY    -> mvarClosure
                ARR_WORDS     -> arrWordsClosure
                MUT_ARR_PTRS_CLEAN -> mutArrPtrsClosure
                MUT_ARR_PTRS_DIRTY -> mutArrPtrsClosure
                MUT_ARR_PTRS_FROZEN_DIRTY -> mutArrPtrsClosure
                MUT_ARR_PTRS_FROZEN_CLEAN -> mutArrPtrsClosure
                MUT_VAR_CLEAN -> ptr1Closure MutVarClosure
                MUT_VAR_DIRTY -> ptr1Closure MutVarClosure
{-                WEAK          -> weakClosure -}
{-                SMALL_MUT_ARR_PTRS_CLEAN -> smallMutArrPtrsClosure
                SMALL_MUT_ARR_PTRS_DIRTY -> smallMutArrPtrsClosure
                SMALL_MUT_ARR_PTRS_FROZEN_DIRTY -> smallMutArrPtrsClosure
                SMALL_MUT_ARR_PTRS_FROZEN_CLEAN -> smallMutArrPtrsClosure-}
                _ | name == "base_GHCziInt_Izh_con_info" -> do
                                 ([],[w]) <- peekContent itbl pclosure
                                 return (Int64Closure PInt (fromIntegral w))
                _ | name == "base_GHCziWord_Wzh_con_info" -> do
                                 ([],[w]) <- peekContent itbl pclosure
                                 return (Word64Closure PWord (fromIntegral w))
                _ | name == "base_GHCziInt_I64zh_con_info" -> do
                                 ([],[w]) <- peekContent itbl pclosure
                                 return (Int64Closure PInt64 (fromIntegral w))
                _ | name == "base_GHCziWord_W64zh_con_info" -> do
                                 ([],[w]) <- peekContent itbl pclosure
                                 return (Word64Closure PWord64 (fromIntegral w))
                  | otherwise                              -> do
                                 (ps,ws) <- peekContent itbl pclosure
                                 return (OtherClosure itbl ps ws)
          | otherwise = return (UnsupportedClosure itbl)
          where
            constrClosure = do
              (ps,ws) <- peekContent itbl pclosure
              return (ConstrClosure itbl ps ws "" "" name)

            thunkClosure con = do
              (ps,ws) <- peekContent itbl pclosure
              return (con itbl ps ws)

            ptr1Closure con = do
              ([p],[]) <- peekContent itbl pclosure
              return (con itbl p)

            papClosure con = do
              (p:ps,[w]) <- peekContent itbl pclosure
              let arity  = fromIntegral (w .&. 0xFFFFFFFF)
              let n_args = fromIntegral ((w `shiftR` 32) .&. 0xFFFFFFFF)
              return (con itbl arity n_args p ps)

            apStackClosure = do
              (p:ps,[]) <- peekContent itbl pclosure
              return (APStackClosure itbl p ps)

            blockingQueueClosure = do
              ([p1,p2,p3,p4],[]) <- peekContent itbl pclosure
              return (BlockingQueueClosure itbl p1 p2 p3 p4)

            mvarClosure = do
              ([p1,p2,p3],[]) <- peekContent itbl pclosure
              return (MVarClosure itbl p1 p2 p3)

            arrWordsClosure = do
              ([],w:ws) <- peekContent itbl pclosure
              return (ArrWordsClosure itbl w ws)

{-            weakClosure = do
              ([p1,p2,p3,p4,p5],[]) <- peekContent itbl pclosure
              return (WeakClosure itbl p1 p2 p3 p4 p5) -}

            mutArrPtrsClosure = do
              (ps,[w1,w2]) <- peekContent itbl pclosure
              return (MutArrClosure itbl w1 w2 ps)

{-            smallMutArrPtrsClosure = do
              (ps,[w1,w2]) <- peekContent itbl pclosure
              return (SmallMutArrClosure itbl w1 w2 ps) -}

        peekContent itbl pclosure = do
          let pptrs  = castPtr pclosure :: Ptr (Ptr Closure)
              pwords = castPtr (pclosure `plusPtr` (fromIntegral (ptrs itbl * #size StgWord))) :: Ptr Word
          ps <- peekArray (fromIntegral (ptrs  itbl)) pptrs
          ws <- peekArray (fromIntegral (nptrs itbl)) pwords
          return (ps,ws)


#include "debugger.h"

data DebuggerCallbacks

foreign import ccall debugger_execv :: CString -> Ptr CString ->
                                       Ptr DebuggerCallbacks -> IO ()

type RegisterInfo = CString -> (#type GElf_Addr) -> (#type long) -> Ptr StgInfoTable -> IO ()

foreign import ccall "wrapper"
  wrapRegisterInfo :: RegisterInfo -> IO (FunPtr RegisterInfo)

type BreakpointHit = (#type GElf_Addr) -> Ptr () -> Ptr (#type long) -> IO CInt

foreign import ccall "wrapper"
  wrapBreakpointHit :: BreakpointHit -> IO (FunPtr BreakpointHit)

