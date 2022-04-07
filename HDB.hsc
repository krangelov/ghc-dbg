module HDB(startDebugger,LinkerName,SourceSpan,SourceSpans
          ,HeapPtr
          ,Debugger(..),DebuggerAction(..)
          ) where

import Foreign
import Foreign.C
import Foreign.Ptr
import Control.Exception
import Numeric (showHex)
import Data.IORef
import Data.Bits
import Data.Containers.ListUtils(nubOrd)
import qualified Data.Map as Map
import qualified Data.Set as Set
import GHC.Exts.Heap
import GHC.Exts.Heap.Utils
import GHC.Exts.Heap.InfoTable

type HeapPtr = (#type GElf_Addr)

type LinkerName = String

data Debugger
  = Debugger {
      peekClosure :: HeapPtr -> IO (Maybe (LinkerName,GenClosure HeapPtr)),
      getStack :: IO [(LinkerName,GenClosure HeapPtr)],
      getSourceFiles :: IO [FilePath],
      findFunction :: FilePath -> (Int,Int,Int,Int) -> IO [LinkerName],
      findSource :: LinkerName -> IO (Maybe SourceSpans)
    }

type SourceSpan  = (Int,Int,Int,Int)
type SourceSpans = (FilePath,[SourceSpan])

data DebuggerAction
  = Step
  | Stop
  | Continue [LinkerName]   -- ^ Continue the program until one of the
                            -- listed names is encountered

startDebugger :: [String] -> (Debugger -> LinkerName -> Maybe SourceSpans -> [HeapPtr] -> IO DebuggerAction) -> IO ()
startDebugger args handleEvent =
  withArgs args $ \c_prog_args@(c_prog:_) ->
  withArray0 nullPtr c_prog_args $ \c_prog_args ->
  withCallbacks $ \c_callbacks -> do
     errno <- debugger_execv c_prog c_prog_args c_callbacks
     if errno /= 0
       then ioError (errnoToIOError "startDebugger" (Errno errno) Nothing (Just (head args)))
       else return ()
  where
    withArgs []         fn = fn []
    withArgs (arg:args) fn =
      withArgs args $ \c_args ->
      withCString arg $ \c_arg ->
        fn (c_arg:c_args)

    withCallbacks :: (Ptr DebuggerCallbacks -> IO a) -> IO a
    withCallbacks fn = do
      ref <- newIORef ("",[],Map.empty,Map.empty,Step)
      (bracket (wrapRegisterCompUnit (register_comp_unit ref)) freeHaskellFunPtr $ \c_register_comp_unit ->
       bracket (wrapRegisterSubProg (register_subprog ref)) freeHaskellFunPtr $ \c_register_subprog ->
       bracket (wrapRegisterScope (register_scope ref)) freeHaskellFunPtr $ \c_register_scope ->
       bracket (wrapRegisterName (register_name ref)) freeHaskellFunPtr $ \c_register_name ->
       bracket (wrapBreakpointHit (breakpoint_hit ref)) freeHaskellFunPtr $ \c_breakpoint_hit ->
       allocaBytes (#size DebuggerCallbacks) $ \c_callbacks -> do
         (#poke DebuggerCallbacks, register_comp_unit) c_callbacks c_register_comp_unit
         (#poke DebuggerCallbacks, register_subprog) c_callbacks c_register_subprog
         (#poke DebuggerCallbacks, register_scope) c_callbacks c_register_scope
         (#poke DebuggerCallbacks, register_name) c_callbacks c_register_name
         (#poke DebuggerCallbacks, breakpoint_hit) c_callbacks c_breakpoint_hit
         fn c_callbacks)
      where
        register_comp_unit ref c_comp_dir c_fname = do
          comp_dir <- if c_comp_dir == nullPtr
                        then return ""
                        else peekCString c_comp_dir
          fname    <- if c_fname == nullPtr
                        then return ""
                        else peekCString c_fname
          (cu,ss,dies,names,action) <- readIORef ref
          writeIORef ref (comp_dir++fname,[],dies,names,action)

        register_subprog ref c_name = do
          name <- if c_name == nullPtr
                    then return ""
                    else peekCString c_name
          (cu,ss,dies,names,action) <- readIORef ref
          writeIORef ref (cu,[],Map.insert name (cu,ss) dies,names,action)

        register_scope ref c_start_line c_start_col c_end_line c_end_col = do
          (cu,ss,dies,names,action) <- readIORef ref
          let s = (fromIntegral c_start_line
                  ,fromIntegral c_start_col
                  ,fromIntegral c_end_line
                  ,fromIntegral c_end_col
                  )
          writeIORef ref (cu,add_scope s ss,dies,names,action)

        register_name ref c_name addr save_byte = do
          name <- peekCString c_name
          (cu,ss,dies,names,action) <- readIORef ref
          writeIORef ref $! (cu,ss,dies,Map.insert addr (name,save_byte) names,action)

        breakpoint_hit ref dbg addr n_args args p_save_byte = do
          (cu,ss,dies,names,action) <- readIORef ref
          case Map.lookup addr names of
            Just (name,save_byte) -> do poke p_save_byte save_byte
                                        args <- peekArray (fromIntegral n_args) args
                                        let die = Map.lookup name dies
                                        new_action <- handleEvent (wrapDebugger ref dbg) name die args
                                        writeIORef ref (cu,ss,dies,names,new_action)
                                        case (action,new_action) of
                                          (Step,        Step        ) -> return 1
                                          (Step,        Continue bs ) -> remove_breakpoints dbg name names bs
                                          (_           ,Stop        ) -> return 3
                                          (Continue bs ,Step        ) -> set_breakpoints    dbg name names bs
                                          (Continue bs1,Continue bs2)
                                             | bs1 == bs2             -> return 1
                                             | otherwise              -> set_breakpoints    dbg name names bs1 >>
                                                                         remove_breakpoints dbg name names bs2
            Nothing               -> do return 0

        add_scope s []      = [s]
        add_scope s (s':ss) =
          case cmpSpan s s' of
            Just LT -> s':ss
            Just EQ -> s :ss
            Just GT -> s :remove_scope s ss
            Nothing -> s':add_scope s ss

        remove_scope s []      = []
        remove_scope s (s':ss) =
          case cmpSpan s s' of
            Just GT -> remove_scope s ss
            _       -> s':remove_scope s ss

        set_breakpoints dbg name names bs = do
          sequence_ [debugger_poke dbg addr 0xCC | (addr, (name, save_byte)) <- Map.toList names
                                                 , not (name `elem` bs)]
          return (if name `elem` bs then 2 else 1)

        remove_breakpoints dbg name names bs = do
          sequence_ [debugger_poke dbg addr save_byte
                                                 | (addr, (name, save_byte)) <- Map.toList names
                                                 , not (name `elem` bs)]
          return (if name `elem` bs then 1 else 2)

    cmpSpan (sl1,sc1,el1,ec1) (sl2,sc2,el2,ec2) =
      case (compare (sl1,sc1) (sl2,sc2),compare (el1,ec1) (el2,ec2)) of
        (LT,GT) -> Just GT
        (EQ,GT) -> Just GT
        (LT,EQ) -> Just GT
        (EQ,EQ) -> Just EQ
        (GT,EQ) -> Just LT
        (EQ,LT) -> Just LT
        (GT,LT) -> Just LT
        _       -> Nothing

    wrapDebugger ref dbg = Debugger peekC stack sourceFiles
                                    findFunction findSource
      where
        peekC addr =
          bracket (debugger_copy_closure dbg addr)
                  (debugger_free_closure dbg) $ \pclosure -> do
            if pclosure == nullPtr
              then return Nothing
              else do (cu,ss,dies,names,action) <- readIORef ref
                      info_ptr <- (#peek StgClosure, header.info) pclosure
                      let name =
                            case Map.lookup info_ptr names of
                              Nothing       -> 's':'c':':':showHex info_ptr ""
                              Just (name,_) -> name
                      itbl <- peekItbl (pclosure `plusPtr` (- (#size StgInfoTable)))
                      clo <- peekClosure name itbl pclosure
                      return (Just (name,clo))

        stack = do
          alloca $ \poffset -> do
            poke poffset 0
            getFrames poffset
          where
            getFrames poffset = do
              frm  <- getFrame poffset
              case frm of
                Nothing          -> return []
                Just frm@(_,clo)
                  | (tipe . info) clo == STOP_FRAME
                                 -> return [frm]
                  | otherwise    -> do frms <- getFrames poffset
                                       return (frm:frms)

            getFrame poffset =
              bracket (debugger_copy_stackframe dbg poffset)
                      (debugger_free_closure dbg) $ \pclosure -> do
                if pclosure == nullPtr
                  then return Nothing
                  else do (cu,ss,dies,names,action) <- readIORef ref
                          info_ptr <- (#peek StgClosure, header.info) pclosure
                          let name =
                                case Map.lookup info_ptr names of
                                  Nothing       -> 's':'c':':':showHex info_ptr ""
                                  Just (name,_) -> name
                          itbl <- peekItbl (pclosure `plusPtr` (- (#size StgInfoTable)))
                          clo <- peekClosure name itbl pclosure
                          return (Just (name,clo))

        sourceFiles = do
          (cu,ss,dies,names,action) <- readIORef ref
          return (nubOrd [cu | (name,(cu,ss)) <- Map.toList dies])

        findFunction fpath span = do
          (cu,ss,dies,names,action) <- readIORef ref
          return (filterRoots
                    [(name,span) | (name,(cu,ss)) <- Map.toList dies
                                 , cu == fpath
                                 , span <- concatMap (match span) ss])
          where
            match s1 s2 =
              case cmpSpan s1 s2 of
                Just EQ -> [s2]
                Just GT -> [s2]
                _       -> []

            filterRoots nss = map fst (foldr add_scope [] nss)

            add_scope ns       []               = [ns]
            add_scope ns@(_,s) (ns'@(_,s'):nss) =
              case cmpSpan s s' of
                Just LT -> ns':nss
                Just EQ -> ns :nss
                Just GT -> ns :remove_scope s nss
                Nothing -> ns':add_scope ns nss

            remove_scope s []               = []
            remove_scope s (ns'@(_,s'):nss) =
              case cmpSpan s s' of
                Just GT -> remove_scope s nss
                _       -> ns':remove_scope s nss

        findSource name = do
          (cu,ss,dies,names,action) <- readIORef ref
          return (Map.lookup name dies)

    peekClosure name itbl pclosure =
      case tipe itbl of
        CONSTR        -> constrClosure 
        CONSTR_1_0    -> constrClosure
        CONSTR_0_1
          | name == "ghczmprim_GHCziTypes_Izh_con_info" -> do
                         ([],[w]) <- peekContent itbl pclosure
                         return (IntClosure PInt (fromIntegral w))
          | Set.member name nullaryConstrsSet
                      -> do clo <- constrClosure
                            return clo{dataArgs=[]}
          | otherwise -> constrClosure
        CONSTR_2_0    -> constrClosure
        CONSTR_1_1    -> constrClosure
        CONSTR_0_2    -> constrClosure
        FUN           -> funClosure FunClosure
        FUN_1_0       -> funClosure FunClosure
        FUN_0_1       -> funClosure FunClosure
        FUN_2_0       -> funClosure FunClosure
        FUN_1_1       -> funClosure FunClosure
        FUN_0_2       -> funClosure FunClosure
        THUNK         -> thunkClosure ThunkClosure
        THUNK_1_0     -> thunkClosure ThunkClosure
        THUNK_0_1     -> thunkClosure ThunkClosure
        THUNK_2_0     -> thunkClosure ThunkClosure
        THUNK_1_1     -> thunkClosure ThunkClosure
        THUNK_0_2     -> thunkClosure ThunkClosure
        THUNK_STATIC  -> thunkClosure ThunkClosure
        THUNK_SELECTOR-> selectorClosure
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
        RET_SMALL     -> retSmall
        CATCH_FRAME   -> catchFrame
{-            WEAK          -> weakClosure -}
{-            SMALL_MUT_ARR_PTRS_CLEAN -> smallMutArrPtrsClosure
        SMALL_MUT_ARR_PTRS_DIRTY -> smallMutArrPtrsClosure
        SMALL_MUT_ARR_PTRS_FROZEN_DIRTY -> smallMutArrPtrsClosure
        SMALL_MUT_ARR_PTRS_FROZEN_CLEAN -> smallMutArrPtrsClosure-}
        INVALID_OBJECT -> return (UnsupportedClosure itbl)
        _ | name == "base_GHCziInt_Izh_con_info"    -> do
                         ([],[w]) <- peekContent itbl pclosure
                         return (Int64Closure PInt (fromIntegral w))
          | name == "base_GHCziWord_Wzh_con_info"   -> do
                         ([],[w]) <- peekContent itbl pclosure
                         return (Word64Closure PWord (fromIntegral w))
          | name == "base_GHCziInt_I64zh_con_info"  -> do
                         ([],[w]) <- peekContent itbl pclosure
                         return (Int64Closure PInt64 (fromIntegral w))
          | name == "base_GHCziWord_W64zh_con_info" -> do
                         ([],[w]) <- peekContent itbl pclosure
                         return (Word64Closure PWord64 (fromIntegral w))
          | otherwise                               -> do
                         (ps,ws) <- peekContent itbl pclosure
                         return (OtherClosure itbl ps ws)
      where
        constrClosure = do
          (ps,ws) <- peekContent itbl pclosure
          let pitbl = pclosure `plusPtr` (- #size StgInfoTable)
          (pkg,modl,name) <- dataConNames pitbl
          return (ConstrClosure itbl ps ws pkg modl name)

        funClosure con = do
          (ps,ws) <- peekContent itbl pclosure
          return (con itbl ps ws)

        thunkClosure con = do
          (ps,ws) <- peekContent itbl{ptrs=ptrs itbl+1} pclosure
          return (con itbl (tail ps) ws)

        selectorClosure = do
          ([_,p],[]) <- peekContent itbl{ptrs=2} pclosure
          return (SelectorClosure itbl p)

        ptr1Closure con = do
          ([p],[]) <- peekContent itbl pclosure
          return (con itbl p)

        papClosure con = do
          arity  <- (#peek StgPAP, arity) pclosure
          n_args <- (#peek StgPAP, n_args) pclosure
          fun    <- (#peek StgPAP, fun) pclosure
          ps     <- peekArray (fromIntegral n_args)
                              (plusPtr (castPtr pclosure)
                                       (#offset StgPAP, payload))
          return (con itbl
                      (fromIntegral (arity  :: (#type StgHalfWord)))
                      (fromIntegral (n_args :: (#type StgHalfWord)))
                      (fun :: HeapPtr)
                      (ps  :: [HeapPtr]))

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
          bytes <- (#peek StgArrBytes, bytes) pclosure
          payload <- peekArray (fromIntegral bytes `div` (#size StgWord))
                               (pclosure `plusPtr` (#offset StgArrBytes, payload))
          return (ArrWordsClosure itbl bytes payload)

        retSmall = do
          let bitmap = (nptrs itbl `shiftL` 32) .|. (ptrs itbl)
          (ps,ws) <- peekBitmap (bitmap .&. bitmap_SIZE_MASK)
                                (bitmap `shiftR` bitmap_BITS_SHIFT)
                                (pclosure `plusPtr` (#size StgHeader))
          return (OtherClosure itbl ps ws)

        catchFrame = do
          ex_blocked <- (#peek StgCatchFrame, exceptions_blocked) pclosure
          handler    <- (#peek StgCatchFrame, handler) pclosure
          return (OtherClosure itbl [handler] [ex_blocked])

        mutArrPtrsClosure = do
          ptrs <- (#peek StgMutArrPtrs, ptrs) pclosure
          size <- (#peek StgMutArrPtrs, size) pclosure
          payload <- peekArray (fromIntegral ptrs)
                               (pclosure `plusPtr` (#offset StgMutArrPtrs, payload))
          return (MutArrClosure itbl ptrs size payload)

{-        smallMutArrPtrsClosure = do
          (ps,[w1,w2]) <- peekContent itbl pclosure
          return (SmallMutArrClosure itbl w1 w2 ps) -}

        peekContent itbl pclosure = do
          let pptrs  = castPtr (pclosure `plusPtr` (#size StgHeader)) :: Ptr HeapPtr
              pwords = castPtr (pptrs    `plusPtr` (fromIntegral (ptrs itbl * #size StgWord))) :: Ptr Word
          ps <- peekArray (fromIntegral (ptrs  itbl)) pptrs
          ws <- peekArray (fromIntegral (nptrs itbl)) pwords
          return (ps,ws)

        peekBitmap size bitmap ptr
          | size == 0 = return ([],[])
          | bitmap .&. 1 == 0 = do
              p <- peek (castPtr ptr)
              (ps,ws) <- peekBitmap (size-1) (bitmap `shiftR` 1) (ptr `plusPtr` (sizeOf (undefined :: HeapPtr)))
              return (p:ps,ws)
          | bitmap .&. 1 == 1 = do
              w <- peek (castPtr ptr)
              (ps,ws) <- peekBitmap (size-1) (bitmap `shiftR` 1) (ptr `plusPtr` (sizeOf (undefined :: Word)))
              return (ps,w:ws)

nullaryConstrsSet = Set.fromList
  [ "stg_NO_FINALIZER_con_info"
  , "ghczmprim_GHCziTypes_True_con_info"
  , "ghczmprim_GHCziTypes_False_con_info"
  , "ghczmprim_GHCziTypes_ZMZN_con_info"
  , "ghczmprim_GHCziTypes_LT_con_info"
  , "ghczmprim_GHCziTypes_EQ_con_info"
  , "ghczmprim_GHCziTypes_GT_con_info"
  , "ghczmprim_GHCziTuple_Z2T_con_info"
  , "base_GHCziMaybe_Nothing_con_info"
  , "base_GHCziIOziHandleziTypes_LF_con_info"
  , "base_GHCziIOziHandleziTypes_BufferListNil_con_info"
  , "base_GHCziIOziHandleziTypes_ClosedHandle"
  , "base_GHCziIOziHandleziTypes_SemiClosedHandle"
  , "base_GHCziIOziHandleziTypes_ReadHandle"
  , "base_GHCziIOziHandleziTypes_WriteHandle_con_info"
  , "base_GHCziIOziHandleziTypes_AppendHandle"
  , "base_GHCziIOziHandleziTypes_ReadWriteHandle"
  , "base_GHCziIOziEncodingziFailure_ErrorOnCodingFailure_con_info"
  ]

#include "debugger.h"

bitmap_SIZE_MASK  = 0x3f
bitmap_BITS_SHIFT = 6

data DebuggerCallbacks

foreign import ccall debugger_execv :: CString -> Ptr CString ->
                                       Ptr DebuggerCallbacks -> IO CInt

foreign import ccall debugger_copy_closure :: Ptr Debugger -> HeapPtr -> IO (Ptr ())
foreign import ccall debugger_copy_stackframe :: Ptr Debugger -> Ptr CSize -> IO (Ptr ())
foreign import ccall debugger_free_closure :: Ptr Debugger -> Ptr () -> IO ()
foreign import ccall debugger_poke :: Ptr Debugger -> (#type GElf_Addr) -> Word8 -> IO ()

type Wrapper a = a -> IO (FunPtr a)

foreign import ccall "wrapper" wrapRegisterCompUnit :: Wrapper (CString -> CString -> IO ())
foreign import ccall "wrapper" wrapRegisterSubProg :: Wrapper (CString -> IO ())
foreign import ccall "wrapper" wrapRegisterScope :: Wrapper (CInt -> CInt -> CInt -> CInt -> IO ())
foreign import ccall "wrapper" wrapRegisterName :: Wrapper (CString -> (#type GElf_Addr) -> (#type uint8_t) -> IO ())
foreign import ccall "wrapper" wrapBreakpointHit :: Wrapper (Ptr Debugger -> (#type GElf_Addr) -> CSize -> Ptr (#type StgWord) -> Ptr (#type uint8_t) -> IO CInt)
