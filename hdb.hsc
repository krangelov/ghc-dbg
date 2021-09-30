import Foreign
import Foreign.C
import Foreign.Ptr
import System.Environment
import Control.Exception
import Data.IORef
import qualified Data.Map as Map
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

    breakpoint_hit ref addr p_save_word = do
      breakpoints <- readIORef ref
      case Map.lookup addr breakpoints of
        Just (name,save_word,itbl) -> do poke p_save_word save_word
                                         print (name,itbl)
                                         return 1
        Nothing                    -> do return 0


#include "debugger.h"

data DebuggerCallbacks

foreign import ccall debugger_execv :: CString -> Ptr CString ->
                                       Ptr DebuggerCallbacks -> IO ()

type RegisterInfo = CString -> (#type GElf_Addr) -> (#type long) -> Ptr StgInfoTable -> IO ()

foreign import ccall "wrapper"
  wrapRegisterInfo :: RegisterInfo -> IO (FunPtr RegisterInfo)

type BreakpointHit = (#type GElf_Addr) -> Ptr (#type long) -> IO CInt

foreign import ccall "wrapper"
  wrapBreakpointHit :: BreakpointHit -> IO (FunPtr BreakpointHit)

