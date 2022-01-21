import System.Environment
import Control.Monad
import GHC.Exts.Heap
import GHC.Exts.Heap.InfoTable
import HDB

main = do
  args <- getArgs
  startDebugger args $ \dbg name srcloc closure -> do
    putStrLn (name++":  "++show closure)
    case srcloc of
      Just (fpath,spans) -> putStrLn (fpath++"  "++show spans)
      Nothing            -> return ()
    case closure of
      ConstrClosure{}
          -> forM_ (ptrArgs closure) $ \arg -> do
                clo <- peekClosure dbg arg
                putStrLn (">>> "++show clo)
      _   -> return ()
       
