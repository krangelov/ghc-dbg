import System.IO
import System.Environment
import Control.Monad
import GHC.Exts.Heap
import GHC.Exts.Heap.InfoTable
import HDB

main = do
  args <- getArgs
  startDebugger args $ \dbg name srcloc args -> do
    putStrLn (name++" "++show args)
    print srcloc
    case srcloc of
      Just (fpath,spans) -> do ls <- fmap lines $ readFile fpath
                               mapM_ (printSpan ls) spans
      Nothing            -> return ()
    loop dbg
    return Step

printSpan ls (sl,sc,el,ec) = do
  let ls' = case take (el-sl+1) (drop (sl-1) ls) of
              []     -> []
              [l]    -> let (ws,xs) = splitAt (sc-1) l
                            (ys,zs) = splitAt (ec-sc) xs
                        in [ws ++ "\ESC[30;47m" ++ ys ++ "\ESC[39;49m" ++ zs]
              (l:ls) -> let (ws,xs) = splitAt (sc-1) l
                            (ys,zs) = splitAt (ec-1) (last ls)
                        in [ws ++ "\ESC[30;47m" ++ xs] ++
                           init ls ++
                           [ys ++ "\ESC[39;49m" ++ zs]
  mapM_ putStrLn ls'

loop dbg = do
  hPutStr stdout ">>> "
  hFlush stdout
  s <- getLine
  case words s of
    []          -> return ()
    ["print",w] -> do
        clo <- peekClosure dbg (read w)
        putStrLn (show clo)
        loop dbg
    ["backtrace"]->do
        stk <- getStack dbg
        mapM_ print stk
        loop dbg
