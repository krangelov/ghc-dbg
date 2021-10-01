import System.Environment
import HDB

main = do
  args <- getArgs
  startDebugger args $ \name closure -> do 
    print (name,closure)
