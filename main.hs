import Prelude hiding ((<>))
import System.IO
import System.Environment
import Control.Monad
import GHC.Exts.Heap
import GHC.Exts.Heap.InfoTable
import Numeric (showHex)
import HDB
import Text.Encoding.Z
import Text.PrettyPrint.Annotated
import Data.IORef
import Data.List
import Data.Char
import Data.Maybe
import qualified Data.Map as Map

main = do
  args <- getArgs
  opts_ref <- newIORef (False,False)
  startDebugger args $ \dbg name srcloc args -> do
    (ptrs,t) <- peekHeapState dbg name args
    opts <- readIORef opts_ref
    let doc = renderHeapTree 1 opts t $$
              vcat (map (\(ptr,t) -> renderHeapPtr ptr <+> char '=' <+> renderHeapTree 0 opts t)
                   (Map.toList ptrs))
    putStrLn (ansiRender doc)
    case srcloc of
      Just (fpath,spans) -> do ls <- fmap lines $ readFile fpath
                               mapM_ (printSpan ls) spans
      Nothing            -> return ()
    (opts,res) <- loop dbg opts
    writeIORef opts_ref opts
    return res

data HeapTree
  = HP HeapPtr                      -- ^ pointer to a shared node
  | HC String (GenClosure HeapTree) -- ^ heap closure
  | HF HeapTree [HeapTree]          -- ^ a stack frame
  | HE HeapTree                     -- ^ what is beeing executed now
  deriving Show

peekHeapState dbg name args = do
  (env,t) <- fixIO $ \res -> do
                        let out = fst res
                            env = Map.empty
                        (env,t:args) <- mapAccumM (peekHeapTree out) env args
                        stk <- getStack dbg
                        case stk of
                          ((name',clo):stk) | name==name' -> do (env,clo) <- down out env clo
                                                                appStack out env stk (HE (HF (HC name clo) [HF t args]))
                          _                               -> appStack out env stk (HE (HF t args))
  let ptrs = fmap snd (Map.filter (\(c,_) -> c > 1) env)
  return (ptrs,t)
  where
    peekHeapTree out env ptr =
      case Map.lookup ptr env of
        Just (c,t) -> return (Map.insert ptr (c+1,t) env, HP ptr)
        Nothing    -> do mb_clo <- peekClosure dbg ptr
                         case mb_clo of
                           Nothing         -> return (env, HP ptr)
                           Just (name,clo) -> do let env1 = Map.insert ptr (1,HP ptr) env
                                                 (env2,clo) <- down out env1 clo
                                                 let env3 = Map.adjust (\(c,_) -> (c,HC name clo)) ptr env2
                                                     res  = case Map.lookup ptr out of
                                                              Just (1,t) -> t
                                                              _          -> HP ptr
                                                 return (env3,res)

    appStack out env []               t = return (env,t)
    appStack out env ((name,clo):stk) t = do
      (env,clo) <- down out env clo
      appStack out env stk (HF (HC name clo) [t])

    down out env clo@(IntClosure info v) = return (env, IntClosure info v)
    down out env clo@(Int64Closure info v) = return (env, Int64Closure info v)
    down out env clo@(WordClosure info v) = return (env, WordClosure info v)
    down out env clo@(Word64Closure info v) = return (env, Word64Closure info v)
    down out env clo@(DoubleClosure info v) = return (env, DoubleClosure info v)
    down out env clo
      | elem typ [CONSTR,     CONSTR_0_1, CONSTR_0_2,
                  CONSTR_1_1, CONSTR_2_0, CONSTR_1_0,
                  FUN,        FUN_0_1,    FUN_0_2,
                  FUN_1_1,    FUN_2_0,    FUN_1_0,
                  THUNK,      THUNK_0_1,  THUNK_0_2,
                  THUNK_1_1,  THUNK_2_0,  THUNK_1_0,
                  THUNK_STATIC] =
          do (env2,args) <- mapAccumM (peekHeapTree out) env (ptrArgs clo)
             return (env2, clo{ptrArgs=args})
      | elem typ [AP, PAP] =
          do (env2,fun) <- peekHeapTree out env (fun clo)
             (env3,pld) <- mapAccumM (peekHeapTree out) env2 (payload clo)
             return (env3, clo{fun=fun, payload=pld})
      | elem typ [IND, IND_STATIC, BLACKHOLE] =
          do (env2,ind) <- peekHeapTree out env (indirectee clo)
             return (env2, clo{indirectee=ind})
      | elem typ [MVAR_CLEAN, MVAR_DIRTY] =
          do (env2,val) <- peekHeapTree out env (value clo)
             return (env2, clo{queueHead=HP (queueHead clo)
                              ,queueTail=HP (queueTail clo)
                              ,value=val
                              })
      | elem typ [MUT_VAR_CLEAN, MUT_VAR_DIRTY] =
          do (env2,val) <- peekHeapTree out env (var clo)
             return (env2, clo{var=val})
      | elem typ [ARR_WORDS] =
          do return (env, clo{arrWords=arrWords clo})
      | elem typ [MUT_ARR_PTRS_CLEAN, MUT_ARR_PTRS_DIRTY,
                  MUT_ARR_PTRS_FROZEN_CLEAN, MUT_ARR_PTRS_FROZEN_DIRTY]=
          do (env2,elems) <- mapAccumM (peekHeapTree out) env (mccPayload clo)
             return (env2, clo{mccPayload=elems})
      | typ == INVALID_OBJECT =
          do return (env, UnsupportedClosure (info clo))
      | otherwise =
          do (env2,args) <- mapAccumM (peekHeapTree out) env (hvalues clo)
             return (env2, clo{hvalues=args})
      where
        typ  = tipe (info clo)

mapAccumM :: Monad m => (a -> b -> m (a, c)) -> a -> [b] -> m (a, [c])
mapAccumM _ s []       = return (s, [])
mapAccumM f s (x : xs) = f s x >>= (\(s', x') -> mapAccumM f s' xs >>=
                                     (\(s'', xs') -> return (s'', x' : xs')))

ansiRender d =
  case spans of
    [Span start len _] -> let (s1,s') = splitAt start s
                              (s2,s3) = splitAt len s'
                          in s1 ++ "\ESC[32;40m" ++ s2 ++ "\ESC[39;49m" ++ s3
    _                  -> s
  where
    (s,spans) = renderSpans d

renderHeapTree d opts (HP ptr) = renderHeapPtr ptr
renderHeapTree d opts (HC name (IntClosure _ v)) = int v
renderHeapTree d opts (HC name (Int64Closure _ v)) = integer (fromIntegral v)
renderHeapTree d opts (HC name (WordClosure _ v)) = integer (fromIntegral v)
renderHeapTree d opts (HC name (Word64Closure _ v)) = integer (fromIntegral v)
renderHeapTree d opts (HC name (DoubleClosure _ v)) = double v
renderHeapTree d opts (HC name clo) =
  case tipe (info clo) of
    CONSTR        -> renderData name clo
    CONSTR_0_1
      | name == "base_GHCziInt_I32zh_con_info"
                  -> hsep (map (integer . fromIntegral) (dataArgs clo))
      | name == "ghczmprim_GHCziTypes_Czh_con_info"
                  -> hsep (map (text . show . chr . fromIntegral) (dataArgs clo))
      | otherwise -> renderData name clo
    CONSTR_0_2    -> renderData name clo
    CONSTR_1_1    -> renderData name clo
    CONSTR_2_0
      | name == "ghczmprim_GHCziTuple_Z2T_con_info"
                  -> let pargs = map (renderHeapTree 0 opts) (ptrArgs clo)
                     in parens (sep (punctuate comma pargs))
      | otherwise -> renderData name clo
    CONSTR_1_0    -> renderData name clo
    CONSTR_NOCAF  -> renderOther name clo
    FUN           -> renderData name clo
    FUN_1_0       -> renderData name clo
    FUN_0_1       -> renderData name clo
    FUN_2_0       -> renderData name clo
    FUN_1_1       -> renderData name clo
    FUN_0_2       -> renderData name clo
    FUN_STATIC    -> text (showName opts name)
    THUNK         -> renderData name clo
    THUNK_1_0     -> renderData name clo
    THUNK_0_1     -> renderData name clo
    THUNK_2_0     -> renderData name clo
    THUNK_1_1     -> renderData name clo
    THUNK_0_2     -> renderData name clo
    THUNK_STATIC  -> text (showName opts name)
    AP            -> let s  = renderHeapTree 1 opts (fun clo)
                         ss = map (renderHeapTree 1 opts) (payload clo)
                     in apply' d s ss
    PAP           -> let s  = renderHeapTree 1 opts (fun clo)
                         ss = map (renderHeapTree 1 opts) (payload clo)
                     in apply' d s ss
    IND           -> renderHeapTree d opts (indirectee clo)
    IND_STATIC    -> renderHeapTree d opts (indirectee clo)
    BLACKHOLE     -> renderHeapTree d opts (indirectee clo)
    MVAR_CLEAN    -> renderMVar clo
    MVAR_DIRTY    -> renderMVar clo
    MUT_VAR_CLEAN -> renderMutVar clo
    MUT_VAR_DIRTY -> renderMutVar clo
    ARR_WORDS     -> text "<ARR_WORDS" <+> sep (map (integer . fromIntegral) (arrWords clo)) <> char '>'
    MUT_ARR_PTRS_CLEAN -> renderMutArray clo
    MUT_ARR_PTRS_DIRTY -> renderMutArray clo
    MUT_ARR_PTRS_FROZEN_CLEAN -> renderMutArray clo
    MUT_ARR_PTRS_FROZEN_DIRTY -> renderMutArray clo
    UPDATE_FRAME  -> let pargs = map (renderHeapTree 1 opts) (hvalues clo)
                     in (text "<Update" <+> sep pargs <> char '>')
    CATCH_FRAME   -> let pargs = map (renderHeapTree 1 opts) (hvalues clo)
                     in (text "<Catch" <+> sep (map (integer . fromIntegral) (rawWords clo)++pargs) <> char '>')
    STOP_FRAME    -> renderOther name clo
    WEAK          -> let key:value:_ = rawWords clo
                         pargs = map (renderHeapTree 1 opts) (hvalues clo)
                     in apply d "Weak#" (pargs++[renderHeapPtr key,renderHeapPtr value])
    RET_SMALL     -> renderOther name clo
    TSO           -> text "<TSO>"
  where
    renderData name clo =
       let pargs = map (renderHeapTree 1 opts) (ptrArgs clo)
           dargs = map (integer . fromIntegral) (dataArgs clo)
       in apply d (showName opts name) (pargs ++ dargs)

    renderOther name clo =
       let pargs = map (renderHeapTree 1 opts) (hvalues clo)
           dargs = map (integer . fromIntegral) (rawWords clo)
       in apply d (showName opts name) (pargs ++ dargs)

    renderMVar clo =
      let s = renderHeapTree 1 opts (value clo)
      in text "<MVAR" <+> s <> char '>'

    renderMutVar clo =
      let s = renderHeapTree 1 opts (var clo)
      in text "<MUT_VAR" <+> s <> char '>'

    renderMutArray clo =
      let elems = map (renderHeapTree 1 opts) (mccPayload clo)
      in text "<MUT_ARR" <+> sep elems <> char '>'
renderHeapTree d opts (HF t ts) =
  apply' d (renderHeapTree 1 opts t) (map (renderHeapTree 1 opts) ts)
renderHeapTree d opts (HE t) =
  annotate () (renderHeapTree 1 opts t)


renderHeapPtr ptr = char '#' <> text (showHex ptr "")

showName (show_pkg,show_mod) name
  | name == "ZCMain_main_info" = ":Main_main_info"
  | take 3 name == "sc:"       = name
  | take 4 name == "stg_"      = reverse (drop 5 rname)
  | otherwise                  = reconstruct (reverse rname)
  where
    rname = reverse name

    reconstruct s
      | s1 == "info"   = x1
      | s2 == "info"   = (if show_mod
                            then zDecodeString x1++"."
                            else "")++
                         (zDecodeString x2)
      | otherwise      = (if show_pkg
                            then zDecodeString x1++":"
                            else "")++
                         (if show_mod
                            then zDecodeString x2++"."
                            else "")++
                         (zDecodeString x3)
      where
        (x1,'_':s1) = break (=='_') s
        (x2,'_':s2) = break (=='_') s1
        (x3,_     ) = break (=='_') s2

apply :: Int -> String -> [Doc a] -> Doc a
apply d s [] = text s
apply d s ss
  | d > 0     = parens s2
  | otherwise = s2
  where
    s2 =
      case ss of
        [s1,s2] | isOperator s -> s1 <+> text s <+> s2
        _                      -> text s <+> sep ss

    isOperator s = not (any (flip elem chars) s)
      where
        chars = ['a'..'z']++['A'..'Z']++['0'..'9']++['_']

apply' :: Int -> Doc a -> [Doc a] -> Doc a
apply' d s [] = s
apply' d s ss
  | d > 0     = parens (s <+> sep ss)
  | otherwise = (s <+> sep ss)

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

loop dbg opts = do
  hPutStr stdout ">>> "
  hFlush stdout
  s <- getLine
  case words s of
    []              -> return (opts,Step)
    ["step"]        -> return (opts,Step)
    ["stop"]        -> return (opts,Stop)
    ("continue":ws) -> return (opts,Continue ws)
    ["print",w]     -> do
        clo <- peekClosure dbg (read w)
        putStrLn (show clo)
        loop dbg opts
    _ -> do putStrLn "Unknown command"
            loop dbg opts
