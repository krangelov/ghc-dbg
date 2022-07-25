{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

import Prelude hiding ((<>))
import System.IO
import System.Environment
import Control.Monad
import Control.Monad.IO.Class
import GHC.Exts.Heap
import GHC.Exts.Heap.InfoTable
import GHC.Debugger
import Numeric (showHex)
import Text.Encoding.Z
import Text.PrettyPrint.Annotated.HughesPJ hiding (render)
import Data.IORef
import Data.List
import Data.Char
import Data.Maybe
import qualified Data.Map as Map
import UI.NCurses
import Foreign.C

main = do
  args <- getArgs
  opts_ref <- newIORef (Options False False [])
  startDebugger args $ \dbg name srcloc args -> do
    (ptrs,t) <- peekHeapState dbg name args
    opts <- readIORef opts_ref
    let doc = ppHeapTree 1 opts t $$
              vcat (map (\(ptr,t) -> ppHeapPtr ptr <+> char '=' <+> ppHeapTree 0 opts t)
                        (Map.toList ptrs))
    (opts,res) <- runCurses $ do
          setEcho False
          setCursorMode CursorInvisible
          clrs <- newColors
          w <- defaultWindow
          (rows,cols) <- updateWindow w $ do
             (rows,cols) <- windowSize
             moveCursor (rows-2) 0
             clearLine
             drawString mainMenu
             clearLine
             return (rows,cols)
          w1 <- newHeapPad doc clrs
                           0 0 (rows-2) (cols `div` 2)
          doc <- case srcloc of
              Just (fpath,spans)
                      -> do text <- liftIO (readFile fpath)
                            let curs = [(sr,sc,er,ec) | (sr,sc,er,ec) <- spans]
                                brks = [span | (fpath',span) <- optBreakpoints opts, fpath==fpath']
                            return (fpath,text,curs,brks)
              _       -> return ("","",[],[])
          w2 <- newSourcePad doc clrs ViewMode
                             0 (cols `div` 2) (rows-2) (cols `div` 2)
          render
          (opts,w1,w2,res) <- loop dbg clrs w w1 w2 0 opts
          closeHeapPad   w1
          closeSourcePad w2
          return (opts,res)

    writeIORef opts_ref opts
    return res

data Colors
  = Colors
      { clrCurrent    :: ColorID
      , clrSelected   :: ColorID
      , clrBreakpoint :: ColorID
      , clrDefault    :: ColorID
      }

data Options
  = Options
      { optShowPackage :: Bool
      , optShowModule  :: Bool
      , optBreakpoints :: [(FilePath,SourceSpan)]
      }

newColors = do
  cc <- newColorID ColorGreen   ColorDefault 1
  cs <- newColorID ColorBlack   ColorWhite   2
  cb <- newColorID ColorRed     ColorDefault 3
  cd <- newColorID ColorDefault ColorDefault 4
  return (Colors cc cs cb cd)

mainMenu = "Commands: (s)tep, (c)ontinue, show (o)utput, (l)oad source,\n          set (b)reakpoint, (Tab)-switch windows, (q)uit"
breakpointMenu = "Mark a region\n(Enter)-set breakpoint, (Esc)-cancel, (Del)-delete existing breakpoint"
fileMenu = "(Enter)-select file, (BackSpc)-remove last character, (Esc)-cancel"

class EventHandler a b | a -> b where
  handleEvent :: Colors -> Event -> a -> Curses (a,b)

data HeapPad
  = HeapPad
      { heapPad    :: Pad
      , heapPadDoc :: (String, Span HeapTreeAnn
                             ,[Span HeapTreeAnn]
                             ,[Span HeapTreeAnn]
                      )
      , heapPadRow :: Integer
      , heapPadCol :: Integer
      , heapPadTextRows :: Integer
      , heapPadTextCols :: Integer
      , heapPadTextX :: Integer
      , heapPadTextY :: Integer
      , heapPadRows :: Integer
      , heapPadCols :: Integer
      }

newHeapPad doc clrs y x rows cols = do
  p <- newPad (max text_rows rows) (max text_cols cols)
  updatePad p row col y x (y+rows-1) (x+cols-1) $ do
    drawString s1
    setColor (clrCurrent clrs)
    drawString s2
    setColor (clrDefault clrs)
    drawString s3
  return (HeapPad p (text,sel,[],links) row col text_rows text_cols y x rows cols)
  where
    (text,spans) = renderSpans doc

    ([sel@(Span start len _)],links) =
       partition (\span -> spanAnnotation span == Current) spans 

    (s1,rest) = splitAt start text
    (s2,s3)   = splitAt len   rest

    ls1 = lines s1
    row | null ls1              = 0
        | row' < 0              = 0
        | row'+rows > text_rows = max 0 (text_rows-rows)
        | otherwise             = row'
        where row' = fromIntegral (length ls1-1)
    col | null ls1              = 0
        | col' < 0              = 0
        | col'+cols > text_cols = max 0 (text_cols-cols)
        | otherwise             = col'
        where col' = fromIntegral (length (last ls1))

    ls        = lines text
    text_rows = fromIntegral (length ls)
    text_cols = fromIntegral (maximum (0:map length ls)+1)

closeHeapPad hp = closePad (heapPad hp)

data HeapPadResult
  = NoHeapResult
  | SelectFunction LinkerName

instance EventHandler HeapPad HeapPadResult where
  handleEvent clrs ev hp
      | ev == EventSpecialKey KeyLeftArrow
                                 = moveLeft  hp
      | ev == EventSpecialKey KeyRightArrow
                                 = moveRight hp
      | ev == EventSpecialKey KeyUpArrow
                                 = scrollPad (-1) 0 hp
      | ev == EventSpecialKey KeyDownArrow
                                 = scrollPad 1 0 hp
      | ev == EventSpecialKey KeyHome
                                 = scrollPad 0 (-heapPadCol hp) hp
      | ev == EventSpecialKey KeyEnd
                                 = scrollPad 0 (heapPadTextCols hp-heapPadCol hp) hp
      | ev == EventSpecialKey KeyDownArrow
                                 = scrollPad 1 0 hp
      | ev == EventSpecialKey KeyNextPage
                                 = scrollPad (heapPadRows hp) 0 hp
      | ev == EventSpecialKey KeyPreviousPage
                                 = scrollPad (-heapPadRows hp) 0 hp
      | otherwise                = return (hp,NoHeapResult)
    where
      moveLeft  hp =
        case heapPadDoc hp of
          (text,cur,[],right)        -> return (hp,NoHeapResult)
          (text,cur,[span],right)    -> return (hp,NoHeapResult)
          (text,cur,span:left,right) -> do let hp' = adjustScroll (hp{heapPadDoc=(text,cur,left,span:right)})
                                               FunName fun = spanAnnotation (head left)
                                           updateHeapPad clrs hp'
                                           render
                                           return (hp',SelectFunction fun)

      moveRight hp =
        case heapPadDoc hp of
          (text,cur,left,[])         -> return (hp,NoHeapResult)
          (text,cur,left,span:right) -> do let hp' = adjustScroll (hp{heapPadDoc=(text,cur,span:left,right)})
                                               FunName fun = spanAnnotation span
                                           updateHeapPad clrs hp'
                                           render
                                           return (hp',SelectFunction fun)

      adjustScroll hp =
        case heapPadDoc hp of
          (text,cur,sel:left,right) -> let ls  = lines (take (spanStart sel) text)
                                           row = fromIntegral (length ls - 1)
                                           col = fromIntegral (length (last ls))
                                           len = fromIntegral (spanLength sel)
                                       in if null ls
                                            then hp
                                            else hp{heapPadRow=if row >= heapPadRow hp && row < heapPadRow hp+heapPadRows hp
                                                                 then heapPadRow hp
                                                                 else min row (heapPadTextRows hp - heapPadRows hp)
                                                   ,heapPadCol=if col >= heapPadCol hp && col+len < heapPadCol hp+heapPadCols hp
                                                                 then heapPadCol hp
                                                                 else min col (heapPadTextCols hp - heapPadCols hp)
                                                   }
          _                         -> hp

      scrollPad dr dc (HeapPad p doc row col text_rows text_cols y x rows cols) = do
        updatePad p new_row new_col y x (y+rows-1) (x+cols-1) $
          return ()
        render
        return (HeapPad p doc new_row new_col text_rows text_cols y x rows cols,NoHeapResult)
        where
          new_row | row' < 0              = 0
                  | row'+rows > text_rows = max 0 (text_rows-rows)
                  | otherwise             = row'
                  where row'=row+dr
          new_col | col' < 0 = 0
                  | col'+cols > text_cols = max 0 (text_cols-cols)
                  | otherwise             = col'
                  where col' = col+dc

updateHeapPad clrs (HeapPad p (text,cur,[],right) row col text_rows text_cols y x rows cols) =
  updatePad p row col y x (y+rows-1) (x+cols-1) $ do
    moveCursor 0 0 >> clear
    let (s1,sm) = splitAt (spanStart  cur) text
        (s2,s3) = splitAt (spanLength cur) sm
    setColor (clrDefault clrs) >> drawString s1
    setColor (clrCurrent clrs) >> drawString s2
    setColor (clrDefault clrs) >> drawString s3
updateHeapPad clrs (HeapPad p (text,cur,sel:left,right) row col text_rows text_cols y x rows cols)
  | spanStart sel < spanStart cur = do
      updatePad p row col y x (y+rows-1) (x+cols-1) $ do
        moveCursor 0 0 >> clear
        let (s1,sm) = splitAt (spanStart  sel) text
            (s2,sn) = splitAt (spanLength sel) sm
            (s3,sp) = splitAt (spanStart cur-spanStart sel-spanLength sel) sn
            (s4,s5) = splitAt (spanLength cur) sp
        setColor (clrDefault  clrs) >> drawString s1
        setColor (clrSelected clrs) >> drawString s2
        setColor (clrDefault  clrs) >> drawString s3
        setColor (clrCurrent  clrs) >> drawString s4
        setColor (clrDefault  clrs) >> drawString s5
  | spanStart sel >= spanStart cur+spanLength cur = do
      updatePad p row col y x (y+rows-1) (x+cols-1) $ do
        moveCursor 0 0 >> clear
        let (s1,sm) = splitAt (spanStart  cur) text
            (s2,sn) = splitAt (spanLength cur) sm
            (s3,sp) = splitAt (spanStart sel-spanStart cur-spanLength cur) sn
            (s4,s5) = splitAt (spanLength sel) sp
        setColor (clrDefault  clrs) >> drawString s1
        setColor (clrCurrent  clrs) >> drawString s2
        setColor (clrDefault  clrs) >> drawString s3
        setColor (clrSelected clrs) >> drawString s4
        setColor (clrDefault  clrs) >> drawString s5
  | otherwise = do
      updatePad p row col y x (y+rows-1) (x+cols-1) $ do
        moveCursor 0 0 >> clear
        let (s1,sm) = splitAt (spanStart  cur) text
            (s2,sn) = splitAt (spanStart sel-spanStart  cur) sm
            (s3,sp) = splitAt (spanLength sel) sn
            (s4,s5) = splitAt (spanStart cur+spanLength cur-spanStart sel-spanLength sel) sp
        setColor (clrDefault  clrs) >> drawString s1
        setColor (clrCurrent  clrs) >> drawString s2
        setColor (clrSelected clrs) >> drawString s3
        setColor (clrCurrent  clrs) >> drawString s4
        setColor (clrDefault  clrs) >> drawString s5

data SourcePadMode
  = ViewMode
  | SelectMode Integer Integer
  | HighlightMode

data SourcePad
  = SourcePad
      { sourcePad :: Pad
      , sourcePadDoc :: (FilePath,String,[SourceSpan],[SourceSpan])
      , sourcePadRow :: Integer
      , sourcePadCol :: Integer
      , sourcePadMode :: SourcePadMode
      , sourcePadViewRow :: Integer
      , sourcePadViewCol :: Integer
      , sourcePadTextRows :: Integer
      , sourcePadTextCols :: Integer
      , sourcePadTextX :: Integer
      , sourcePadTextY :: Integer
      , sourcePadRows :: Integer
      , sourcePadCols :: Integer
      }

newSourcePad doc@(_,text,curs,_) clrs mode y x rows cols = do
  p <- newPad (max text_rows rows) (max text_cols cols)
  let sp = SourcePad p doc row col mode row col text_rows text_cols y x rows cols
  updateSourcePad clrs sp
  return sp
  where
    ls        = lines text
    text_rows = fromIntegral (length ls+1)
    text_cols = fromIntegral (maximum (0:map length ls)+1)

    ((scr,scc,ecl,ecc) : _) = curs

    row | null curs                         = 0
        | fromIntegral scr+rows > text_rows = max 0 (text_rows-rows)
        | otherwise                         = fromIntegral scr
    col | null curs                         = 0
        | fromIntegral scc+cols > text_cols = max 0 (text_cols-cols)
        | otherwise                         = fromIntegral scc

closeSourcePad hp = closePad (sourcePad hp)

updateSourcePad clrs (SourcePad p doc@(_,text,curs,brks) row col mode vrow vcol text_rows text_cols y x rows cols) =
  updatePad p vrow vcol y x (y+rows-1) (x+cols-1) $ do
    moveCursor 0 0
    setColor (clrDefault    clrs) >> drawString text
    setColor (clrBreakpoint clrs) >> mapM_ (drawSpan ls) brks
    setColor (clrCurrent    clrs) >> mapM_ (drawSpan ls) curs
    setColor (clrSelected   clrs) >> mapM_ (drawSpan ls) sels
    moveCursor row col
  where
    drawSpan ls (srow,scol,erow,ecol) = do
      moveCursor (fromIntegral (srow-1)) (fromIntegral (scol-1))
      let fragment =
            case splitAt (erow-srow) (drop (srow-1) ls) of
              (s_l:ls',e_l:_) -> unlines (drop (scol-1) s_l : ls') ++ take (ecol-1) e_l
              ([]     ,  l:_) -> take (ecol-scol) (drop (scol-1) l)
              ([]     ,[]   ) -> ""
      drawString fragment

    ls   = lines text
    sels = case mode of
             ViewMode             -> []
             HighlightMode        -> curs
             SelectMode srow scol ->
               let [(sr,sc),(er,ec)] =
                        sort [(fromIntegral srow,fromIntegral scol)
                             ,(fromIntegral row,fromIntegral col)
                             ]
               in [(sr+1,sc+1,er+1,ec+1)]

data SourcePadResult
  = NoSourceResult
  | SetBreakpoint FilePath SourceSpan
  | CancelBreakpoint
  | DeleteBreakpoint FilePath Int Int

instance EventHandler SourcePad SourcePadResult where
  handleEvent clrs ev sp
      | ev == EventSpecialKey KeyLeftArrow
                                 = scrollPad 0 (-1) sp
      | ev == EventSpecialKey KeyRightArrow
                                 = scrollPad 0 1 sp
      | ev == EventSpecialKey KeyHome
                                 = scrollPad 0 (-sourcePadCol sp) sp
      | ev == EventSpecialKey KeyEnd
                                 = scrollPad 0 (sourcePadTextCols sp-sourcePadCol sp) sp
      | ev == EventSpecialKey KeyUpArrow
                                 = scrollPad (-1) 0 sp
      | ev == EventSpecialKey KeyDownArrow
                                 = scrollPad 1 0 sp
      | ev == EventSpecialKey KeyNextPage
                                 = scrollPad (sourcePadRows sp) 0 sp
      | ev == EventSpecialKey KeyPreviousPage
                                 = scrollPad (-sourcePadRows sp) 0 sp
      | ev == EventCharacter 'b' = startBreakPoint sp
      | ev == EventCharacter '\ESC'=cancelBreakPoint sp
      | ev == EventCharacter '\n'= setBreakPoint sp
      | ev == EventSpecialKey KeyDeleteCharacter
                                 = deleteBreakpoint
      | ev == EventCharacter '\t'= setupCursor sp
      | otherwise                = return (sp,NoSourceResult)
    where
      scrollPad dr dc (SourcePad p doc row col spos vrow vcol text_rows text_cols y x rows cols) = do
        let sp = SourcePad p doc new_row new_col spos new_vrow new_vcol text_rows text_cols y x rows cols
        updateSourcePad clrs sp
        render
        return (sp,NoSourceResult)
        where
          new_row | row' < 0          = 0
                  | row' >= text_rows = text_rows-1
                  | otherwise         = row'
                  where row'=row+dr
          new_col | col' < 0          = 0
                  | col' >= text_cols = text_cols-1
                  | otherwise         = col'
                  where col' = col+dc
          new_vrow | new_row <  vrow      = new_row
                   | new_row >= vrow+rows = new_row-rows+1
                   | otherwise            = vrow
          new_vcol | new_col <  vcol      = new_col
                   | new_col >= vcol+cols = new_col-cols+1
                   | otherwise            = vcol

      startBreakPoint sp = do
        let sp' = sp{sourcePadMode=SelectMode (sourcePadRow sp) (sourcePadCol sp)}
        updateSourcePad clrs sp'
        render
        return (sp',NoSourceResult)

      cancelBreakPoint sp = do
        let sp' = sp{sourcePadMode=ViewMode}
        updateSourcePad clrs sp'
        render
        return (sp',CancelBreakpoint)

      deleteBreakpoint =
        case sourcePadMode sp of
          SelectMode _ _ -> do
            let (fpath,text,curs,brks) = sourcePadDoc sp
                row   = fromIntegral (sourcePadRow sp)+1
                col   = fromIntegral (sourcePadCol sp)+1
                brks' = filter (not . matchSourceSpan row col) brks
                sp'   = sp{sourcePadDoc =(fpath,text,curs,brks')
                          ,sourcePadMode=ViewMode
                          }
            updateSourcePad clrs sp'
            render
            return (sp',DeleteBreakpoint fpath row col)
          _ -> return (sp,NoSourceResult)

      setupCursor (SourcePad p doc row col spos vrow vcol text_rows text_cols y x rows cols) = do
        updatePad p vrow vcol y x (y+rows-1) (x+cols-1) $ do
          moveCursor row col
        render
        return (sp,NoSourceResult)

      setBreakPoint sp =
        case sourcePadMode sp of
          SelectMode srow scol -> do
            let row = sourcePadRow sp
                col = sourcePadCol sp
                [(sr,sc),(er,ec)] =
                     sort [(fromIntegral srow,fromIntegral scol)
                          ,(fromIntegral row,fromIntegral col)
                          ]
                span = (sr+1,sc+1,er+1,ec+1)
                (fpath,text,curs,brks) = sourcePadDoc sp
                sp' = sp{ sourcePadDoc  = (fpath,text,curs,span:brks)
                        , sourcePadMode = ViewMode
                        }
            updateSourcePad clrs sp'
            render
            return (sp',SetBreakpoint fpath span)
          _                    -> return (sp,NoSourceResult)

matchSourceSpan row col (srow,scol,erow,ecol)
  | row <  srow                = False
  | row == srow && col <  scol = False
  | row == erow && col >= ecol = False
  | row >  erow                = False
  | otherwise                  = True


loop :: Debugger
     -> Colors
     -> Window
     -> HeapPad
     -> SourcePad
     -> Int
     -> Options
     -> Curses (Options, HeapPad, SourcePad, DebuggerAction)
loop dbg clrs w w1 w2 focus opts = do
  ev <- getEvent w Nothing
  case ev of
    Just ev
      | ev == EventCharacter 's' -> return (opts,w1,w2,Step)
      | ev == EventCharacter 'c' -> do bpts <- breakpointNames (optBreakpoints opts)
                                       return (opts,w1,w2,Continue bpts)
      | ev == EventCharacter 'q' -> return (opts,w1,w2,Stop)
      | ev == EventCharacter 'o' -> do liftIO endwin
                                       liftIO $ do
                                         b <- hGetBuffering stdin
                                         hSetBuffering stdin NoBuffering
                                         hSetEcho stdin False
                                         getChar
                                         hSetEcho stdin True
                                         hSetBuffering stdin b
                                       render
                                       loop dbg clrs w w1 w2 focus opts
      | ev == EventCharacter '\t'-> do setCursorMode (if focus == 0 then CursorVisible else CursorInvisible)
                                       if focus == 0
                                         then handleEvent clrs ev w2 >> return ()
                                         else handleEvent clrs ev w1 >> return ()
                                       loop dbg clrs w w1 w2 (1-focus) opts
      | ev == EventCharacter 'l' -> do fpaths <- liftIO (getSourceFiles dbg)
                                       setCursorMode CursorVisible
                                       mb_path <- selectFilePath clrs w fpaths
                                       case mb_path of
                                         Nothing    -> do setCursorMode (if focus == 0 then CursorInvisible else CursorVisible)
                                                          loop dbg clrs w w1 w2 focus opts
                                         Just fpath -> do closeSourcePad w2
                                                          text <- liftIO (readFile fpath)
                                                          (rows,cols) <- updateWindow w $ windowSize
                                                          let brks = [span | (fpath',span) <- optBreakpoints opts, fpath==fpath']
                                                          w2 <- newSourcePad (fpath,text,[],brks) clrs ViewMode
                                                                0 (cols `div` 2) (rows-2) (cols `div` 2)
                                                          render
                                                          loop dbg clrs w w1 w2 1 opts
      | ev == EventCharacter 'b' -> do updateWindow w $ do
                                         (rows,cols) <- windowSize
                                         moveCursor (rows-2) 0
                                         clearLine
                                         drawString breakpointMenu
                                         clearLine
                                       render
                                       setCursorMode CursorVisible
                                       (w2,_) <- handleEvent clrs ev w2
                                       loop dbg clrs w w1 w2 1 opts
      | focus == 0               -> do (w1,res) <- handleEvent clrs ev w1
                                       case res of
                                         NoHeapResult       -> do loop dbg clrs w w1 w2 focus opts
                                         SelectFunction fun -> do mb_span <- liftIO (findSource dbg fun)
                                                                  (rows,cols) <- updateWindow w $ windowSize
                                                                  closeSourcePad w2
                                                                  w2 <- case mb_span of
                                                                          Nothing            -> do newSourcePad ("","",[],[]) clrs ViewMode
                                                                                                                0 (cols `div` 2) (rows-2) (cols `div` 2)
                                                                          Just (fpath,spans) -> do text <- liftIO (readFile fpath)
                                                                                                   let brks = [span | (fpath',span) <- optBreakpoints opts, fpath==fpath']
                                                                                                   newSourcePad (fpath,text,spans,brks) clrs HighlightMode
                                                                                                                0 (cols `div` 2) (rows-2) (cols `div` 2)
                                                                  render
                                                                  loop dbg clrs w w1 w2 focus opts
      | focus == 1               -> do (w2,res) <- handleEvent clrs ev w2
                                       case res of
                                         NoSourceResult           -> do loop dbg clrs w w1 w2 focus opts
                                         SetBreakpoint fpath span -> do restoreMainMenu
                                                                        loop dbg clrs w w1 w2 0 (addBreakpoint fpath span opts)
                                         CancelBreakpoint         -> do restoreMainMenu
                                                                        loop dbg clrs w w1 w2 0 opts
                                         DeleteBreakpoint fpath row col
                                                                  -> do restoreMainMenu
                                                                        loop dbg clrs w w1 w2 0 (delBreakpoint fpath row col opts)
      | otherwise                -> loop dbg clrs w w1 w2 focus opts
  where
    restoreMainMenu = do
      setCursorMode CursorInvisible
      updateWindow w $ do
        (rows,cols) <- windowSize
        moveCursor (rows-2) 0
        clearLine
        drawString mainMenu
        clearLine
      render

    addBreakpoint fpath span opts =
      opts{optBreakpoints=(fpath,span):optBreakpoints opts}

    delBreakpoint fpath row col opts =
      opts{optBreakpoints=filter (not . match) (optBreakpoints opts)}
      where
        match (fpath',span) =
          fpath == fpath' && matchSourceSpan row col span

    breakpointNames bpts =
      liftIO (fmap (nub . concat)
                   (mapM (uncurry (findFunction dbg)) bpts))


selectFilePath clrs w fpaths = interact "" Nothing
  where
    interact cs mb_best = do
      updateWindow w $ do
        (rows,cols) <- windowSize
        moveCursor (rows-1) 0
        drawString fileMenu
        clearLine
        moveCursor (rows-2) 0
        let prompt = "file name: "
        drawString prompt
        case mb_best of
          Nothing            -> do clearLine
          Just (fpath,i,len) -> do let (s1,sm) = splitAt i   fpath
                                       (s2,s3) = splitAt len sm
                                   drawString s1
                                   setColor (clrCurrent clrs)
                                   drawString s2
                                   setColor (clrDefault clrs)
                                   drawString s3
                                   clearLine
                                   moveCursor (rows-2) (fromIntegral (length prompt+i+len))
      render
      ev <- getEvent w Nothing
      case ev of
        (Just (EventSpecialKey KeyBackspace)) -> repeat (drop 1 cs)
        (Just (EventCharacter '\n'))          -> finish (fmap (\(fpath,_,_) -> fpath) mb_best)
        (Just (EventCharacter '\ESC'))        -> finish Nothing
        (Just (EventCharacter c))
          | isPrint c                         -> repeat (c:cs)
        _                                     -> interact cs mb_best

    repeat cs = interact cs (select (reverse cs) fpaths)

    finish mb_best = do
      updateWindow w $ do
        (rows,cols) <- windowSize
        moveCursor (rows-2) 0
        clearLine
        drawString mainMenu
        clearLine
      render
      return mb_best

    select [] fpaths         = Nothing
    select cs []             = Nothing
    select cs (fpath:fpaths) =
      case contains fpath 0 of
        Nothing -> select cs fpaths
        Just i  -> Just (fpath,i,len)
      where
        len = length cs

        contains [] i         = Nothing
        contains s2 i
          | take len s2 == cs = Just i
          | otherwise         = contains (tail s2) (i+1)


foreign import ccall safe endwin :: IO CInt

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
                        (env,t:args) <- peekHeapArgs out env args
                        stk <- getStack dbg
                        case stk of
                          ((name',clo):stk) | name==name' -> do (env,_,clo) <- down out env clo
                                                                appStack out env stk (HE (HF (HC name clo) [HF t args]))
                          _                               -> appStack out env stk (HE (HF t args))
  let ptrs = fmap thd (Map.filter (\(c,zero,_) -> c > 1 && not zero) env)
  return (ptrs,t)
  where
    thd (_,_,x) = x

    peekHeapTree out env ptr =
      case Map.lookup ptr env of
        Just (c,zero,t)
                -> let t' | zero      = t
                          | otherwise = HP ptr
                   in return (Map.insert ptr (c+1,zero,t) env, zero, t')
        Nothing -> do mb_clo <- peekClosure dbg ptr
                      case mb_clo of
                        Nothing         -> return (env, True, HP ptr)
                        Just (name,clo) -> do let env1 = Map.insert ptr (1,True,HP ptr) env
                                              (env2,zero,clo) <- down out env1 clo
                                              let env3 = Map.adjust (\(c,_,_) -> (c,zero,HC name clo)) ptr env2
                                                  res  = case Map.lookup ptr out of
                                                           Just (c,zero,t) | c > 1 && not zero -> HP ptr
                                                                           | otherwise         -> t
                                                           Nothing                             -> HP ptr
                                              return (env3,zero,res)

    appStack out env []               t = return (env,t)
    appStack out env ((name,clo):stk) t = do
      (env,zero,clo) <- down out env clo
      appStack out env stk (HF (HC name clo) [t])

    down out env clo@(IntClosure info v) = return (env, True, IntClosure info v)
    down out env clo@(Int64Closure info v) = return (env, True, Int64Closure info v)
    down out env clo@(WordClosure info v) = return (env, True, WordClosure info v)
    down out env clo@(Word64Closure info v) = return (env, True, Word64Closure info v)
    down out env clo@(DoubleClosure info v) = return (env, True, DoubleClosure info v)
    down out env clo
      | elem typ [CONSTR,     CONSTR_0_1, CONSTR_0_2,
                  CONSTR_1_1, CONSTR_2_0, CONSTR_1_0,
                  FUN,        FUN_0_1,    FUN_0_2,
                  FUN_1_1,    FUN_2_0,    FUN_1_0,
                  THUNK,      THUNK_0_1,  THUNK_0_2,
                  THUNK_1_1,  THUNK_2_0,  THUNK_1_0,
                  THUNK_STATIC] =
          do (env2,args) <- peekHeapArgs out env (ptrArgs clo)
             let zero = name == "base_GHCziInt_I32zh_con_info" ||
                        name == "ghczmprim_GHCziTypes_Czh_con_info" ||
                        null (ptrArgs clo) && null (dataArgs clo)
             return (env2, zero, clo{ptrArgs=args})
      | elem typ [AP, PAP] =
          do (env2,_,fun) <- peekHeapTree out env (fun clo)
             (env3,pld) <- peekHeapArgs out env2 (payload clo)
             return (env3, null pld, clo{fun=fun, payload=pld})
      | elem typ [IND, IND_STATIC, BLACKHOLE] =
          do (env2,zero,ind) <- peekHeapTree out env (indirectee clo)
             return (env2,zero,clo{indirectee=ind})
      | elem typ [MVAR_CLEAN, MVAR_DIRTY] =
          do (env2,_,val) <- peekHeapTree out env (value clo)
             return (env2, False, clo{queueHead=HP (queueHead clo)
                                     ,queueTail=HP (queueTail clo)
                                     ,value=val
                                     })
      | elem typ [MUT_VAR_CLEAN, MUT_VAR_DIRTY] =
          do (env2,_,val) <- peekHeapTree out env (var clo)
             return (env2, False, clo{var=val})
      | elem typ [ARR_WORDS] =
          do return (env, False, clo{arrWords=arrWords clo})
      | elem typ [MUT_ARR_PTRS_CLEAN, MUT_ARR_PTRS_DIRTY,
                  MUT_ARR_PTRS_FROZEN_CLEAN, MUT_ARR_PTRS_FROZEN_DIRTY]=
          do (env2,elems) <- peekHeapArgs out env (mccPayload clo)
             return (env2, False, clo{mccPayload=elems})
      | typ == INVALID_OBJECT =
          do return (env, False, UnsupportedClosure (info clo))
      | otherwise =
          do (env2,args) <- peekHeapArgs out env (hvalues clo)
             let zero = null (hvalues clo) && null (rawWords clo)
             return (env2, zero, clo{hvalues=args})
      where
        typ  = tipe (info clo)

    peekHeapArgs out env []       = return (env, [])
    peekHeapArgs out env (x : xs) = do (env, _, x) <- peekHeapTree out env x
                                       (env, xs)   <- peekHeapArgs out env xs
                                       return (env, x : xs)

data HeapTreeAnn
  = FunName LinkerName
  | Current
  deriving (Eq,Show)

ppHeapTree d opts (HP ptr) = ppHeapPtr ptr
ppHeapTree d opts (HC name (IntClosure _ v)) = int v
ppHeapTree d opts (HC name (Int64Closure _ v)) = integer (fromIntegral v)
ppHeapTree d opts (HC name (WordClosure _ v)) = integer (fromIntegral v)
ppHeapTree d opts (HC name (Word64Closure _ v)) = integer (fromIntegral v)
ppHeapTree d opts (HC name (DoubleClosure _ v)) = double v
ppHeapTree d opts (HC name clo) =
  case tipe (info clo) of
    CONSTR        -> ppData name clo
    CONSTR_0_1
      | name == "base_GHCziInt_I32zh_con_info"
                  -> hsep (map (integer . fromIntegral) (dataArgs clo))
      | name == "ghczmprim_GHCziTypes_Czh_con_info"
                  -> hsep (map (text . show . chr . fromIntegral) (dataArgs clo))
      | otherwise -> ppData name clo
    CONSTR_0_2    -> ppData name clo
    CONSTR_1_1    -> ppData name clo
    CONSTR_2_0
      | name == "ghczmprim_GHCziTuple_Z2T_con_info"
                  -> let pargs = map (ppHeapTree 0 opts) (ptrArgs clo)
                     in parens (sep (punctuate comma pargs))
      | otherwise -> ppData name clo
    CONSTR_1_0    -> ppData name clo
    CONSTR_NOCAF  -> ppOther name clo
    FUN           -> ppData name clo
    FUN_1_0       -> ppData name clo
    FUN_0_1       -> ppData name clo
    FUN_2_0       -> ppData name clo
    FUN_1_1       -> ppData name clo
    FUN_0_2       -> ppData name clo
    FUN_STATIC    -> annotate (FunName name) (text (showName opts name))
    THUNK         -> ppData name clo
    THUNK_1_0     -> ppData name clo
    THUNK_0_1     -> ppData name clo
    THUNK_2_0     -> ppData name clo
    THUNK_1_1     -> ppData name clo
    THUNK_0_2     -> ppData name clo
    THUNK_STATIC  -> annotate (FunName name) (text (showName opts name))
    AP            -> let s  = ppHeapTree 1 opts (fun clo)
                         ss = map (ppHeapTree 1 opts) (payload clo)
                     in apply' d s ss
    PAP           -> let s  = ppHeapTree 1 opts (fun clo)
                         ss = map (ppHeapTree 1 opts) (payload clo)
                     in apply' d s ss
    IND           -> ppHeapTree d opts (indirectee clo)
    IND_STATIC    -> ppHeapTree d opts (indirectee clo)
    BLACKHOLE     -> ppHeapTree d opts (indirectee clo)
    MVAR_CLEAN    -> ppMVar clo
    MVAR_DIRTY    -> ppMVar clo
    MUT_VAR_CLEAN -> ppMutVar clo
    MUT_VAR_DIRTY -> ppMutVar clo
    ARR_WORDS     -> text "<ARR_WORDS" <+> sep (map (integer . fromIntegral) (arrWords clo)) <> char '>'
    MUT_ARR_PTRS_CLEAN -> ppMutArray clo
    MUT_ARR_PTRS_DIRTY -> ppMutArray clo
    MUT_ARR_PTRS_FROZEN_CLEAN -> ppMutArray clo
    MUT_ARR_PTRS_FROZEN_DIRTY -> ppMutArray clo
    UPDATE_FRAME  -> let pargs = map (ppHeapTree 1 opts) (hvalues clo)
                     in (text "<Update" <+> sep pargs <> char '>')
    CATCH_FRAME   -> let pargs = map (ppHeapTree 1 opts) (hvalues clo)
                     in (text "<Catch" <+> sep (map (integer . fromIntegral) (rawWords clo)++pargs) <> char '>')
    STOP_FRAME    -> ppOther name clo
    WEAK          -> let key:value:_ = rawWords clo
                         pargs = map (ppHeapTree 1 opts) (hvalues clo)
                     in apply' d (text "Weak#") (pargs++[ppHeapPtr key,ppHeapPtr value])
    RET_SMALL     -> ppOther name clo
    RET_FUN       -> ppOther name clo
    TSO           -> text "<TSO>"
  where
    ppData name clo =
       let pargs = map (ppHeapTree 1 opts) (ptrArgs clo)
           dargs = map (integer . fromIntegral) (dataArgs clo)
       in apply d opts name (pargs ++ dargs)

    ppOther name clo =
       let pargs = map (ppHeapTree 1 opts) (hvalues clo)
           dargs = map (integer . fromIntegral) (rawWords clo)
       in apply d opts name (pargs ++ dargs)

    ppMVar clo =
      let s = ppHeapTree 1 opts (value clo)
      in text "<MVAR" <+> s <> char '>'

    ppMutVar clo =
      let s = ppHeapTree 1 opts (var clo)
      in text "<MUT_VAR" <+> s <> char '>'

    ppMutArray clo =
      let elems = map (ppHeapTree 1 opts) (mccPayload clo)
      in text "<MUT_ARR" <+> sep elems <> char '>'
ppHeapTree d opts (HF t ts) =
  apply' d (ppHeapTree 1 opts t) (map (ppHeapTree 1 opts) ts)
ppHeapTree d opts (HE t) =
  annotate Current (ppHeapTree 1 opts t)

ppHeapPtr ptr = char '#' <> text (showHex ptr "")

showName opts name
  | name == "ZCMain_main_info" = ":Main_main_info"
  | take 3 name == "sc:"       = name
  | take 4 name == "stg_"      = reverse (drop 5 rname)
  | otherwise                  = reconstruct (reverse rname)
  where
    rname = reverse name

    reconstruct s
      | s1 == "info"   = x1
      | s2 == "info"   = (if optShowModule opts
                            then zDecodeString x1++"."
                            else "")++
                         (zDecodeString x2)
      | otherwise      = (if optShowPackage opts
                            then zDecodeString x1++":"
                            else "")++
                         (if optShowModule opts
                            then zDecodeString x2++"."
                            else "")++
                         (zDecodeString x3)
      where
        (x1,'_':s1) = break (=='_') s
        (x2,'_':s2) = break (=='_') s1
        (x3,_     ) = break (=='_') s2

apply d opts name ss
  | null ss   = s_doc
  | d > 0     = parens s2
  | otherwise = s2
  where
    s     = showName opts name
    s_doc = annotate (FunName name) (text s)

    s2 =
      case ss of
        [s1,s2] | isOperator -> s1 <+> s_doc <+> s2
        _                      -> s_doc <+> sep ss

    isOperator = not (any (flip elem chars) s)
      where
        chars = ['a'..'z']++['A'..'Z']++['0'..'9']++['_']

apply' d s [] = s
apply' d s ss
  | d > 0     = parens (s <+> sep ss)
  | otherwise = (s <+> sep ss)

