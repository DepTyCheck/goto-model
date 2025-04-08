module Show.Program.Raw

import Spec.Program

import Show.Value
import Show.Program.LinearBlock
import Data.String

public export
Show (Source n) where
  show (Src vs) = "(\{show vs})"

public export
Show (VectSource {}) where
  show srcs = "[\{show' srcs}]"
  where
    show' : VectSource m n -> String
    show' [] = ""
    show' [src] = show src
    show' (src :: src1 :: srcs) = "\{show src}, \{show' $ src1 :: srcs}"

public export
Show (VectBool {}) where
  show bs = "[\{show' bs 0}]"
  where
    show' : VectBool m -> Nat -> String
    show' [] _ = ""
    show' [False] _ = ""
    show' [True] n = show n
    show' (False :: bs) n = show' bs n
    show' (True :: bs) n = do
      let rec = show' bs (S n)
      if rec == ""
         then show n
         else joinBy ", " [show n, rec]

public export
Show (Program {n = S n'} immSrc delaSrc srcs cLim uc ols) where
  show (Step bs @{sink} @{loopDec} linBlk @{closeDec} edgeDec cont) = do
    let sinkStr : String; sinkStr = case sink of
                                         SinkIsValidWithImmediate => "immediate sink"
                                         SinkIsValidWithNothing => "just sink"
    let loopStr : String; loopStr = case loopDec of
                                         NoNewLoop => "no loop"
                                         -- OneNewLoop => "starts loop"
    let pre = "Available: \{show $ length bs}, bs: \{show bs} (\{sinkStr}, \{loopStr})"
    let post : String; post = case edgeDec of
                                   Exit => "Exit"
                                   Jmp => "Jmp"
                                   Condjmp => "Condjmp"
    let ppBlk : ?; ppBlk = joinBy "\n" [pre, show linBlk, post]
    let rec : ?; rec = show cont
    if rec == ""
       then ppBlk
       else joinBy "\n" [ppBlk, rec]
  show Finish = "Finish"
  show FinishAll = "FinishAll"

