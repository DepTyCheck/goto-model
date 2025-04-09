module Show.Program.Raw

import Spec.Program

import Show.Value
import Show.Program.LinearBlock
import Data.String

public export
Show (Source n) where
  show (Src vs) = "(\{show vs})"

public export
Show (MaybeSource n) where
  show Nothing = "(Nothing)"
  show (Just $ Src vs) = "(Just \{show vs}\)"

public export
Show (VectSource {}) where
  show srcs = "[\{show' srcs}]"
  where
    show' : VectSource m n -> String
    show' [] = ""
    show' [src] = show src
    show' (src :: src1 :: srcs) = "\{show src}, \{show' $ src1 :: srcs}"

public export
Show Guarantee where
  show GValue = "GValue"
  show GType = "GType"
  show GNothing = "GNothing"

public export
Show (VectGuarantee n) where
  show gs = "[\{show' gs}]"
    where
      show' : forall n . VectGuarantee n -> String
      show' [] = ""
      show' [g] = show g
      show' (g1 :: g2 :: gs) = "\{show g1}, \{show' (g2 :: gs)}"

public export
Show (Loop n) where
  show (L savedRegs savedSrcs savedUc gs initRegs) = "L \{show savedRegs} \{show savedSrcs} \{show savedUc} \{show gs} \{show initRegs}"

public export
Show (ListLoop n) where
  show ols = "[\{show' ols}]"
    where
      show' : forall n . ListLoop n -> String
      show' [] = ""
      show' [ol] = show ol
      show' (ol1 :: ol2 :: ols) = "\{show ol1}, \{show' $ ol2 :: ols}"

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
                                         OneNewLoop => "starts loop"
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

