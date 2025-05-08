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
  show (L savedRegs savedSrcs savedUc gs initRegs) =
    "L \{show savedRegs} \{show savedSrcs} \{show savedUc} \{show gs} \{show initRegs}"

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
Show (SinkIsValid a b c) where
  show SinkIsValidWithImmediate = "immediate sink"
  show SinkIsValidWithNothing = "just sink"

public export
Show (OpenLoopDecision a b c) where
  show NoNewLoop = "no loop"
  show (OneNewLoop {gs}) = "starts loop, guarantees = \{show gs}"

public export
Show (CloseLoopDecision a b) where
  show NoClose = "no loop closing"
  show (DoClose _) = "closes loop"

public export
showCond : (regIdx : Nat) ->
           (p : PrimaryPredicate vTy) ->
           (PredicateConstant p) ->
           (neg : Bool) ->
           String
-- Unary predicates
showCond regIdx IsTrue NoConstant neg =
  let negStr : String; negStr = if neg then "NOT " else "" in "\{negStr}r_\{show regIdx}"
-- Binary predicates
showCond regIdx p (Constant c) neg = "r_\{show regIdx} \{showPrimPred p neg} \{show c}"
  where
    showPrimPred : forall vTy . (p : PrimaryPredicate vTy) -> (neg : Bool) -> String
    showPrimPred LessThan False = "LT"
    showPrimPred Equal False = "EQ"
    showPrimPred LessThanOrEqual False = "LE"
    showPrimPred LessThan True = "GT"
    showPrimPred Equal True = "EQ"
    showPrimPred LessThanOrEqual True = "GE"
    showPrimPred IsTrue _ = ""  -- impossible

public export
showEdge : (edgeDec : EdgeDecision closeDec finalRegs canFinish) -> String
showEdge Exit = "Exit"
showEdge Jmp = "Jmp"
showEdge (Condjmp (ConditionAny condRegIdx pp x neg)) = "Condjmp \{showCond (toIndex condRegIdx) pp x neg}"
  where
    toIndex : HasUndet vs -> Nat
    toIndex HasUndetHere = Z
    toIndex (HasUndetThere prf') = S (toIndex prf')
showEdge (Condjmp (ConditionVar varRegIdx pp x neg)) = "Condjmp \{showCond (toIndex varRegIdx) pp x neg}"
  where
    toIndex : HasLoopVariant a b c d -> Nat
    toIndex Here = Z
    toIndex (There prf') = S (toIndex prf')

public export
Show (Program {n = S n'} immSrc delaSrc srcs cLim uc ols) where
  show (Step bs @{sink} @{loopDec} linBlk @{closeDec} edgeDec cont) = do
    let sinkStr : String; sinkStr = show sink
    let loopDecStr : String; loopDecStr = show loopDec
    let pre : String; pre = "Available: \{show $ length bs}, bs: \{show bs} (\{sinkStr}, \{loopDecStr})"

    let closeDecStr : String; closeDecStr = show closeDec
    let edgeStr : String; edgeDecStr = showEdge edgeDec
    let post : String; post = "\{edgeDecStr} (\{closeDecStr})"

    let ppBlk : ?; ppBlk = joinBy "\n" [pre, show linBlk, post]
    let rec : ?; rec = show cont
    if rec == ""
       then ppBlk
       else joinBy "\n" [ppBlk, rec]
  show Finish = "Finish"
  show FinishAll = "FinishAll"

