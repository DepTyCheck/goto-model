module Show.Program.LinearBlock

import Spec.Program.LinearBlock
import Show.Value
import Data.String
import Debug.Trace

public export
Show (LinearBlock cLim closeDec regs finalRegs) where
  show (Assign target i cont) = do
    let insn = "Assign \{show target} <- \{show i}"
    let rec = show cont
    if rec == ""
       then insn
       else joinBy "\n" [insn, rec]
  show (RegOp vop target @{MkFusedProduce @{ProduceOp @{hasTyL} @{_} @{hasTyR}}} cont) = do
    let li = toIndex hasTyL
    let ri = toIndex hasTyR
    let insn = "\{show vop} \{show target} <- \{show li} \{show ri}"
    let rec = show cont
    if rec == ""
       then insn
       else joinBy "\n" [insn, rec]
  show Finish = ""
  show _ = trace "Unreachable!!" ""
