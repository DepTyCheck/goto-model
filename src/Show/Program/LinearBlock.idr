module Show.Program.LinearBlock

import Spec.Program
import Show.Value
import Data.String

public export
Show (LinearBlock regs finalRegs) where
  show (Assign target i cont) = do
    let insn = "Assign \{show target} <- \{show i}"
    let rec = show cont
    if rec == ""
       then insn
       else joinBy "\n" [insn, rec]
  show (RegOp vop target @{ProduceOp @{hasTyL} @{_} @{hasTyR}} cont) = do
    let li = toIndex hasTyL
    let ri = toIndex hasTyR
    let insn = "\{show vop} \{show target} <- \{show li} \{show ri}"
    let rec = show cont
    if rec == ""
       then insn
       else joinBy "\n" [insn, rec]
  show Finish = ""
