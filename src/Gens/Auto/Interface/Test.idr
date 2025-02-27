module Gens.Auto.Interface.Test

import Gens.Auto.Interface.Common
import public Spec.Program
import public Spec.Value.Decidable


public export
genSquash : Fuel ->
           {vTy : _} -> {savedIsDet, initIsDet, finalIsDet, isDet : _} -> (uc' : _) -> 
           (savedExpr : VExpr (Just vTy) savedIsDet) -> (initExpr : VExpr (Just vTy) initIsDet) ->
           (finalExpr : VExpr (Just vTy) finalIsDet) -> (uc : _) ->
           Gen MaybeEmpty $ (vExpr : VExpr (Just vTy) isDet ** Squash uc' savedExpr initExpr finalExpr uc vExpr)

public export
genPick : Fuel ->
          {n : _} -> (ss : ListSource n) ->
          Gen MaybeEmpty $ (uc ** vs ** ss' ** Pick ss uc vs ss')

