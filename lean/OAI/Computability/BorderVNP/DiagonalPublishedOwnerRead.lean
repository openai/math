import Lean

/-! # The stored receiving word at the owner of the published site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

/-- Read the receiving team's word through the actual owner's projection on an installed frame. -/
theorem publishedOwnerWord {cells teams : Nat} {installed configured : Nat → Fin teams}
    {word : Fin cells → Nat} (projection : installed=configured)
    (read : ∀ c, word c=(installed c.val).val) :
    ∀ c, word c=(configured c.val).val :=
  fun c => (read c).trans (congrArg Fin.val (congrFun projection c.val))

open Lean Meta Elab Term

/-- Apply the published-owner equality to the same finite cell and stored word. The word and both
owner tables are read from the supplied register observation and the actual writer projection. -/
elab "publishedOwnerRead% " read:term:max " via " projection:term:max : term => do
  let observed ← elabTerm read none
  let projected ← elabTerm projection none
  let some ownerEq ← whnfUntil (← inferType projected) ``Eq | throwError "expected the installed owner projection"
  let installed := ownerEq.getAppArgs[1]!
  let configured := ownerEq.getAppArgs[2]!
  forallBoundedTelescope (← inferType observed) (some 1) fun atCell observation => do
    unless atCell.size == 1 do throwError "expected an observation of every finite cell"
    let c := atCell[0]!
    let some cellType ← whnfUntil (← inferType c) ``Fin | throwError "expected the physical cell index"
    let some wordEq ← whnfUntil observation ``Eq | throwError "expected the stored receiving word"
    let some teamType ← whnfUntil (← inferType (mkApp installed (mkProj ``Fin 0 c))) ``Fin |
      throwError "expected the finite team recorded by the installed owner"
    let words ← mkLambdaFVars atCell wordEq.getAppArgs[1]!
    return mkAppN (mkConst ``publishedOwnerWord) #[cellType.getAppArgs.back!,teamType.getAppArgs.back!,
      installed,configured,words,projected,observed]

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
