import OAI.Computability.BorderVNP.DiagonalCalendarLookupOpeningWords

/-! # The installed opening words at a rebanked site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open VPVNP.BurstRAM RoutingISA
/-- Opening words can be read from the returned memory that the processor identifies with the recorded one. -/
theorem readAtOriginalMemory {w : ℕ} (P : (ℕ → ℕ) → Prop)
    {m₁ m₂ : Memory w} (eq : m₁ = m₂) (h : P (readings m₂)) : P (readings m₁) := by
  subst m₂
  exact h

open Lean Meta Elab Term in
/-- Take the actual opening-word observation at this exterior and team, and transport it
along the equality of the two physical site memories recorded in its first stage. -/
elab (name := openingWordsOnHistory) "openingWordsOnHistory% " width:term:max reads:ident exterior:ident team:ident stages:ident : term => do
  let operandAt (id : TSyntax `ident) : TermElabM Expr := do
    let value ← getFVarFromUserName id.getId
    addTermInfo' id value
    return value
  let teamValue ← operandAt team
  let seen := mkApp2 (← operandAt reads) (← operandAt exterior) teamValue
  let originalSite := mkApp (← operandAt stages) teamValue
  let equal := Expr.proj ``And 0 originalSite
  let some observation ← whnfUntil (← inferType seen) ``SignedCalendarAt.LookupOpeningWords |
    throwError "expected the original compiled opening words on the issued RAM"
  let some same ← whnfUntil (← inferType equal) ``Eq | throwError "expected the witnessed original memory"
  let predicate := observation.appFn!
  return mkAppN (Lean.mkConst ``readAtOriginalMemory) #[← elabTerm width none, predicate,
    same.getAppArgs[1]!, same.getAppArgs[2]!, equal, seen]

end Diagonal

end BorderVNP
end Computability
end OAI
