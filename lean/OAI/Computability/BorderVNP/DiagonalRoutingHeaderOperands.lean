import OAI.Computability.BorderVNP.PackedRoutingHeaders

/-! # Matching a returned header to the operands of a native call -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Lean Meta Packing.RoutingOutputs

private theorem onRegisteredWords {h₀ o₀ e₀ c₀ n₀ : ℕ} {m₀ : ℕ → ℕ}
    {h₁ o₁ e₁ c₁ n₁ : ℕ} {m₁ : ℕ → ℕ}
    (head : h₀=h₁) (origin : o₀=o₁) (edges : e₀=e₁) (cells : c₀=c₁)
    (entries : n₀=n₁) (memory : m₀=m₁) (observed : Header h₀ o₀ e₀ c₀ n₀ m₀) :
    Header h₁ o₁ e₁ c₁ n₁ m₁ := by
  cases head; cases origin; cases edges; cases cells; cases entries; cases memory
  exact observed

/-- Use a returned routing header at the six operands requested by its caller.
The frame address, directory origin, two geometry sizes, entry count and memory
are checked separately so the selected calendar remains folded. -/
def routingHeaderOnOperands (receipt requested : Expr) : MetaM Expr := do
  let some returned ← whnfUntil (← inferType receipt) ``Header
    | throwError "expected a routing header from the actual return"
  let some required ← whnfUntil requested ``Header
    | throwError "expected the routing header of the native call"
  let stored := returned.getAppArgs
  let given := required.getAppArgs
  let mut same := #[]
  for left in stored, right in given, index in [:stored.size] do
    unless ← isDefEq left right do
      throwError "the returned routing header differs from its native call at operand {index}"
    same := same.push (← mkEqRefl left)
  return mkAppN (mkConst ``onRegisteredWords) (stored ++ given ++ same ++ #[receipt])

end Diagonal

end BorderVNP
end Computability
end OAI
