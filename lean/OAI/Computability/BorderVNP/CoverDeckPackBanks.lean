import OAI.Computability.BorderVNP.PackedChoiceMux
import OAI.Computability.BorderVNP.PackedDeckWeightedChoice
import OAI.Computability.BorderVNP.CoverDeckRefinementFrame

/-!
# The two count banks supplied to deck refinement

The prior tile counts pass through on the first channel. A shared one-hot
motion label selects a complete candidate bank for the second channel.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open VPVNP.VerifierNetwork (Frame Expr)
open BinPackingGames.Foundations.Complexity.CookLevin
open PackedDeckCandidate

/-- Count arrays, updated mean numerators, and one-hot finite motion label. -/
abbrev ChoicePins (B : Type*) (q l m w : ℕ) := Input B (Fin q → Deck l) m w ⊕ Fin m

private def bankExpr (B : Type*) (q l m w : ℕ) (p : CountBits B q l w) : Expr (ChoicePins B q l m w) :=
  if p.1 then PackedChoiceMux.read Sum.inr (fun j => .inl (.inl (some j,p.2))) else .input (.inl (.inl (none,p.2)))

/-- Realize the choice of a complete candidate array in parallel, one
short multiplexer per selected output bit. -/
noncomputable def packBanks (B : Type*) [Fintype B] (q l m w : ℕ) :
    Frame (ChoicePins B q l m w) (CountBits B q l w) := (Frame.initial id).step (bankExpr B q l m w)

theorem packBanks_size (B : Type*) [Fintype B] (q l m w : ℕ) :
    (packBanks B q l m w).size ≤ Fintype.card (CountBits B q l w)*(4*m+1) := by
  apply (Frame.step_size_le _ _ (4*m+1) ?_).trans_eq (Nat.zero_add _)
  intro p
  unfold bankExpr
  split
  · exact PackedChoiceMux.read_size _ _
  · change 1 ≤ 4*m+1
    omega

/-- The two physical count words exposed by the selected motion. -/
def bankWord {B : Type*} {q l m w : ℕ} (x : Input B (Fin q → Deck l) m w → Bool)
    (j : Fin m) (p : CountBits B q l w) := x (.inl (if p.1 then some j else none,p.2))

theorem packBanks_eval {B : Type*} [Fintype B] {q l m w : ℕ} (y : ChoicePins B q l m w → Bool)
    (x : Input B (Fin q → Deck l) m w → Bool) (j : Fin m)
    (hraw : ∀ p, y (.inl (.inl p)) = x (.inl p)) (hflag : ∀ i, y (.inr i) = true ↔ i=j) :
    (packBanks B q l m w).eval y = bankWord x j := by
  have hid : (Frame.initial id).eval y = y := funext (Frame.initial_eval id y)
  funext p
  rcases p with ⟨s,tail⟩
  cases s <;> simp [packBanks,bankExpr,bankWord,hid,StatementCircuit.Expr.eval,
    PackedChoiceMux.read_eval _ _ y j hflag,hraw]

@[simp] theorem physicalCount_bankWord {B : Type*} {q l m w : ℕ}
    (x : Input B (Fin q → Deck l) m w → Bool) (j : Fin m) (s : Bool) (b : B) (g : Fin q → Deck l) :
    physicalCount (bankWord x j) s b g = inputCounts x (if s then some j else none) b g := rfl

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
