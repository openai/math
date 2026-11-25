import OAI.Computability.BorderVNP.CrossingIntegral
import OAI.Computability.VPVNP.VerifierMachineNetwork

/-!
# Local input format for the signed crossing verifier

The two signed output flags contribute their difference. The query ports
consist of a one-hot terminal index, a one-hot padded mode, and occupation
masks of the old and new states. Only the private block is summed locally.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.FusionStage

open VPVNP.VerifierNetwork

/-- The physical query bits of one crossing table. -/
abbrev Query (q H E : ℕ) := Fin q ⊕ Fin (2*H) ⊕ Fin E ⊕ Fin (E+H)

/-- One-hot terminal/mode indicators and the masks on the adjacent state cuts. -/
def queryBits {q H E : ℕ} (x : Fin q) (j : Fin (2*H)) (old : EnergyState E)
    (next : EnergyState (E+H)) : Query q H E → Bool :=
  Sum.elim (fun t => decide (t=x)) (Sum.elim (fun r => decide (r=j))
    (Sum.elim (fun i => decide (i.val ∈ old.val)) (fun i => decide (i.val ∈ next.val))))

/-- Positive paths count once and negative paths count with the opposite sign. -/
def signValue (o : Bool → Bool) : ℤ := (o false).toNat - ((o true).toNat : ℤ)

/-- A verified local signed crossing circuit, including zeroes on all unused mode codes. -/
structure Checker {q H : ℕ} (w : WireStates H q) (E : ℕ) (reverse left : Bool) where
  /-- Number of private witness bits for the local path. -/
  guesses : ℕ
  /-- Two signed output flags on query and private witness bits. -/
  frame : Frame (Query q H E ⊕ Fin guesses) Bool
  /-- The path sum computes the padded integer coefficient of the specified orientation. -/
  correct : ∀ (x : Fin q) (j : Fin (2*H)) (old : EnergyState E) (next : EnergyState (E+H)),
    (∑ a : Fin guesses → Bool, signValue (frame.eval (Sum.elim (queryBits x j old next) a))) =
    if h : j.val < w.weight then w.factors E reverse left (⟨j.val,h⟩,next) x old else 0

end Crossing.FusionStage

end BorderVNP
end Computability
end OAI
