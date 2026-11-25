import OAI.Computability.BorderVNP.PackedHistoryOuter

/-! # Public transcript sum of an iterated physical pack expansion -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Shortening.Adaptive Packing Crossing VPVNP.VerifierNetwork
open scoped Classical

variable {K T : ℕ} {A : ℕ → Type*} {W G : ℕ → Type}
variable [∀ j, Fintype (W j)] [∀ j, Fintype (G j)]
variable {σ R : Type*} [Fintype σ] [AddCommMonoid R]

/-- A public bit assignment contributes the value of its actual outer physical pack.
Invalid assignments contribute zero, and the whole sum reproduces precisely the
manuscript's dependent packHistory with its original multiplicities. -/
theorem sum_outer (bottom : A 0) (epoch : ∀ t, (Fin K → A t) → ProfileSum (A (t+1)))
    (C : Codec (outerSystem T epoch) G) (rep : Represents A W) (step : Steps K T W G)
    (ok : LocalCorrect C rep step) (f : Frame σ (W 0)) (x : σ → Bool) (h : rep 0 (f.eval x) bottom)
    (readout : (W T → Bool) → R) (value : A T → R) (hr : ∀ z s, rep T z s → readout z = value s) :
    (∑ g : Slot K G T → Bool, if flag step T le_rfl (repeatLeaf K f T) x g then
      readout (output step T le_rfl (repeatLeaf K f T) x g) else 0) =
      ∑ q, value ((packHistory bottom epoch T).term q) := by
  have hl (n : ℕ) : LeafState rep x n (repeatLeaf K bottom n) (repeatLeaf K f n) := by
    induction n with
    | zero => exact h
    | succ n ih => exact fun _ => ih
  rw [sum_transcripts C rep step ok T le_rfl _ _ x (hl T) readout value hr]
  rw [← (outerEquiv bottom epoch T le_rfl).sum_comp]
  exact Finset.sum_congr rfl fun q _ => congrArg value (outerEquiv_state bottom epoch T le_rfl q).symm

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
