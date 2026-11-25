import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sort

namespace OAI
/-! # Counting strictly increasing choices of marked positions -/

namespace Hierarchy.FormulaPartition

/-- The first mark is fixed at zero. The remaining marks occupy distinct
positive positions along the chain. -/
abbrev Positions (t L : ℕ) :=
  {f : Fin (t+1) → Fin (L+1) // StrictMono f ∧ f 0 = 0}

noncomputable instance (t L : ℕ) : Fintype (Positions t L) := by
  classical
  unfold Positions
  infer_instance

theorem card_positions (t L : ℕ) : Fintype.card (Positions t L) ≤ 2^L := by
  classical
  let mask (p : Positions t L) : Finset (Fin L) :=
    Finset.univ.filter (fun j => j.succ ∈ Set.range p.val)
  have inj : Function.Injective mask := by
    intro p q eq
    apply Subtype.ext
    apply (p.property.1.range_inj_of_wellFoundedLT q.property.1).mp
    apply Set.ext
    intro a
    refine Fin.cases ?_ (fun j => ?_) a
    · exact iff_of_true ⟨0,p.property.2⟩ ⟨0,q.property.2⟩
    · have same : j ∈ mask p ↔ j ∈ mask q := by rw [eq]
      simpa [mask] using same
  simpa only [Fintype.card_finset,Fintype.card_fin] using Fintype.card_le_of_injective mask inj

end Hierarchy.FormulaPartition

end OAI
