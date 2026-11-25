import OAI.ThreeFlat.Routing.SpillCompactionCore
import OAI.ThreeFlat.Routing.SpillStageCost

namespace OAI
/-! # The complete repeated-halving sparse compactor

Every intermediate two-pass graph is fixed at its public bank size. A common
per-slot charge at the largest scale pays for all the smaller banks.
-/

noncomputable section
open scoped Classical
namespace ThreeFlat.Routing.Spill
open Concentrator

/-- At all sufficiently large terminal bank sizes there is a uniform
linear-logarithmic-cost compactor for every positive number of halvings. -/
theorem exists_dyadic_compactors (F : Type*) [CommSemiring F] :
    ∃ cutoff c : ℕ, ∀ last, cutoff ≤ 2*last → ∀ k w,
      ∃ s : Compactor F (2^(k+1)*last) last w,
        s.network.cells ≤ 2^(k+1)*last*(Nat.log 2 (2^(k+1)*last)+w+3)*c := by
  obtain ⟨cutoff,D,h⟩ := exists_two_pass_banks (C := 2) (q := 2) (by decide) (by decide)
  refine ⟨cutoff,3*bankCharge D,?_⟩
  intro last hc k w
  apply dyadic_of_halvings
  intro r hr
  obtain ⟨B⟩ := h r (hc.trans (Nat.mul_le_mul_left _ hr))
  refine ⟨⟨twoPassStage (F := F) B w,
    fun x legal => twoPassStage_complete (F := F) B w x (by omega),
    twoPassStage_preserves (F := F) B w,
    packingStage_zeroBlanks (F := F) _ _ _ _ _⟩,?_⟩
  exact (twoPassStage_cells (F := F) B w).trans_eq (by ring)

/-- Arbitrary-size compaction with a public, sufficiently large terminal
bank. The cost increases only by the constant factor for dyadic padding. -/
theorem exists_sparse_compactors (F : Type*) [CommSemiring F] :
    ∃ cutoff c : ℕ, ∀ n r w : ℕ, 0 < r → r ≤ n → cutoff ≤ 2*r →
      ∃ s : Compactor F n r w, s.network.cells ≤ n*(Nat.log 2 n+w+4)*c := by
  obtain ⟨cutoff,c,dyadic⟩ := exists_dyadic_compactors F
  refine ⟨cutoff,2*c,?_⟩
  intro n r w hr hrn hc
  exact compactor_of_dyadic hr hrn (fun k => dyadic r hc k w)

end ThreeFlat.Routing.Spill

end
end OAI
