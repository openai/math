import OAI.LinearAlgebra.SpectralBooks.Fermion.WickReversalEquiv
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickResidualLength
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickSkew

/-! # Block exchange in the Wick expansion -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

variable {α k E : Type*} [CommRing k] [Ring E] [Algebra k E]
variable (C A : α → E)
variable (hcc : ∀ x y, C x * C y + C y * C x = 0)
variable (haa : ∀ x y, A x * A y + A y * A x = 0)

include hcc haa in
/-- With the kernel reoriented, each reversed term equals its forward term
times the sign of the block interchange. -/
theorem wickTerm_reverse (κ : α → α → k) {l r : List α} (p : Matching l r) :
    p.reverse.weight (fun x y ↦ -κ y x) • normal k C A p.reverse.residual =
      (-1 : k)^(l.length*r.length) • (p.weight κ • normal k C A p.residual) := by
  rw [Matching.weight_reverse, p.reverse.residual_eq_append, p.residual_eq_append,
    Matching.leftRest_reverse, Matching.rightRest_reverse,
    normal_append_swap k C A hcc haa p.leftRest p.rightRest, p.leftRest_length, p.rightRest_length,
    pow_add, smul_smul, smul_smul]
  congr 1
  ring

include hcc haa in
/-- Reindexing by the reversed matching exchanges the Wick sums with the
single sign for swapping the original blocks. -/
theorem wickSum_reverse (κ : α → α → k) (l r : List α) :
    wickSum (fun x y ↦ -κ y x) (normal k C A) r l =
      (-1 : k)^(l.length*r.length) • wickSum κ (normal k C A) l r := by
  unfold wickSum
  rw [Finset.smul_sum, ← (Matching.reverseEquiv l r).sum_comp]
  apply Finset.sum_congr rfl
  intro p _
  exact wickTerm_reverse C A hcc haa κ p

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
