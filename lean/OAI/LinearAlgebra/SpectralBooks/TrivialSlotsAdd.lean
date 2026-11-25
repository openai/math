import OAI.LinearAlgebra.SpectralBooks.TrivialSlots

/-! # Direct sums with one-dimensional slots

On each unoccupied site the local addition map sends both scalar blocks
to the single scalar slot. The occupied sites retain their two blocks.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

open scoped BigOperators Classical
universe v u w z

variable {S : Type u} (O : Type z) {K : Type w} [Fintype S] [Fintype O] [CommSemiring K]

/-- Extension by scalar slots takes a direct sum on the occupied sites to a
restriction of the direct sum on all sites. -/
theorem withTrivial_add_restricts (X Y : Raw.{v} S K) :
    (withTrivial O (add X Y)).Restricts (add (withTrivial O X) (withTrivial O Y)) := by
  classical
  let : DecidableEq (S ⊕ O) := Classical.decEq _
  let M (i : S ⊕ O) : (withTrivial O (add X Y)).Leg i →
      (add (withTrivial O X) (withTrivial O Y)).Leg i → K := match i with
    | .inl _ => fun x a => if a = x then 1 else 0
    | .inr _ => fun _ _ => 1
  refine ⟨M, fun x => ?_⟩
  change sumCoeff X.coeff Y.coeff (fun s => x (.inl s)) =
    ∑ a, sumCoeff (withTrivial O X).coeff (withTrivial O Y).coeff a *
      ∏ i, M i (x i) (a i)
  simp only [sumCoeff, add_mul, Finset.sum_add_distrib]
  rw [sum_pushCoeff_mul, sum_pushCoeff_mul]
  have weight {B : S → Type v} (a b : ∀ i, B i) (q : K) :
      (@ite K (a = b) (Classical.propDecidable _) q 0) = q * ∏ i, (if a i = b i then (1 : K) else 0) := by
    simp [Fintype.prod_boole, ← funext_iff, mul_ite]
  congr 1
  · unfold pushCoeff
    refine Fintype.sum_equiv (withTrivialIndex O X).symm _ _ (fun a => ?_)
    simp only [withTrivial, withTrivialIndex, Fintype.prod_sum_type, M, Finset.prod_const_one,
      mul_one]
    exact weight (B := fun s => X.Leg s ⊕ Y.Leg s) (fun s => .inl (a s)) (fun s => x (.inl s)) (X.coeff a)
  · unfold pushCoeff
    refine Fintype.sum_equiv (withTrivialIndex O Y).symm _ _ (fun a => ?_)
    simp only [withTrivial, withTrivialIndex, Fintype.prod_sum_type, M, Finset.prod_const_one,
      mul_one]
    exact weight (B := fun s => X.Leg s ⊕ Y.Leg s) (fun s => .inr (a s)) (fun s => x (.inl s)) (Y.coeff a)

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
