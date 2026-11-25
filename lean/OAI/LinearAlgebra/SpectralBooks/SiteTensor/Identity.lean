import OAI.LinearAlgebra.SpectralBooks.Exterior.Exterior
import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Split

/-! # The ordinary sum identity for an exterior split

The marked coefficient tensor multiplied by the diagonal on an exterior
level is the ordinary sum of the two orders of exterior contraction. Grouping
any of the labels preserves this coefficient identity, giving the restriction
bound on the sum of their classes even when the placement has collisions.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SiteTensor.Relocation

open Exterior
open scoped BigOperators Classical

variable {I J : Type} {K : Type*} {A : I → Type} [CommRing K] {Q b : ℕ}

/-- The two orders of contraction produce a diagonal on the exterior labels,
with the original marked tensor as coefficient. -/
theorem plus_add_minus_eq (T : (∀ i, A i) → Fin Q → K)
    (x : ∀ i, A i) (i : Fin Q) (α β : Level Q (b + 1)) :
    plusCoeff T (create K) (contract K) x i α β +
      minusCoeff T (contract K) (create K) x i α β =
        T x i * (if α = β then 1 else 0) := by
  have h := split_coeff K (T x) i β α
  simp only [Matrix.mul_apply, Finset.sum_mul] at h
  simpa only [plusCoeff, minusCoeff, mul_assoc, mul_comm, mul_left_comm, eq_comm] using h

/-- In any placement, the restriction class of an ordinary sum is at most the
direct sum of its classes. All three local formats agree definitionally. -/
theorem grouped_split_le_of_add {U H : Type} [Fintype U] [Fintype H]
    [Fintype I] [Fintype J] [Nonempty J] [∀ i, Fintype (A i)]
    (σ : I → J) (c a d : J) (P S R : (∀ i, A i) → U → H → H → K)
    (hsum : ∀ x i α β, P x i α β = S x i α β + R x i α β) :
    ofRaw ((split A U H P).group (placeSplit σ c a d)) ≤
      ofRaw ((split A U H S).group (placeSplit σ c a d)) +
        ofRaw ((split A U H R).group (placeSplit σ c a d)) := by
  let V (f : (∀ i, A i) → U → H → H → K) := (split A U H f).group (placeSplit σ c a d)
  let s : (∀ j, (V P).Leg j) → K := (V S).coeff
  let t : (∀ j, (V P).Leg j) → K := (V R).coeff
  have he : (V P).coeff = s + t := funext fun _ => hsum _ _ _ _
  apply ofRaw_le_iff.mpr
  change Crossing.IsRestriction (V P).coeff (sumCoeff s t)
  rw [he]
  exact ordinary_add_restricts _ _

/-- The class inequality at every node of the exterior splitting tree. -/
theorem grouped_split_le [Fintype I] [Fintype J] [Nonempty J] [∀ i, Fintype (A i)]
    (T : (∀ i, A i) → Fin Q → K) (σ : I → J) (c a d : J) :
    ofRaw ((split A (Fin Q) (Level Q (b + 1))
      (fun x i α β => T x i * (if α = β then 1 else 0))).group (placeSplit σ c a d)) ≤
      ofRaw ((split A (Fin Q) (Level Q (b + 1)) (plusCoeff T (create K) (contract K))).group
        (placeSplit σ c a d)) +
      ofRaw ((split A (Fin Q) (Level Q (b + 1)) (minusCoeff T (contract K) (create K))).group
        (placeSplit σ c a d)) :=
  grouped_split_le_of_add σ c a d _ _ _ fun x i α β => (plus_add_minus_eq T x i α β).symm

end SiteTensor.Relocation

end

end SpectralBooks
end LinearAlgebra
end OAI
