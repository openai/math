import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicPrimeWord
import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicPrimeWordIdentify

/-! # Realizing the dyadic prime-axis algebra map on physical registers

The Rader Fourier word and its inverse use the same occupied workspace.
Seven mixing slots and one relabeling slot suffice beyond the Fourier depth.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation.DyadicPrimeAxis

open Matrix

variable {R : Type*} [CommRing R] [Nontrivial R] {p : ℕ} [Fact p.Prime]
  {C : PrimeAxisOrbit p} {u : Rˣ} {hm : IsUnit ((p-1 : ℕ) : R)} (a : DyadicPrimeAxis R p C u hm)
  {J : Type}

local notation "m" => (p-1)

/-- The inverse basis change, in physical orbit order, is the inverse raw matrix. -/
theorem backward_submatrix :
    a.backward.submatrix C.optionEquiv id =
      (dyadicPrimeForwardMatrix ⟨0, by have := (Fact.out : p.Prime).two_le; omega⟩ u hm a.diagonal)⁻¹ := by
  rw [← a.forward_submatrix]
  symm
  apply Matrix.inv_eq_right_inv
  rw [Matrix.submatrix_mul_equiv, a.forward_mul_backward, Matrix.submatrix_id_id]

/-- In a physical ordering, row labels specify basis frequencies and column
labels specify cyclic residues. Only the latter pass through the orbit enumeration. -/
theorem forward_reindex (rows : J ≃ Option (Fin m)) (cols : J ≃ ZMod p) :
    a.forward.submatrix rows cols =
      (dyadicPrimeForwardMatrix ⟨0, by have := (Fact.out : p.Prime).two_le; omega⟩ u hm
        a.diagonal).submatrix rows (cols.trans C.optionEquiv.symm) := by
  rw [← a.forward_submatrix]
  ext i j
  simp

/-- For the inverse change the physical output and input relabelings exchange places. -/
theorem backward_reindex (rows : J ≃ Option (Fin m)) (cols : J ≃ ZMod p) :
    a.backward.submatrix cols rows =
      (dyadicPrimeForwardMatrix ⟨0, by have := (Fact.out : p.Prime).two_le; omega⟩ u hm
        a.diagonal)⁻¹.submatrix (cols.trans C.optionEquiv.symm) rows := by
  rw [← a.backward_submatrix]
  ext i j
  simp

variable [Fintype J] [DecidableEq J] {W : Type} [Fintype W] [DecidableEq W] {D : ℕ}

/-- Compile both directions of the prime-axis algebra isomorphism for arbitrary
physical orderings of the source cyclic powers and target split monomials. -/
theorem occupiedWord_pair (rows : J ≃ Option (Fin m)) (cols : J ≃ ZMod p)
    (hp : IsUnit (p:R)) (hu : u^m = 1)
    (hs : Pairwise fun i j : Fin m => IsUnit ((u:R)^i.val - (u:R)^j.val))
    (hF : OccupiedWord W D (geometricMatrix m (u:R)))
    (hB : OccupiedWord W D (geometricMatrix m (u:R))⁻¹) :
    OccupiedWord W (D+8) (a.forward.submatrix rows cols) ∧
    OccupiedWord W (D+8) (a.backward.submatrix cols rows) := by
  have hptwo := (Fact.out : p.Prime).two_le
  have hm1 : m + 1 = p := by omega
  have hp' : IsUnit (((m : ℕ) : R) + 1) := by
    rw [← Nat.cast_add_one, hm1]
    exact hp
  let z : Fin m := ⟨0, by omega⟩
  have h := occupiedWord_dyadicPrimeForwardMatrix_pair z rfl u hm hp' hu hs
    a.diagonal a.diagonal_zero hF hB
  rw [show D + 8 = (7+D)+1 by omega]
  apply occupiedWord_rectangular_reindex_pair a.forward_mul_backward C.optionEquiv _ _ rows cols
  · rw [a.forward_submatrix]
    exact h.1
  · rw [a.forward_submatrix]
    exact h.2

end Deformation.DyadicPrimeAxis

end FiniteFourier
end LinearAlgebra
end OAI
