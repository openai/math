import OAI.Computability.VPVNP.ShiftedReadout
import OAI.Computability.VPVNP.ShiftedResidue

/-!
# Matrix identity for shifted fermionic crossing

Each summand in the coefficient extracted in Appendix B is the product of
two finite matrices supported on opposite energy shifts. We recover these
matrices from the shifted residue, with one summand for each term of
`(z - w)^d`. The result is valid also between states of unequal energy.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Crossing

open Lemmata.FockCircuits Lemmata.FockCircuits.FiniteIdentity
open scoped BigOperators
open LaurentPolynomial

variable (R : Type*) [CommRing R]

/-- Opposite-order fermionic modes recover the vacuum pairing times the
identity matrix, at any shift inside the enlarged cutoff. -/
theorem shifted_operator_identity (L K : ℕ) (A B I J : Index L) (d : ℕ) (s : ℤ)
    (hd : 2 * d + 2 = sourceEnergy A.val.sort + sourceEnergy B.val.sort)
    (hcut : doubledEnergy J.val + K + max (sourceEnergy A.val.sort) (sourceEnergy B.val.sort) + 4 ≤ 2 * L)
    (hs : |-2 * s - 2| ≤ K) :
    (∑ a : Fin (d + 1), (-1 : R) ^ (a : ℕ) * d.choose a *
      (let q := 2 * s + (doubledEnergy B.val : ℤ) - 2 * (a : ℕ)
       (diagonal R L (-q) (Pi.single A 1) * diagonal R L q (Pi.single B 1)) I J -
         (-1 : R) ^ (A.val.sort.length * B.val.sort.length) *
           (diagonal R L q (Pi.single B 1) * diagonal R L (-q) (Pi.single A 1)) I J)) =
      (if I = J then (1 : R) else 0) * matrix R L (Pi.single A 1) ⟨∅, by simp⟩ B := by
  let energy : Index L → ℤ := fun i => doubledEnergy i.val
  let aMat := matrix R L (Pi.single A 1)
  let bMat := matrix R L (Pi.single B 1)
  have hA : energyField energy (doubledEnergy A.val) aMat = scaledMatrix R L A := by
    apply Matrix.ext
    intro i j
    exact (scaledMatrix_eq_monomial R L A i j).symm
  have hB : bMat.map C = constantMatrix R L B := rfl
  by_cases hij : doubledEnergy I.val = doubledEnergy J.val
  · have hgrade : energy I = energy J := congrArg Nat.cast hij
    have hdegree : 2 * (d : ℤ) + 2 = (doubledEnergy A.val : ℤ) + doubledEnergy B.val := by
      simp only [sourceEnergy_sort] at hd
      omega
    have readout := shifted_supercommutator_readout energy aMat bMat
      (doubledEnergy A.val) (doubledEnergy B.val) s
      ((-1 : R) ^ (A.val.sort.length * B.val.sort.length)) d hdegree I J hgrade
    rw [hA, hB] at readout
    have hidx : 2 * (-s - 1) = -2 * s - 2 := by ring
    have hres := shifted_weighted_matrix_residue_all R L K A B I J d hd hij
      (by omega) (-s - 1) (hidx ▸ hs)
    rw [hidx] at hres
    apply readout.symm.trans
    simpa only [Units.smul_def, zsmul_eq_mul, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one, Int.cast_pow, Int.cast_neg, Int.cast_one] using hres
  · have hne : I ≠ J := fun e => hij (congrArg (fun x : Index L => doubledEnergy x.val) e)
    have hgrade : energy I ≠ energy J := by dsimp [energy]; omega
    simp only [hne, ↓reduceIte, zero_mul]
    apply Finset.sum_eq_zero
    intro a _
    let q : ℤ := 2 * s + (doubledEnergy B.val : ℤ) - 2 * (a : ℕ)
    have hforward := opposite_modes_off_energy energy aMat bMat (-q) I J hgrade
    have hreverse := opposite_modes_off_energy energy bMat aMat q I J hgrade
    rw [neg_neg] at hforward
    change _ * ((energyMode energy aMat (-q) * energyMode energy bMat q) I J -
      _ * (energyMode energy bMat q * energyMode energy aMat (-q)) I J) = _
    rw [hforward, hreverse, mul_zero, sub_zero, mul_zero]

end Crossing

end VPVNP
end Computability
end OAI
