import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-! # Scaled residues of mixed-radix addresses

Axis zero varies fastest. The scaled Chinese remainder isomorphism is additive, and its
coordinate of a mixed-radix rank is the original digit translated by a function of
strictly earlier digits. Composite, pairwise coprime radices are allowed.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRT

open Finset
variable {d : ℕ}

/-- Place value for the digit on axis `i`. -/
def «prefix» (a : Fin d → ℕ) (i : Fin d) : ℕ := ∏ j ∈ Iio i, a j

/-- Mixed-radix rank. This is also defined for unbounded digits. -/
def rank (a t : Fin d → ℕ) : ℕ := ∑ i, «prefix» a i * t i

/-- Scale the residue modulo each radix by the inverse of its place value. -/
def weight (a : Fin d → ℕ) (i : Fin d) : ZMod (a i) := («prefix» a i : ZMod (a i))⁻¹

variable (a : Fin d → ℕ) (h : Pairwise (fun i j => (a i).Coprime (a j)))

include h in
theorem prefix_coprime (i : Fin d) : («prefix» a i).Coprime (a i) :=
  Nat.Coprime.prod_left fun _ hj => h (Finset.mem_Iio.mp hj).ne

include h in
theorem prefix_mul_weight (i : Fin d) : («prefix» a i : ZMod (a i)) * weight a i = 1 :=
  ZMod.coe_mul_inv_eq_one _ (prefix_coprime a h i)

include h in
theorem weight_mul_prefix (i : Fin d) : weight a i * («prefix» a i : ZMod (a i)) = 1 := by
  rw [mul_comm, prefix_mul_weight a h]

include h in
private def scaleAxis (i : Fin d) : ZMod (a i) ≃+ ZMod (a i) where
  toFun x := weight a i * x
  invFun x := («prefix» a i : ZMod (a i)) * x
  left_inv x := by dsimp only; rw [← mul_assoc, prefix_mul_weight a h, one_mul]
  right_inv x := by dsimp only; rw [← mul_assoc, weight_mul_prefix a h, one_mul]
  map_add' _ _ := mul_add _ _ _

/-- The scaled CRT coordinate map, as an additive equivalence of cyclic convolution groups. -/
noncomputable def scaled : ZMod (∏ i, a i) ≃+ (∀ i, ZMod (a i)) :=
  (ZMod.prodEquivPi a h).toAddEquiv.trans (AddEquiv.piCongrRight (scaleAxis a h))

theorem scaled_apply (x : ZMod (∏ i, a i)) (i : Fin d) :
    scaled a h x i = weight a i * ZMod.castHom (dvd_prod_of_mem a (mem_univ i)) _ x := by
  change weight a i * (ZMod.prodEquivPi a h x i) = _
  rw [ZMod.prodEquivPi_apply]

@[simp] theorem scaled_natCast (r : ℕ) (i : Fin d) :
    scaled a h (r : ZMod (∏ j, a j)) i = weight a i * (r : ZMod (a i)) := by
  rw [scaled_apply, map_natCast]

/-- Adding a more significant digit contributes a multiple of every earlier axis length. -/
theorem dvd_prefix {i j : Fin d} (hij : i < j) : a i ∣ «prefix» a j :=
  dvd_prod_of_mem _ (mem_Iio.mpr hij)

/-- Triangular formula `yᵢ = tᵢ + μᵢ ∑_{j<i} Pⱼ tⱼ` on every address. -/
theorem scaled_rank (t : Fin d → ℕ) (i : Fin d) :
    scaled a h (rank a t : ZMod (∏ j, a j)) i =
      (t i : ZMod (a i)) + weight a i * ((∑ j ∈ Iio i, «prefix» a j * t j : ℕ) : ZMod (a i)) := by
  rw [scaled_natCast]
  unfold rank
  push_cast
  have hrestrict : (∑ j, («prefix» a j : ZMod (a i)) * (t j : ZMod (a i))) =
      ∑ j ∈ insert i (Iio i), («prefix» a j : ZMod (a i)) * (t j : ZMod (a i)) := by
    symm
    apply sum_subset (subset_univ _)
    intro j _ hj
    have hij : i < j := by
      simp only [mem_insert, mem_Iio, not_or] at hj
      exact lt_of_le_of_ne (le_of_not_gt hj.2) (Ne.symm hj.1)
    rw [(ZMod.natCast_eq_zero_iff ..).mpr (dvd_prefix a hij), zero_mul]
  rw [hrestrict, sum_insert (by simp), mul_add, ← mul_assoc, weight_mul_prefix a h, one_mul]

/-- Mathlib's tuple-to-address encoding orders axes by these very place values. -/
theorem rank_eq_finPiFinEquiv (t : ∀ i, Fin (a i)) :
    rank a (fun i => t i) = (finPiFinEquiv t : ℕ) := by
  rw [rank, finPiFinEquiv_apply]
  apply sum_congr rfl
  intro i _
  rw [mul_comm]
  congr 1
  exact prod_bij' (fun (j : Fin d) hj => (⟨j.val, show j < i from mem_Iio.mp hj⟩ : Fin i.val))
    (fun j _ => Fin.castLE i.isLt.le j)
    (fun _ _ => mem_univ _) (fun j _ => mem_Iio.mpr j.isLt)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem rank_lt (t : ∀ i, Fin (a i)) :
    rank a (fun i => t i) < ∏ i, a i := by
  rw [rank_eq_finPiFinEquiv]
  exact (finPiFinEquiv t).isLt

private theorem finEquiv_eq_cast {n : ℕ} [NeZero n] (x : Fin n) :
    ZMod.finEquiv n x = (x.val : ZMod n) := by
  cases n with
  | zero => exact Fin.elim0 x
  | succ n =>
    apply Fin.ext
    change x.val = (x.val % (n + 1))
    exact (Nat.mod_eq_of_lt x.isLt).symm

/-- The permutation taking the valid digit tuple of a mixed-radix rank to its scaled
residue coordinates. This is an equivalence even when some axes have length one. -/
noncomputable def address (ha : ∀ i, a i ≠ 0) :
    (∀ i, Fin (a i)) ≃ (∀ i, ZMod (a i)) := by
  letI : NeZero (∏ i, a i) := ⟨prod_ne_zero_iff.mpr fun i _ => ha i⟩
  exact finPiFinEquiv |>.trans (ZMod.finEquiv _).toEquiv |>.trans (scaled a h).toEquiv

theorem address_apply (ha : ∀ i, a i ≠ 0) (t : ∀ i, Fin (a i)) :
    address a h ha t = scaled a h (rank a (fun i => t i)) := by
  let : NeZero (∏ i, a i) := ⟨prod_ne_zero_iff.mpr fun i _ => ha i⟩
  change scaled a h (ZMod.finEquiv _ (finPiFinEquiv t)) = _
  rw [finEquiv_eq_cast, rank_eq_finPiFinEquiv]

theorem address_coordinate (ha : ∀ i, a i ≠ 0) (t : ∀ i, Fin (a i)) (i : Fin d) :
    address a h ha t i = ((t i).val : ZMod (a i)) +
      weight a i * ((∑ j ∈ Iio i, «prefix» a j * (t j).val : ℕ) : ZMod (a i)) := by
  rw [address_apply, scaled_rank]

end CRT

end NearSquareRoot
end Computability
end OAI
