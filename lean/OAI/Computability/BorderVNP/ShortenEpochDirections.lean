import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

/-!
# Perpendicular directions in a shortening epoch

The signed coordinate permutations on pages 18–19 of the border-circuit paper act on
the product of real tangent planes indexed by the Boolean cube. The argument works for
any real inner-product space in place of a tangent plane.
-/

namespace OAI
namespace Computability
namespace BorderVNP

noncomputable section

namespace Epoch

/-- Addresses of the `2^D` factors. -/
abbrev Cube (D : ℕ) := Fin D → Bool

/-- Flip one bit of a factor address. -/
def flip {D : ℕ} (i : Fin D) (x : Cube D) : Cube D :=
  fun k => if k = i then !(x k) else x k

@[simp] private theorem flip_twice {D : ℕ} (i : Fin D) (x : Cube D) :
    flip i (flip i x) = x := by
  funext k
  by_cases h : k = i <;> simp [flip, h]

private theorem flip_comm {D : ℕ} (i j : Fin D) (x : Cube D) :
    flip j (flip i x) = flip i (flip j x) := by
  funext k
  simp only [flip]
  split_ifs <;> rfl

private def flipEquiv {D : ℕ} (i : Fin D) : Equiv.Perm (Cube D) where
  toFun := flip i
  invFun := flip i
  left_inv := flip_twice i
  right_inv := flip_twice i

private def bitSign (b : Bool) : ℝ := if b then -1 else 1

/-- The sign is negative precisely when an odd number of earlier bits are set. -/
def prefixSign {D : ℕ} (j : Fin D) (x : Cube D) : ℝ :=
  ∏ k ∈ Finset.Iio j, bitSign (x k)

/-- The accumulated sign squares to one in every component. -/
theorem prefixSign_sq {D : ℕ} (j : Fin D) (x : Cube D) :
    prefixSign j x * prefixSign j x = 1 := by
  unfold prefixSign
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro k _
  cases x k <;> simp [bitSign]

private theorem prefixSign_flip {D : ℕ} (i j : Fin D) (x : Cube D) :
    prefixSign j (flip i x) = (if i < j then -1 else 1) * prefixSign j x := by
  unfold prefixSign
  calc
    _ = ∏ k ∈ Finset.Iio j, ((if k = i then -1 else 1) * bitSign (x k)) := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases h : k = i
      · subst k
        cases hb : x i <;> simp [flip, bitSign, hb]
      · simp [flip, h]
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']; simp

/-- The Euclidean product of all factor spaces. Each factor is a tangent plane in Lemma 6.1. -/
abbrev Direction (D : ℕ) (E : Type*) := PiLp 2 fun _ : Cube D => E

variable {D : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The signed permutation `Aᵢ` flips factor bit `i` and multiplies the entire component
by the parity sign of the preceding bits. -/
def signedFlip (i : Fin D) : Direction D E →ₗ[ℝ] Direction D E where
  toFun u := WithLp.toLp 2 fun x => prefixSign i x • u (flip i x)
  map_add' u v := by ext x; simp [smul_add]
  map_smul' r u := by
    ext x
    change prefixSign i x • (r • u (flip i x)) = r • (prefixSign i x • u (flip i x))
    exact smul_comm _ _ _

private theorem signedFlip_apply (i : Fin D) (u : Direction D E) (x : Cube D) :
    signedFlip i u x = prefixSign i x • u (flip i x) := rfl

/-- Each signed coordinate permutation is an involution. -/
theorem signedFlip_involutive (i : Fin D) :
    Function.Involutive (signedFlip i (E := E)) := by
  intro u
  ext x
  simp [signedFlip_apply, prefixSign_flip, smul_smul, prefixSign_sq]

/-- Flipping a bit is self-adjoint for the real product inner product. -/
theorem signedFlip_symmetric (i : Fin D) (u v : Direction D E) :
    inner ℝ (signedFlip i u) v = inner ℝ u (signedFlip i v) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [signedFlip_apply, real_inner_smul_left, real_inner_smul_right]
  let f := fun x : Cube D => prefixSign i x * inner ℝ (u x) (v (flip i x))
  calc
    _ = ∑ x, f (flipEquiv i x) := by
      apply Finset.sum_congr rfl
      intro x _
      simp [f, flipEquiv, prefixSign_flip]
    _ = _ := Equiv.sum_comp (flipEquiv i) f

/-- Distinct signed flips anticommute. The minus sign arises exactly once,
from the smaller index occurring in the larger index's sign prefix. -/
theorem signedFlip_anticommute {i j : Fin D} (h : i ≠ j) (u : Direction D E) :
    signedFlip i (signedFlip j u) = -signedFlip j (signedFlip i u) := by
  ext x
  simp only [signedFlip_apply, PiLp.neg_apply, prefixSign_flip, smul_smul, flip_comm i j x]
  rcases lt_or_gt_of_ne h with hlt | hgt
  · simp [hlt, not_lt_of_gt hlt, mul_comm]
  · simp [hgt, not_lt_of_gt hgt, mul_comm]

/-- The images of every direction under distinct signed flips are perpendicular. -/
theorem signedFlip_orthogonal {i j : Fin D} (h : i ≠ j) (u : Direction D E) :
    inner ℝ (signedFlip i u) (signedFlip j u) = 0 := by
  have hneg : inner ℝ (signedFlip i u) (signedFlip j u) =
      -inner ℝ (signedFlip i u) (signedFlip j u) := by
    calc
      _ = inner ℝ u (signedFlip i (signedFlip j u)) := signedFlip_symmetric i _ _
      _ = -inner ℝ u (signedFlip j (signedFlip i u)) := by
        rw [signedFlip_anticommute h, inner_neg_right]
      _ = -inner ℝ (signedFlip j u) (signedFlip i u) := by rw [signedFlip_symmetric]
      _ = _ := congrArg Neg.neg (real_inner_comm _ _)
  linarith

/-- A single unit direction supplies all `D` orthonormal directions for the crossing. -/
theorem signedFlip_orthonormal (u : Direction D E) (hu : ‖u‖ = 1) :
    Orthonormal ℝ (fun i : Fin D => signedFlip i u) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases h : i = j
  · subst j
    rw [ite_eq_left rfl, signedFlip_symmetric, signedFlip_involutive i u, real_inner_self_eq_norm_sq, hu]
    norm_num
  · simpa [h] using signedFlip_orthogonal h u

end Epoch

end

end BorderVNP
end Computability
end OAI
