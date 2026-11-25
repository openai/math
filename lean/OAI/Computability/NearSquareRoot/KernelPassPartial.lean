import OAI.Computability.NearSquareRoot.KernelPassFactors
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Partial normalized Walsh transforms in fixed linear coordinates

Both end charts may choose any binary bases of the full address. The active
coordinate block costs one child per axis. The residual block is copied through
the transform. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

open Matrix Finset SynchronizedPadding SynchronizedPair KernelNormalization
open scoped BigOperators

noncomputable section

variable {A k : ℕ}

/-- The normalized two-point Walsh matrix on binary digits. -/
abbrev bitWalsh : Matrix (ZMod 2) (ZMod 2) ℂ := walsh

private def singleStage (a b : Fin A) : Matrix (ZMod 2) (ZMod 2) ℂ :=
  if b = a then bitWalsh else 1

private theorem tensor_singleStage (a : Fin A) :
    tensorMatrix (singleStage a) = childLocal a := by
  ext y x
  change (∏ b, singleStage a b (y b) (x b)) = _
  unfold childLocal
  split_ifs with h
  · rw [prod_eq_single a]
    · simp [singleStage]
    · intro b _ hb
      simp [singleStage, hb, Matrix.one_apply, h b hb]
    · simp
  · push Not at h
    obtain ⟨b,hb,hn⟩ := h
    exact prod_eq_zero (mem_univ b) (by simp [singleStage, hb, hn.symm])

/-- Single-column matrix of the program on any list of distinct axes. -/
theorem partial_tensor (axes : List (Fin A)) (h : axes.Nodup) :
    partialLocal axes = tensorMatrix (fun b => if b ∈ axes then bitWalsh else 1) := by
  induction axes with
  | nil => simp [partialLocal]
  | cons a axes ih =>
    obtain ⟨ha,ht⟩ := List.nodup_cons.mp h
    change childLocal a * partialLocal axes = _
    rw [← tensor_singleStage, ih ht, ← tensorMatrix_mul]
    congr 1
    funext b
    by_cases eq : b = a
    · subst b; simp [singleStage,ha]
    · simp [singleStage,eq]

/-- Change both physical address charts by applying binary linear
permutations before and after a realized matrix. -/
theorem Realizes.submatrix {n : ℕ} {M : Local A} (hM : Realizes n M)
    (ey ex : Bits A ≃ₗ[ZMod 2] Bits A) :
    Realizes n (M.submatrix ey ex) := by
  have h := ((Realizes.permutation ey.symm).mul hM).mul (Realizes.permutation ex)
  simp only [zero_add,add_zero] at h
  have e : pushAddress (⇑ey.symm) * M * pushAddress (⇑ex) = M.submatrix ey ex := by
    ext y x
    simp only [Matrix.mul_apply, pushAddress, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ite_mul, one_mul, zero_mul,
      Matrix.submatrix_apply]
    simp [eq_comm, LinearEquiv.eq_symm_apply]
  rwa [e] at h

/-- Split an address into a prefix and the remaining coordinates. -/
def splitBits (k r : ℕ) : Bits (k + r) ≃ₗ[ZMod 2] Bits k × Bits r where
  toFun x := (fun i => x (Fin.castAdd r i), fun j => x (Fin.natAdd k j))
  invFun x := Fin.append x.1 x.2
  left_inv x := by ext i; exact Fin.addCases (by simp) (by simp) i
  right_inv x := by ext <;> simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {R : Type*} [AddCommGroup R] [Module (ZMod 2) R]

/-- Normalized Walsh on the first block and equality on the residual block.
Input and output charts may differ. -/
def partialChart (ey ex : Bits A ≃ₗ[ZMod 2] Bits k × R) : Local A := by
  classical
  exact fun y x => if (ey y).2 = (ex x).2 then
    (w : ℂ)^k * character ((ey y).1 ⬝ᵥ (ex x).1) else 0

private theorem split_realizes (k r : ℕ) :
    Realizes k (partialChart (splitBits k r) (splitBits k r)) := by
  let axes := (List.finRange k).map (Fin.castAdd r)
  have nodup : axes.Nodup := (List.nodup_finRange k).map (Fin.castAdd_injective _ _)
  have h := Realizes.partial axes
  have length : axes.length = k := by simp [axes]
  rw [length, partial_tensor axes nodup] at h
  suffices eq : tensorMatrix (fun b => if b ∈ axes then bitWalsh else 1) =
      partialChart (splitBits k r) (splitBits k r) by rwa [eq] at h
  ext y x
  change (∏ b, (if b ∈ axes then bitWalsh else 1) (y b) (x b)) = _
  rw [Fin.prod_univ_add]
  have hl (b : Fin k) : Fin.castAdd r b ∈ axes := by simp [axes]
  have hr (b : Fin r) : Fin.natAdd k b ∉ axes := by
    simp only [axes,List.mem_map,List.mem_finRange,true_and,not_exists]
    intro i he
    have := congrArg Fin.val he
    simp at this
    omega
  simp only [hl, hr, ↓reduceIte]
  let e := splitBits k r
  have ha : (∏ i : Fin k, walsh (y (Fin.castAdd r i)) (x (Fin.castAdd r i))) =
      (w : ℂ)^k * character ((e y).1 ⬝ᵥ (e x).1) := axis_character _ _
  rw [ha]
  unfold partialChart
  by_cases he : (e y).2 = (e x).2
  · have hc (i : Fin r) : y (Fin.natAdd k i) = x (Fin.natAdd k i) := congrFun he i
    simp [e] at he
    simp [he,hc,e, Matrix.one_apply]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp he
    change y (Fin.natAdd k i) ≠ x (Fin.natAdd k i) at hi
    have hz : (∏ j : Fin r, (1 : Matrix (ZMod 2) (ZMod 2) ℂ)
        (y (Fin.natAdd k j)) (x (Fin.natAdd k j))) = 0 :=
      prod_eq_zero (mem_univ i) (Matrix.one_apply_ne hi)
    change ¬(splitBits k r y).2 = (splitBits k r x).2 at he
    simp only [hz, mul_zero, he, ↓reduceIte]

/-- Arbitrary invertible charts on the source and destination preserve the
child budget of a partial normalized Walsh transform. -/
theorem Realizes.partialChart [FiniteDimensional (ZMod 2) R]
    (ey ex : Bits A ≃ₗ[ZMod 2] Bits k × R) :
    Realizes k (KernelPass.partialChart ey ex) := by
  classical
  let r := Module.finrank (ZMod 2) R
  have hdim : A = k+r := by simpa [r, Module.finrank_prod] using ey.finrank_eq
  subst A
  let b := (Module.finBasis (ZMod 2) R).equivFun
  let l := (LinearEquiv.refl (ZMod 2) (Bits k)).prodCongr b
  let cy := (ey.trans l).trans (splitBits k r).symm
  let cx := (ex.trans l).trans (splitBits k r).symm
  have h := (split_realizes k r).submatrix cy cx
  convert h using 1
  ext y x
  have fy : splitBits k r (cy y) = ((ey y).1,b (ey y).2) :=
    (splitBits k r).apply_symm_apply _
  have fx : splitBits k r (cx x) = ((ex x).1,b (ex x).2) :=
    (splitBits k r).apply_symm_apply _
  simp only [KernelPass.partialChart, Matrix.submatrix_apply]
  split_ifs with hy hx hx
  · rw [fy,fx]
  · exact (hx (by rw [fy,fx]; exact congrArg b hy)).elim
  · rw [fy,fx] at hx
    exact (hy (b.injective hx)).elim
  · rfl

end
end KernelPass

end NearSquareRoot
end Computability
end OAI
