import OAI.Optimization.LinearProgramming.Farkas.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

/-! The marked-coordinate subspace alternative and the slack-space encoding in §2. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Farkas

open Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Exactly one of a subspace and its dot-product orthogonal has a nonnegative
vector strictly positive at a prescribed coordinate. -/
theorem subspace_coordinate_alternative {n : ℕ} (W : Submodule K (Fin n → K)) (i : Fin n) :
    (∃ x ∈ W, 0 ≤ x ∧ 0 < x i) ↔
      ¬ ∃ y ∈ W.orthogonalBilin (dotProductBilin K K), 0 ≤ y ∧ 0 < y i := by
  constructor
  · rintro ⟨x, hx, hx₀, hxi⟩ ⟨y, hy, hy₀, hyi⟩
    have hxy : 0 < x ⬝ᵥ y := Finset.sum_pos' (fun j _ => mul_nonneg (hx₀ j) (hy₀ j))
      ⟨i, Finset.mem_univ _, mul_pos hxi hyi⟩
    exact hxy.ne' (hy x hx)
  · intro hno
    let e := (Module.finBasis K W).equivFun
    let f := W.subtype.comp e.symm.toLinearMap
    let M := LinearMap.toMatrix' f
    let u : Fin n → K := Pi.single i 1
    rcases alternative (Module.finrank K W) (Fin n) (-M) (-u) with ⟨z, hz⟩ | ⟨y, hy, hM, hu⟩
    · have hdom : u ≤ M *ᵥ z := fun j => by
        simpa only [Matrix.neg_mulVec, Pi.neg_apply, neg_le_neg_iff] using hz j
      have hm : M *ᵥ z ∈ W := by rw [LinearMap.toMatrix'_mulVec]; exact (e.symm z).property
      have hu₀ : 0 ≤ u := Pi.single_nonneg.mpr zero_le_one
      have hui : (1 : K) ≤ (M *ᵥ z) i := by simpa [u] using hdom i
      exact ⟨_, hm, hu₀.trans hdom, zero_lt_one.trans_le hui⟩
    · apply False.elim ∘ hno
      have hM₀ : M.transpose *ᵥ y = 0 := by simpa [Matrix.neg_mulVec] using hM
      have hyi : 0 < y i := by simpa [u] using hu
      refine ⟨y, ?_, hy, hyi⟩
      intro x hx
      change x ⬝ᵥ y = 0
      have heq : M *ᵥ e ⟨x, hx⟩ = x := by simp [M, f]
      rw [← heq, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM₀,
        zero_dotProduct]

variable {m d : ℕ}

/-- Homogeneous slack parametrization `(β,u) ↦ (β, β b - A u)`. -/
def slackMap (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) :
    (K × (Fin d → K)) →ₗ[K] (Fin (m+1) → K) where
  toFun z := Fin.cons z.1 (z.1 • b - A *ᵥ z.2)
  map_add' z w := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [Matrix.mulVec_add, add_smul]
      ring
  map_smul' r z := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [Matrix.mulVec_smul, mul_sub, mul_assoc]

/-- A marked nonnegative slack vector is equivalent to a feasible point over the same field. -/
theorem slack_primal_iff (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) :
    (∃ w ∈ LinearMap.range (slackMap A b), 0 ≤ w ∧ 0 < w 0) ↔ ∃ x, A *ᵥ x ≤ b := by
  constructor
  · rintro ⟨_, ⟨⟨β, u⟩, rfl⟩, hn, hp⟩
    change 0 < β at hp
    refine ⟨β⁻¹ • u, fun i => ?_⟩
    rw [Matrix.mulVec_smul]
    change β⁻¹ * (A *ᵥ u) i ≤ b i
    have hi : 0 ≤ β * b i - (A *ᵥ u) i := hn i.succ
    simpa only [div_eq_inv_mul] using (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using sub_nonneg.mp hi)
  · rintro ⟨x, hx⟩
    refine ⟨slackMap A b (1, x), ⟨_, rfl⟩, fun i => ?_, zero_lt_one⟩
    refine Fin.cases zero_le_one (fun j => ?_) i
    change 0 ≤ 1 * b j - (A *ᵥ x) j
    simpa only [one_mul, sub_nonneg] using hx j

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The dot product with an arbitrary homogeneous slack vector. -/
private theorem slack_pairing (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (β q : K)
    (u : Fin d → K) (y : Fin m → K) :
    slackMap A b (β, u) ⬝ᵥ Fin.cons q y = β * (q + b ⬝ᵥ y) - (A.transpose *ᵥ y) ⬝ᵥ u := by
  change (Fin.cons β (β • b - A *ᵥ u) : Fin (m+1) → K) ⬝ᵥ Fin.cons q y = _
  rw [show (Fin.cons β (β • b - A *ᵥ u) : Fin (m+1) → K) ⬝ᵥ Fin.cons q y =
      β * q + (β • b - A *ᵥ u) ⬝ᵥ y from Fin.sum_univ_succ _]
  rw [sub_dotProduct, smul_dotProduct, dotProduct_comm (A *ᵥ u), Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, smul_eq_mul]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Orthogonality to every slack vector is equivalent to the two Farkas equations. -/
theorem slack_orthogonal_iff (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) (q : K)
    (y : Fin m → K) :
    (Fin.cons q y : Fin (m+1) → K) ∈ (LinearMap.range (slackMap A b)).orthogonalBilin
        (dotProductBilin K K) ↔ A.transpose *ᵥ y = 0 ∧ b ⬝ᵥ y = -q := by
  constructor
  · intro h
    have hh (β : K) (u : Fin d → K) : β * (q + b ⬝ᵥ y) - (A.transpose *ᵥ y) ⬝ᵥ u = 0 :=
      (slack_pairing A b β q u y).symm.trans (h _ ⟨(β, u), rfl⟩)
    refine ⟨dotProduct_eq_zero _ (fun u => ?_), ?_⟩
    · simpa using hh 0 u
    · have hsum : q + b ⬝ᵥ y = 0 := by simpa using hh 1 0
      exact eq_neg_of_add_eq_zero_right hsum
  · rintro ⟨hne, heq⟩ _ ⟨⟨β,u⟩, rfl⟩
    change slackMap A b (β,u) ⬝ᵥ Fin.cons q y = 0
    simp [slack_pairing, hne, heq]

/-- A dual slack witness gives exactly a Farkas certificate with a negative right-hand side. -/
theorem slack_dual_iff (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) :
    (∃ w ∈ (LinearMap.range (slackMap A b)).orthogonalBilin (dotProductBilin K K),
      0 ≤ w ∧ 0 < w 0) ↔ ∃ y : Fin m → K, 0 ≤ y ∧ A.transpose *ᵥ y = 0 ∧ b ⬝ᵥ y < 0 := by
  constructor
  · rintro ⟨w, hw, hn, hp⟩
    have ho := (slack_orthogonal_iff A b (w 0) (Fin.tail w)).mp (by simpa using hw)
    exact ⟨Fin.tail w, fun i => hn i.succ, ho.1, ho.2.trans_lt (neg_neg_of_pos hp)⟩
  · rintro ⟨y, hn, hA, hneg⟩
    refine ⟨Fin.cons (-(b ⬝ᵥ y)) y, (slack_orthogonal_iff _ _ _ _).mpr ⟨hA, by simp⟩,
      fun i => ?_, neg_pos.mpr hneg⟩
    exact Fin.cases (neg_pos.mpr hneg).le hn i

end Farkas
end LinearProgramming
end Optimization
end OAI
