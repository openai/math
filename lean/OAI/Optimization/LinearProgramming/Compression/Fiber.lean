import OAI.Optimization.LinearProgramming.Compression.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Rat.Cast.CharZero

/-! Fixing some generator coordinates adds only signed unit rows to the clipping
polyhedron. This separates the coefficient bound from the number of minor comparisons. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators Matrix

variable {ι σ κ : Type*} {K : Type*} [Field K]
  [DecidableEq κ]

/-- Append `y (anchor j) ≤ x j` and `-y (anchor j) ≤ -x j` for every fixed coordinate. -/
def fiberRows (A : Matrix ι κ K) (anchor : σ → κ) : Matrix (ι ⊕ (σ × Bool)) κ K :=
  Matrix.of fun t i => t.elim (fun u => A u i) (fun jb =>
    if i = anchor jb.1 then if jb.2 then 1 else -1 else 0)

def fiberRhs (b : ι → K) (x : σ → K) : (ι ⊕ (σ × Bool)) → K :=
  Sum.elim b (fun jb => if jb.2 then x jb.1 else -x jb.1)

theorem fiberRows_mulVec_inr [Fintype κ] (A : Matrix ι κ K) (anchor : σ → κ) (y : κ → K) (j : σ)
    (s : Bool) : (fiberRows A anchor *ᵥ y) (.inr (j,s)) = if s then y (anchor j) else -y (anchor j) := by
  cases s <;> simp [fiberRows, Matrix.mulVec, dotProduct, ite_mul]

theorem fiberRows_mulVec_le_iff [LinearOrder K] [IsStrictOrderedRing K] [Fintype κ] (A : Matrix ι κ K) (b : ι → K) (anchor : σ → κ)
    (x : σ → K) (y : κ → K) : fiberRows A anchor *ᵥ y ≤ fiberRhs b x ↔
      A *ᵥ y ≤ b ∧ ∀ j, y (anchor j) = x j := by
  constructor
  · intro h
    refine ⟨fun u => h (.inl u), fun j => ?_⟩
    have h₁ := h (.inr (j,true))
    have h₂ := h (.inr (j,false))
    simp [fiberRows_mulVec_inr, fiberRhs] at h₁ h₂
    exact le_antisymm h₁ h₂
  · rintro ⟨h, hy⟩ (u | ⟨j,s⟩)
    · exact h u
    · simp only [fiberRows_mulVec_inr, fiberRhs, Sum.elim_inr, hy, le_refl]

theorem fiberRows_cast_real (A : Matrix ι κ ℚ) (anchor : σ → κ) :
    (fiberRows A anchor).map (Rat.cast : ℚ → ℝ) =
      fiberRows (A.map (Rat.cast : ℚ → ℝ)) anchor := by
  ext r i
  cases r with
  | inl r => rfl
  | inr js =>
    rcases js with ⟨j,s⟩
    cases s <;> by_cases h : i = anchor j <;> simp [Matrix.map, fiberRows, h]

theorem fiberRhs_cast_real (b : ι → ℚ) (x : σ → ℚ) (r : ι ⊕ (σ × Bool)) :
    ((fiberRhs b x r : ℚ) : ℝ) = fiberRhs (fun i => (b i : ℝ)) (fun j => (x j : ℝ)) r := by
  cases r with
  | inl r => rfl
  | inr js =>
    rcases js with ⟨j,s⟩
    cases s <;> simp [fiberRhs]

theorem fiberRows_height (A : Matrix ι κ ℚ) (anchor : σ → κ) {H : ℕ} (hH : 0 < H)
    (hA : ∀ i j, (A i j).num.natAbs ≤ H ∧ (A i j).den ≤ H) (t : ι ⊕ (σ × Bool)) (i : κ) :
    (fiberRows A anchor t i).num.natAbs ≤ H ∧ (fiberRows A anchor t i).den ≤ H := by
  cases t with
  | inl r => exact hA r i
  | inr js =>
    rcases js with ⟨j,s⟩
    cases s <;> by_cases h : i = anchor j <;> simp [fiberRows, h] <;> omega

theorem fiberRhs_height (b : ι → ℚ) (x : σ → ℚ) {H : ℕ}
    (hb : ∀ i, (b i).num.natAbs ≤ H ∧ (b i).den ≤ H)
    (hx : ∀ j, (x j).num.natAbs ≤ H ∧ (x j).den ≤ H) (t : ι ⊕ (σ × Bool)) :
    (fiberRhs b x t).num.natAbs ≤ H ∧ (fiberRhs b x t).den ≤ H := by
  cases t with
  | inl r => exact hb r
  | inr js =>
    rcases js with ⟨j,s⟩
    cases s <;> simpa [fiberRhs] using hx j

/-- Coefficients of the fixed coordinates when the augmented system is written as
`H y ≤ c - G x`. Their magnitudes are at most one. -/
def fiberParameter {K : Type*} [Ring K] [DecidableEq σ] :
    Matrix (ι ⊕ (σ × Bool)) σ K :=
  Matrix.of fun t j => t.elim (fun _ => 0) (fun js =>
    if j = js.1 then if js.2 then -1 else 1 else 0)

def fiberConstant (b : ι → K) : (ι ⊕ (σ × Bool)) → K :=
  Sum.elim b (fun _ => 0)

theorem fiberConstant_sub_mulVec [Fintype σ] [DecidableEq σ] (b : ι → K) (x : σ → K) :
    fiberConstant b - fiberParameter *ᵥ x = fiberRhs b x := by
  funext r
  cases r with
  | inl r => simp [fiberConstant, fiberRhs, fiberParameter, Matrix.mulVec, dotProduct]
  | inr js =>
    obtain ⟨j,s⟩ := js
    cases s <;> simp [fiberConstant, fiberRhs, fiberParameter, Matrix.mulVec, dotProduct, ite_mul]

theorem fiberParameter_cast_real [DecidableEq σ] :
    (fiberParameter (ι := ι) (σ := σ) (K := ℚ)).map (Rat.cast : ℚ → ℝ) = fiberParameter := by
  ext r i
  cases r with
  | inl r => simp [fiberParameter, Matrix.map]
  | inr js =>
    obtain ⟨j,s⟩ := js
    cases s <;> by_cases h : i = j <;> simp [Matrix.map, fiberParameter, h]

theorem fiberParameter_height [DecidableEq σ] (r : ι ⊕ (σ × Bool)) (i : σ) :
    (fiberParameter (K := ℚ) r i).num.natAbs ≤ 1 ∧ (fiberParameter (K := ℚ) r i).den ≤ 1 := by
  cases r with
  | inl r => simp [fiberParameter]
  | inr js =>
    obtain ⟨j,s⟩ := js
    cases s <;> by_cases h : i = j <;> simp [fiberParameter, h]

end Compression
end LinearProgramming
end Optimization
end OAI
