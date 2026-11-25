import OAI.LinearAlgebra.MatrixExponent.Rectangle.Rows
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Discrete weighted growth of three polynomial prices

Move the three widths from `n(A,B,C)` to `(n+1)(A,B,C)`. For each
pair of widths use both orders of the two increments. Their sum
allows the paired row estimates to be applied at each unchanged
width, both before and after the change. The harmonic lower bound
on the increments telescopes against a difference of logarithms.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter

variable {P Q R : ℕ → ℕ → ℝ} {x y z : ℝ}

/-- Paired growth for the logs of two prices with the same first input. -/
def Increments (P Q : ℕ → ℕ → ℝ) (d : ℝ) : Prop :=
  ∀ m j k b c : ℕ, 0 < b → 0 < c →
    4 * d * b * c / (m + (j + b) + (k + c) + 2 : ℕ) ≤
      (P m (j + b) - P m j) * c + (Q m (k + c) - Q m k) * b

theorem increments_of_rows (hx : 0 < x)
    (hp : ∀ m n, 0 < P m n) (hq : ∀ m n, 0 < Q m n)
    (h₁ : ∀ m, Row (fun n => (P m n) ^ (1 / x)) (fun n => (Q m n) ^ (1 / x)) m)
    (h₂ : ∀ m, Row (fun n => (Q m n) ^ (1 / x)) (fun n => (P m n) ^ (1 / x)) m) :
    Increments (fun m n => Real.log (P m n)) (fun m n => Real.log (Q m n)) x := by
  intro m j k b c hb hc
  have h := paired_secants (h₁ m) (h₂ m) j k b c hb hc
  simp only [Real.log_rpow (hp _ _), Real.log_rpow (hq _ _)] at h
  dsimp only
  field_simp at h ⊢
  linarith only [h]

private theorem Increments.step (hp : Increments P Q x) (hx : 0 ≤ x)
    {A B C n m : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hm : m ≤ (n + 1) * A) :
    4 * x * B * C / (((n : ℝ) + 3) * (A + B + C)) ≤
      (P m ((n + 1) * B) - P m (n * B)) * C + (Q m ((n + 1) * C) - Q m (n * C)) * B := by
  have he := hp m (n * B) (n * C) B C hB hC
  simp only [← Nat.succ_mul] at he
  apply le_trans _ he
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  push_cast
  have hm' : (m : ℝ) ≤ (n + 1) * A := by exact_mod_cast hm
  have hA' : 1 ≤ (A : ℝ) := by exact_mod_cast hA
  linarith

/-- If a potential grows by at least `v/(n+3)` at every step and is
at most `w log(n+3)+C`, then `v ≤ w`. -/
private theorem growth {f : ℕ → ℝ} {v w C : ℝ} (hv : 0 ≤ v)
    (hl : ∀ n : ℕ, v / ((n : ℝ) + 3) ≤ f (n + 1) - f n)
    (hu : ∀ n, f n ≤ w * Real.log ((n : ℝ) + 3) + C) : v ≤ w := by
  have hb (n : ℕ) : f 0 + v * (Real.log ((n : ℝ) + 3) - Real.log 3) ≤ f n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h : Real.log ((n : ℝ) + 4) - Real.log (n + 3) ≤ 1 / ((n : ℝ) + 3) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        refine (Real.log_le_sub_one_of_pos (by positivity)).trans_eq ?_
        field_simp
        ring
      have hh := mul_le_mul_of_nonneg_left h hv
      rw [mul_one_div] at hh
      rw [Nat.cast_succ, show (n : ℝ) + 1 + 3 = n + 4 by ring]
      linarith [hl n]
  by_contra! hlt
  have ht : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 3)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop ((C - f 0 + v * Real.log 3) / (v - w))).exists
  have := (div_lt_iff₀ (sub_pos.mpr hlt)).mp hn
  linarith [hb n, hu n]

def LogBound (P : ℕ → ℕ → ℝ) : Prop :=
  ∀ i j, P i j ≤ Real.log ((i : ℝ) + j + 1)

theorem weighted_growth (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (p : Increments P Q x) (q : Increments (Function.swap P) R y)
    (r : Increments (Function.swap Q) (Function.swap R) z)
    (hP : LogBound P) (hQ : LogBound Q) (hR : LogBound R)
    {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    4 * (x * B * C + y * A * C + z * A * B) ≤ ((A : ℝ) + B + C) ^ 2 := by
  let S := (A : ℝ) + B + C
  have hS : 0 < S := by unfold S; positivity
  let v := 4 * (x * B * C + y * A * C + z * A * B) / S
  let f (n : ℕ) := P (n * A) (n * B) * C + Q (n * A) (n * C) * B + R (n * B) (n * C) * A
  have hl (n : ℕ) : v / ((n : ℝ) + 3) ≤ f (n + 1) - f n := by
    have h (D : ℕ) : n * D ≤ (n + 1) * D := Nat.mul_le_mul_right D (Nat.le_succ n)
    have h₁ := p.step hx hA hB hC (h A)
    have h₂ := p.step hx hA hB hC (n := n) le_rfl
    have h₃ := q.step hy hB hA hC (h B)
    have h₄ := q.step hy hB hA hC (n := n) le_rfl
    have h₅ := r.step hz hC hA hB (h C)
    have h₆ := r.step hz hC hA hB (n := n) le_rfl
    rw [show (B : ℝ) + A + C = S by unfold S; ring] at h₃ h₄
    rw [show (C : ℝ) + A + B = S by unfold S; ring] at h₅ h₆
    dsimp only [Function.swap, f, v, S] at *
    rw [div_div, mul_comm ((A : ℝ) + B + C)]
    simp only [div_eq_mul_inv] at h₁ h₂ h₃ h₄ h₅ h₆ ⊢
    linarith only [h₁, h₂, h₃, h₄, h₅, h₆]
  have hu (n : ℕ) : f n ≤ S * Real.log ((n : ℝ) + 3) + S * Real.log S := by
    have hu' {P : ℕ → ℕ → ℝ} (h : LogBound P) {i j : ℕ} (hij : (i : ℝ) + j ≤ S) :
        P (n * i) (n * j) ≤ Real.log ((n : ℝ) + 3) + Real.log S := by
      rw [← Real.log_mul (by positivity) hS.ne']
      refine (h _ _).trans (Real.log_le_log (by positivity) ?_)
      have h₁ : 1 ≤ (A : ℝ) := by exact_mod_cast hA
      have h₂ := mul_le_mul_of_nonneg_left hij (Nat.cast_nonneg (α := ℝ) n)
      push_cast
      unfold S at *
      linarith
    let L := Real.log ((n : ℝ) + 3) + Real.log S
    calc
      _ ≤ L * C + L * B + L * A := by
        unfold f
        gcongr
        · apply hu' hP; unfold S; linarith
        · apply hu' hQ; unfold S; linarith
        · apply hu' hR; unfold S; linarith
      _ = _ := by unfold L S; ring
  have he : v ≤ S := growth (by unfold v; positivity) hl hu
  exact (pow_two S).symm ▸ (div_le_iff₀ hS).mp he

end OAI.LinearAlgebra.MatrixExponent.Rectangle
