import OAI.LinearAlgebra.SpectralBooks.Cube

/-! # Endpoint coupling costs after reducing all coordinate gap widths

A small width makes each one-coordinate change almost independent of the
other coordinates. Telescoping from the all-false corner approximates the
table by a sum of one-coordinate functions, whose mean depends only on the
one-coordinate marginals.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace CubeTable

open Finset Function
noncomputable section

variable {r : ℕ}

/-- An endpoint probability law with prescribed probabilities at the second endpoint. -/
structure IsCoupling (w : CubeTable r) (t : Fin r → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ w x
  total : ∑ x, w x = 1
  marginal : ∀ i, (∑ x, if x i then w x else 0) = t i

def cost (w N : CubeTable r) : ℝ := ∑ x, w x * N x

def independent (t : Fin r → ℝ) : CubeTable r :=
  fun x ↦ ∏ i, if x i then t i else 1 - t i

theorem independent_isCoupling {t : Fin r → ℝ} (ht : ∀ i, t i ∈ Set.Icc 0 1) :
    IsCoupling (independent t) t := by
  let p (i : Fin r) (b : Bool) := if b then t i else 1 - t i
  have htotal (i : Fin r) : ∑ b : Bool, p i b = 1 := by simp [p]
  constructor
  · intro x
    exact Finset.prod_nonneg (fun i _ ↦ by
      change 0 ≤ if x i then t i else 1 - t i
      split <;> first | exact (ht i).1 | exact sub_nonneg.mpr (ht i).2)
  · change (∑ x : Fin r → Bool, ∏ i, p i (x i)) = 1
    rw [← Fintype.prod_sum]
    simp only [htotal, Finset.prod_const_one]
  · intro i
    let q (j : Fin r) (b : Bool) := if j = i ∧ b = false then 0 else p j b
    have hq (x : Fin r → Bool) : (if x i then independent t x else 0) = ∏ j, q j (x j) := by
      cases hi : x i with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [q, hi])).symm
      | true =>
        simp only [↓reduceIte]
        apply Finset.prod_congr rfl
        intro j _
        by_cases hj : j = i
        · subst j
          simp [q, p, hi]
        · simp [q, p, hj]
    simp only [hq, ← Fintype.prod_sum]
    have hj (j : Fin r) : (∑ b : Bool, q j b) = if j = i then t j else 1 := by
      by_cases h : j = i <;> simp [q, p, h]
    simp only [hj, Fintype.prod_ite_eq']

theorem cost_mono {w : CubeTable r} {t : Fin r → ℝ} (hw : IsCoupling w t)
    {N M : CubeTable r} (h : N ≤ M) : cost w N ≤ cost w M :=
  Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (h x) (hw.nonneg x)

/-- Additive approximation, normalized to agree with the price at the all-false corner. -/
def additiveApprox (N : CubeTable r) : CubeTable r := fun x ↦
  N (fun _ ↦ false) + ∑ i, if x i then -gap N i (fun _ ↦ false) else 0

theorem abs_sub_additiveApprox (N : CubeTable r) {ε : ℝ} (hε : 0 ≤ ε)
    (hwid : ∀ i, width N i ≤ ε) (x : Fin r → Bool) : |N x - additiveApprox N x| ≤ r * ε := by
  let o : Fin r → Bool := fun _ ↦ false
  let d (i : Fin r) := if x i then -gap N i o else 0
  have h (s : Finset (Fin r)) :
      |N (s.piecewise x o) - (N o + ∑ i ∈ s, d i)| ≤ s.card * ε := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      let y := s.piecewise x o
      have hy : update y i false = y := update_eq_self_iff.mpr (by simp [y, hi, o])
      have hstep : |N (update y i (x i)) - N y - d i| ≤ ε := by
        cases hx : x i with
        | false => simpa [d, hx, hy] using hε
        | true =>
          have hb := (abs_gap_sub_gap_le_width N i o y).trans (hwid i)
          simp only [gap, hy] at hb
          simp only [d, hx, ↓reduceIte, sub_neg_eq_add, gap]
          convert hb using 2
          ring
      rw [piecewise_insert, sum_insert hi, card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      calc
        _ = |(N (update y i (x i)) - N y - d i) + (N y - (N o + ∑ j ∈ s, d j))| := by
          congr 1
          change N (update y i (x i)) - _ = _
          ring
        _ ≤ _ := (abs_add_le _ _).trans ((add_le_add hstep ih).trans_eq (by ring))
  simpa [additiveApprox, o, d] using h univ

private theorem cost_additiveApprox {w : CubeTable r} {t : Fin r → ℝ}
    (hw : IsCoupling w t) (N : CubeTable r) :
    cost w (additiveApprox N) = N (fun _ ↦ false) + ∑ i, t i * (-gap N i (fun _ ↦ false)) := by
  simp only [cost, additiveApprox, mul_add, mul_sum, sum_add_distrib, ← sum_mul, hw.total, one_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hw.marginal i, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x i <;> simp [hx]

private theorem abs_cost_sub_of_uniform {w N M : CubeTable r} {t : Fin r → ℝ}
    (hw : IsCoupling w t) {d : ℝ} (h : ∀ x, |N x - M x| ≤ d) :
    |cost w N - cost w M| ≤ d := by
  simp only [cost, ← Finset.sum_sub_distrib, ← mul_sub]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ x, w x * d := Finset.sum_le_sum fun x _ ↦ by
      rw [abs_mul, abs_of_nonneg (hw.nonneg x)]
      exact mul_le_mul_of_nonneg_left (h x) (hw.nonneg x)
    _ = d := by rw [← sum_mul, hw.total, one_mul]

/-- Couplings with the same marginals differ in expected cost by at most
twice the additive approximation error. -/
theorem cost_le_cost_of_width {w π : CubeTable r} {t : Fin r → ℝ}
    (hw : IsCoupling w t) (hπ : IsCoupling π t) (N : CubeTable r)
    {ε : ℝ} (hε : 0 ≤ ε) (hwid : ∀ i, width N i ≤ ε) :
    cost w N ≤ cost π N + 2 * (r : ℝ) * ε := by
  have hA := abs_sub_additiveApprox N hε hwid
  have hwA := (abs_le.mp (abs_cost_sub_of_uniform hw hA)).2
  have hπA := (abs_le.mp (abs_cost_sub_of_uniform hπ hA)).1
  rw [cost_additiveApprox hw] at hwA
  rw [cost_additiveApprox hπ] at hπA
  linarith

end
end CubeTable

end SpectralBooks
end LinearAlgebra
end OAI
