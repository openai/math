import OAI.Hierarchy.ProbeReplacementLedger
import OAI.Hierarchy.ProbeIntegerBatch

namespace OAI
/-! # Quadratic control of simultaneous, integral replacements

The bound follows from incidence in the disjoint failed balls. It applies to
all installed and consumed word widths separately, before cancellation. -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators Classical
noncomputable section

variable {E I : Type*} [Fintype E] [Fintype I]

omit [Fintype I] in
/-- Counting actual incidence in each commodity, the stock displacement produced by a
bounded family of coincident roles has the required linear dependence on 1/K. -/
theorem stock_uniform (kind : E → Option I) (installed consumed : E → ℕ)
    (K w C d : ℕ) (hK : 0 < K) (hw : 0 < w)
    (degree : ∀ i, (Finset.univ.filter fun e => kind e=some i).card ≤ d)
    (cost : ∀ e, K*(installed e + consumed e) ≤ w*C) (i : I) :
    |stockChange kind (netUnits w installed consumed) i| ≤ (d:ℝ)*C/K := by
  classical
  let fiber := Finset.univ.filter fun e => kind e=some i
  have realK : 0 < (K:ℝ) := by exact_mod_cast hK
  have realw : 0 < (w:ℝ) := by exact_mod_cast hw
  have unit (e : E) : |netUnits w installed consumed e| ≤ (C:ℝ)/K := by
    rw [netUnits,abs_div,abs_of_pos realw,div_le_div_iff₀ realw realK]
    have both : |(installed e:ℝ)-consumed e| ≤ installed e+consumed e := by
      rw [abs_le]; constructor <;> linarith only [Nat.cast_nonneg (α:=ℝ) (installed e),Nat.cast_nonneg (α:=ℝ) (consumed e)]
    have realCost : (K:ℝ)*((installed e:ℝ)+consumed e) ≤ w*C := by exact_mod_cast cost e
    nlinarith only [mul_le_mul_of_nonneg_left both realK.le,realCost]
  change |∑ e, if kind e=some i then netUnits w installed consumed e else 0| ≤ _
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ e ∈ fiber, |netUnits w installed consumed e| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _ ∈ fiber, (C:ℝ)/K := Finset.sum_le_sum fun e _ => unit e
    _ = (fiber.card:ℝ)*((C:ℝ)/K) := by simp
    _ ≤ (d:ℝ)*((C:ℝ)/K) := mul_le_mul_of_nonneg_right (by exact_mod_cast degree i) (by positivity)
    _ = _ := by ring

/-- Choose one fixed inverse batch rate that absorbs the nonlinear remainder on every
problem size. The dimension bound is on the real physical commodity array. -/
theorem exists_quadratic_rate {a s density γ C L : ℝ}
    (ha : 0 < a) (hs : 0 < s) (hd : 0 < density) (hg : 0 < γ)
    (hC : 0 ≤ C) (_hL : 0 ≤ L) :
    ∃ K : ℕ, 0 < K ∧ ∀ {n : ℕ}, (Fintype.card I:ℝ) ≤ L*n →
      ∀ δ : I → ℝ, (∀ i, |δ i| ≤ C/K) →
      (∑ i, (δ i)^2/(4*s*a)) ≤ (n:ℝ)*density*γ/(8*K) := by
  obtain ⟨K,large⟩ := exists_nat_gt (max (2*L*C^2/(s*a*density*γ)) 0)
  have hK : (0:ℝ) < K := (le_max_right _ _).trans_lt large
  have bound := (div_lt_iff₀ (show 0 < s*a*density*γ by positivity)).1 ((le_max_left _ _).trans_lt large)
  refine ⟨K,by exact_mod_cast hK,?_⟩
  intro n dim δ size
  have coord (i : I) : (δ i)^2/(4*s*a) ≤ (C/K)^2/(4*s*a) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa using (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ C/(K:ℝ))).2 (size i)
  calc
    _ ≤ ∑ _ : I, (C/K)^2/(4*s*a) := Finset.sum_le_sum fun i _ => coord i
    _ = (Fintype.card I:ℝ)*((C/K)^2/(4*s*a)) := by simp
    _ ≤ (L*n)*((C/K)^2/(4*s*a)) := mul_le_mul_of_nonneg_right dim (by positivity)
    _ ≤ _ := by
      apply (le_div_iff₀ (show 0 < 8*(K:ℝ) by positivity)).2
      have simple : L*((C/K)^2/(4*s*a))*(8*K) ≤ density*γ := by
        field_simp [hK.ne',hs.ne',ha.ne']
        nlinarith only [bound.le]
      nlinarith only [mul_le_mul_of_nonneg_left simple (Nat.cast_nonneg (α:=ℝ) n)]

end
end Hierarchy.AdaptiveProbe

end OAI
