import OAI.Hierarchy.ProbeOuterLedger
import OAI.Hierarchy.ProbeParameters

namespace OAI
/-! # The actual initial bill for the scale-t tile bank -/

namespace Hierarchy.AdaptiveProbe
open Filter
open scoped BigOperators
noncomputable section

/-- The positive-scale part has one link per payload, tile and layer (the
center, or one of the two signed endpoints per axis). The other core links
can have arbitrary nonnegative lengths in the physical layout. -/
abbrev CoreRow (Z P : Type*) (N k : ℕ) := Z ⊕ ((P × Fin N) × Option (Fin k × Bool))

def coreScale {Z P : Type*} {N k : ℕ} (t : ℝ) : CoreRow Z P N k → ℝ :=
  Sum.elim (fun _=>0) (fun _=>t)

def coreLength {Z P : Type*} {N k : ℕ} (zeroLength : Z → ℝ) : CoreRow Z P N k → ℝ :=
  Sum.elim zeroLength (fun _=>1)

theorem core_capacity_bill {Z P : Type*} [Fintype Z] [Fintype P] (N k : ℕ)
    (p q Q Λ t : ℝ) (positive : 0<t) (zeroLength : Z→ℝ) :
    (∑ e : CoreRow Z P N k, Λ*capacity p q Q (coreScale t e) (coreLength zeroLength e)) =
      Fintype.card P * (Λ*(1+2*k)*N*t^p) := by
  simp [CoreRow,Fintype.sum_sum_type,coreScale,coreLength,capacity_unit _ _ _ _ positive,
    nsmul_eq_mul,Fintype.card_prod,Fintype.card_option,Nat.cast_mul,Nat.cast_add]
 ; ring

/-- With the stage bound Nt≤C and p>1, the initial per-payload capacity
bill fits the paper's first unit, uniformly before the population is chosen. -/
theorem core_capacity_eventual (k : ℕ) {p σ Λ C : ℝ}
    (hp : 1<p) (hσ : 0<σ) (hΛ : 0<Λ) (hC : 0<C) :
    ∀ᶠ W : ℕ in atTop, ∀ N : ℕ, (N:ℝ)*dyadicScale W≤C →
      Λ*(1+2*k)*N*(dyadicScale W)^p≤1 := by
  have hk : 0<Λ*(1+2*(k:ℝ)) := by positivity
  filter_upwards [affordable_scale hp hσ hC hk (show (0:ℝ)<1 by norm_num),eventually_ge_atTop 1] with W hard large
  intro N bound
  have pay := (hard.2 (N:ℝ) (by positivity) bound).1
  have one : (1:ℝ)≤W := by exact_mod_cast large
  have enough : (1:ℝ)≤(W:ℝ)^4 := one_le_pow₀ one
  calc
    _ = (Λ*(1+2*(k:ℝ)))*(1:ℝ)*N*(dyadicScale W)^p := by ring
    _ ≤ _ := by
      apply le_trans _ pay
      have t : 0≤(dyadicScale W)^p := Real.rpow_nonneg (by unfold dyadicScale; positivity) _
      gcongr

/-- At zero inventory the actual count of scale-t core links supplies the
initial cash bound for the probing schedule. -/
theorem initial_core_budget {I X Z P : Type*} [Fintype I] [Fintype Z] [Fintype P]
    (B : OuterBank I X) (start : X) (w N k : ℕ) (p q Q Λ t : ℝ) (positive : 0<t)
    (len : Z→ℝ) (ha : 0≤B.a) (hb : ∀ i,0≤B.coefficient i)
    (empty : ∀ i,B.stock start i=0)
    (installed : B.cash start =
      ∑ e : CoreRow Z P N k, Λ*capacity p q Q (coreScale t e) (coreLength len e))
    (scale : Λ*(1+2*k)*N*t^p≤1) : B.balance w 1 start≤Fintype.card P := by
  apply B.initial_balance start empty ha hb
  rw [installed,core_capacity_bill N k p q Q Λ t positive]
  simpa only [mul_one] using (mul_le_mul_of_nonneg_left scale (Nat.cast_nonneg (α:=ℝ) (Fintype.card P)))

end
end Hierarchy.AdaptiveProbe

end OAI
