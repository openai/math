import OAI.LinearAlgebra.MatrixExponent.Rounds.Installation
import OAI.LinearAlgebra.MatrixExponent.Shaving.Stages

/-!
# A stage with arbitrary fixed polynomial label lengths

The cutoff may depend on the label length, but the saving and
the field-size window are chosen first. The same finite extension
works for all networks and all rounds of the stage.
-/

namespace OAI.LinearAlgebra.MatrixExponent
open Filter

namespace Rounds

private theorem height_grows : Tendsto (Nat.clog 2) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [Shaving.tendsto_height.eventually_ge_atTop (B : ℝ)] with n hn
  exact_mod_cast hn

theorem label_length_le (C : ℝ) (hC : 0 ≤ C) (r : ℕ) :
    ∀ᶠ n : ℕ in atTop, ⌈C * (1 + Real.logb 2 (Nat.clog 2 n)) ^ r⌉₊ ≤ (Nat.clog 2 (Nat.clog 2 n)) ^ (r + 1) := by
  have ht := Shaving.tendsto_height.comp height_grows
  filter_upwards [height_grows.eventually_ge_atTop 1,
    ht.eventually_ge_atTop 1, ht.eventually_ge_atTop (C * 2 ^ r)] with n h₀ h₁ h₂
  let h := Nat.clog 2 n
  let x : ℝ := Nat.clog 2 h
  change 1 ≤ x at h₁
  change C * 2 ^ r ≤ x at h₂
  have hlog : Real.logb 2 h ≤ x := by
    have := Nat.le_ceil (Real.logb 2 h)
    rw [show ⌈Real.logb 2 h⌉₊ = Nat.clog 2 h from Real.natCeil_logb_natCast 2 h] at this
    exact this
  have hz : 0 ≤ Real.logb 2 h := Real.logb_nonneg (by norm_num) (by exact_mod_cast h₀)
  apply Nat.ceil_le.mpr
  rw [Nat.cast_pow]
  calc
    _ ≤ C * (2 * x) ^ r := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) _) hC
    _ = (C * 2 ^ r) * x ^ r := by rw [mul_pow, mul_assoc]
    _ ≤ x * x ^ r := mul_le_mul_of_nonneg_right h₂ (by positivity)
    _ = _ := (pow_succ' ..).symm

theorem labelLimit_le (C : ℝ) (hC : 0 ≤ C) (r : ℕ) :
    ∀ᶠ n : ℕ in atTop, Shaving.labelLimit C r n ≤ inputDictionary (r + 1) n := by
  filter_upwards [label_length_le C hC r] with n hn
  exact Nat.pow_le_pow_right (by decide) hn

theorem PolyInstallable.macro_stage {F : Type} [Field F] (install : PolyInstallable F) :
    Shaving.Macro F := by
  intro δ β hd hd' hb hb'
  obtain ⟨p, A, T₀, c, L, _, _, _, go⟩ := install δ β hd hd' hb hb'
  let q := p.groupRate + c + 1
  have hq : 1 ≤ (q : ℝ) := by unfold q; push_cast; linarith
  obtain ⟨D, hD, fields⟩ := Shaving.extension F L A
  refine ⟨β / q, D, by positivity, hD, ?_⟩
  intro a b ξ C r ha ha' hβ hβ' hξ hC
  have small : (q : ℝ) * a < β := by rwa [lt_div_iff₀ (by positivity), mul_comm] at ha'
  have ha1 : a ≤ 1 := by nlinarith
  have ht : 0 < a * δ / 6 := by positivity
  obtain ⟨M, hm⟩ := go a b ξ ha small hβ hβ' hξ (r + 1)
  have cost := p.costs (M := M) (T₀ := T₀) (ξ := ξ) (b := b) ht ha1 (by linarith)
  have grow := (tendsto_rpow_atTop ht).comp Shaving.tendsto_height
  filter_upwards [hm, cost, grow.eventually_ge_atTop 3, height_grows.eventually fields,
    labelLimit_le C hC r] with n hn hcost hg hfield hlabels
  obtain ⟨v, hv, hr⟩ := hn
  obtain ⟨K, _, _, _, _, _, _, hlo, hhi, hdeg⟩ := hfield
  refine ⟨K, inferInstance, inferInstance, inferInstance, hdeg, ?_⟩
  apply v.stage_of_installations ha hd (small.le.trans hβ) hv (hcost v hv) hg
  intro x y G m u labels hl hm hs had hf hu he
  exact hr K hlo hhi x y G m u labels hl hm hs had (hf.trans hlabels) hu he

theorem macro_of_shared_price {F : Type} [Field F] [Finite F]
    (h : Prices.SharedPrice (AlgebraicClosure F)) : Shaving.Macro F := by
  apply PolyInstallable.macro_stage
  apply polyInstallable_of_controller F h
  intro K _ _ s hs p l b
  exact SphereScale.controlled K s hs p l b

theorem macro_of_square_saving {F : Type} [Field F] [Finite F]
    (h : omega F < 9 / 4) : Shaving.Macro F :=
  macro_of_shared_price (shared_of_saving h)

end Rounds

/-- The tensor-power bound for arbitrary trivalent networks with
separate exterior positions. -/
theorem compresses_of_square_saving {F : Type} [Field F] [Finite F]
    (h : omega F < 9 / 4) : Compresses F :=
  compresses_of_shared_price (shared_of_saving h)

end OAI.LinearAlgebra.MatrixExponent
