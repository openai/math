import OAI.Geometry.Hirsch.Calibration

noncomputable section

open Filter

namespace OAI.Geometry.Hirsch.Layer.Growth.Plan

variable (p : Plan)

theorem bounds (k : ℕ) : ∀ᶠ r : ℕ in atTop, let u := p.dial r
    u.capacity k*u.U ≤ u.gamma*u.M ∧
    u.capacity k*(u.tests.value u.K+(u.K*(u.D k).max+(u.D k).step+1)*u.p) ≤ u.gamma*u.A := by
  let c : ℝ := (p.dial 0).capacity k
  let b : ℝ := p.K*((p.dial 0).D k).max+((p.dial 0).D k).step+1
  have h := dominates (show 1-(p.T : ℝ) < -1+(3-p.T) by linarith) c
  have h' := ((Order.base (-100*p.K)).add
    (((Order.base (-2*p.T)).scale b).up (by linarith [p.large,p.two]))).scale c
  filter_upwards [h,h'.lt (y := -1+(-32*p.K)) (by linarith [p.two])] with r h h'
  dsimp only
  rw [umax,end_test]
  rw [← mul] at h h'
  exact ⟨h.le,h'.le⟩

theorem reliable (k : ℕ) (hk : k ≤ p.h) : ∀ᶠ r : ℕ in atTop, let u := p.dial r
    u.gamma ≤ u.margin k^u.K - 2*u.K*u.cost (k+1) := by
  have hN : (0 : ℝ) < p.N := Nat.cast_pos.mpr p.npos
  have gap : (-1 : ℝ) < (-8/p.N*k)*p.K := by
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,lt_div_iff₀ hN]
    simp only [N,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
    have hh : (k : ℝ) ≤ p.h := Nat.cast_le.mpr hk
    nlinarith [p.two,mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg p.K : (0 : ℝ) ≤ p.K)]
  have cost := (((Order.base (-100*p.K)).scale (1+4^p.K)).scale (↑(k+1) : ℝ)).scale (2*p.K)
  have hh := ((Order.base (-1)).add (cost.up (by linarith [p.two]))).lt gap
  filter_upwards [hh] with r hh
  dsimp only; rw [le_sub_iff_add_le,Dials.margin,p.lambda,pow,pow,Dials.cost,p.end_test]
  exact hh.le

theorem contract : ∀ᶠ r : ℕ in atTop, let u := p.dial r
    u.K*Real.exp (-u.L) ≤ 1/2 ∧ (u.K*Real.exp (-u.L))^u.cycles ≤ u.t/2 := by
  have hN : (0 : ℝ) < p.N := Nat.cast_pos.mpr p.npos
  have h := (Order.base (-1/p.N)).scale p.K
  have low := (h.scale 2).lt (div_neg_of_neg_of_pos (by norm_num) hN)
  have gap : (-1/(p.N : ℝ))*p.rounds < -(p.T : ℝ) := by
    rw [rounds,Nat.cast_mul,← mul_assoc,div_mul_cancel₀ _ hN.ne']
    push_cast; linarith
  filter_upwards [low,((h.power p.rounds).scale 2).lt gap] with r hl hh
  rw [zero] at hl
  dsimp only; rw [p.neg_lambda]
  change p.K*E r _ ≤ 1/2 ∧ (p.K*E r _)^p.rounds ≤ E r (-p.T)/2
  constructor <;> linarith

theorem bins (r : ℕ) (hr : 0 < r) : (p.dial r).M < price (p.dial r).t (p.dial r).J := by
  have he : (2 : ℝ)^(4*r+2) = E r 4 * 4 := by
    rw [pow_add,Nat.mul_comm 4 r,pow_mul,← one,pow]; norm_num
  change E r (3-p.T) < E r (-p.T)/4 * 2^(4*r+2)
  rw [he,show E r (-p.T)/4 * (E r 4*4) = E r (-p.T)*E r 4 by ring,mul]
  apply Real.exp_lt_exp.mpr
  apply mul_lt_mul_of_pos_left (by linarith)
  exact mul_pos (Nat.cast_pos.mpr hr) (Real.log_pos (by norm_num))

theorem valid : ∀ᶠ r : ℕ in atTop, (p.dial r).Valid := by
  have hrel := Filter.eventually_all_finite (Set.finite_le_nat p.h) |>.mpr (fun k hk => p.reliable k hk)
  have hbounds := Filter.eventually_all_finite (Set.finite_lt_nat p.h) |>.mpr (fun k _ => p.bounds k)
  have hsmall := Filter.eventually_all_finite (Set.finite_lt_nat p.h) |>.mpr (fun k _ => p.small k)
  filter_upwards [eventually_gt_atTop 0,hrel,hbounds,hsmall,p.comparisons,p.contract] with r hr hrel hb hs he hc
  refine ⟨p.enough,?_,pos ..,mono _ ?_,le_one _ ?_,pos ..,le_one _ ?_,?_,(pos ..).le,
    (pos ..).le,pos ..,pos ..,p.start r,hrel,hb,he.1,he.2.1,he.2.2,p.bins r hr,hs,hc.1,hc.2⟩
  · exact Nat.le_self_pow hr.ne' 2
  · linarith [p.large,p.two]
  · exact neg_nonpos.mpr (Nat.cast_nonneg _)
  · exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg _)
  · change 0 ≤ (r : ℝ)*Real.log 2/p.N
    positivity

end OAI.Geometry.Hirsch.Layer.Growth.Plan
