import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace OAI
/-! # Squeezing the width profile of the exposed tagged predicate -/

namespace Hierarchy.TaggedWidthProfile

open Real Set MeasureTheory Filter
open scoped ContDiff
noncomputable section

/-- Smooth width exponents to which the shorter-address induction applies. -/
structure Admissible (s : ℝ) (u : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ u
  positive : ∀ a, 1 ≤ a → 0 < u a
  initial : s < u 1
  slope : ∀ a, 1 ≤ a → 0 ≤ -deriv u a ∧ -deriv u a < 1
  plateau : ∃ A : ℝ, 1 < A ∧ ∀ a, A ≤ a → u a = u A

/-- The ordinary and control cost terms have strictly positive slack on every
compact range of widths in the induction. -/
theorem Admissible.uniform_margins {s : ℝ} {u : ℝ→ℝ} (hu : Admissible s u) (A : ℝ) :
    (∃ m : ℝ,0<m ∧ ∀ a∈Icc 1 A,m≤u a) ∧
    ∀ a : ℝ,1≤a → 1+u 1≤a+u a := by
  refine ⟨isCompact_Icc.exists_forall_le' hu.smooth.continuous.continuousOn
    (fun a ha=>hu.positive a ha.1),?_⟩
  have mono : StrictMonoOn (fun a : ℝ=>a+u a) (Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
      ((continuous_id.add hu.smooth.continuous).continuousOn)
    intro a ha
    have a1 : 1≤a := interior_subset ha
    have d := (hasDerivAt_id a).add ((hu.smooth.differentiable (by simp) a).hasDerivAt)
    rw [d.deriv]
    linarith [(hu.slope a a1).2]
  exact fun a ha=>mono.monotoneOn (by simp) ha ha

/-- The ordinary work and the width-one control calls consume an arbitrarily
small fraction of the parent allowance, uniformly across the width interval. -/
theorem Admissible.ordinary_control_work {s : ℝ} {u : ℝ → ℝ} (hu : Admissible s u)
    (A k : ℝ) {control ε : ℝ} (hcontrol : control < u 1) (hε : 0 < ε) :
    ∀ᶠ h : ℝ in Filter.atTop, ∀ a ∈ Icc 1 A, ∀ n : ℝ, 0 ≤ n →
      n*h^a*(log h)^k + n*h^(1+control)*(log h)^k ≤ ε*(n*h^a*h^(u a)) := by
  obtain ⟨⟨m,hm,lower⟩,total⟩ := hu.uniform_margins A
  let d := min m (u 1-control)
  have hd : 0 < d := lt_min hm (sub_pos.mpr hcontrol)
  have little := (isLittleO_log_rpow_rpow_atTop k hd).bound (half_pos hε)
  filter_upwards [little, Filter.eventually_gt_atTop (1:ℝ)] with h budget h₁
  intro a ha n hn
  have hp := zero_lt_one.trans h₁
  change ‖(log h)^k‖ ≤ ε/2*‖h^d‖ at budget
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (log_pos h₁).le _),
    Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hp _)] at budget
  have dm : d ≤ u a := (min_le_left _ _).trans (lower a ha)
  have dc : 1+control+d ≤ a+u a := by linarith [total a ha.1,min_le_right m (u 1-control)]
  have price (x : ℝ) (win : x+d ≤ a+u a) :
      h^x*(log h)^k ≤ (ε/2)*(h^a*h^(u a)) := calc
    _ ≤ h^x*((ε/2)*h^d) := mul_le_mul_of_nonneg_left budget (Real.rpow_pos_of_pos hp _).le
    _ = (ε/2)*h^(x+d) := by rw [Real.rpow_add hp];ring
    _ ≤ (ε/2)*h^(a+u a) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h₁.le win)
      (half_pos hε).le
    _ = _ := by rw [Real.rpow_add hp]
  have q := mul_le_mul_of_nonneg_left (add_le_add (price a (by linarith)) (price (1+control) dc)) hn
  linarith only [q]

/-- One simultaneous strict margin for all pruning prices on a compact
interval. Here the price coordinates are b = −u′ and v = u + ab. -/
theorem Admissible.price_margins {s : ℝ} {u : ℝ→ℝ} (hu : Admissible s u) (A : ℝ) :
    ∃ δ : ℝ,0<δ ∧ ∀ a∈Icc 1 A,
      -deriv u a+δ≤1 ∧ δ≤u a+a*(-deriv u a)-(-deriv u a) := by
  obtain ⟨m,hm,mu⟩:=(hu.uniform_margins A).1
  have slopeContinuous : Continuous (fun a=>1+deriv u a) :=
    continuous_const.add (hu.smooth.continuous_deriv (by simp))
  have gradient : ∀ a∈Icc (1:ℝ) A,0<1+deriv u a := fun a ha=>by linarith [(hu.slope a ha.1).2]
  obtain ⟨v,hv,hbound⟩:=isCompact_Icc.exists_forall_le' slopeContinuous.continuousOn gradient
  refine ⟨min m v,lt_min hm hv,?_⟩
  intro a ha
  have h₁:=(min_le_right m v).trans (hbound a ha)
  have h₂:=(min_le_left m v).trans (mu a ha)
  refine ⟨by linarith,?_⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr ha.1) (hu.slope a ha.1).1]

/-- A common δ and η for all the dual charges of the shorter-call protocol,
including the dyadic floor and reciprocal margins. -/
theorem Admissible.uniform_prices {s : ℝ} {u : ℝ→ℝ} (hu : Admissible s u) (A : ℝ) :
    ∃ δ η : ℝ,0<δ ∧ 0<η ∧ ∀ a∈Icc 1 A,
      let b:=-deriv u a
      let v:=u a+a*b
      let θ:=b+δ
      0<θ ∧ δ≤θ ∧ θ<1 ∧ (1+η)*θ≤v-δ ∧ η≤v-δ ∧
        η≤1/θ-1 ∧ 1/θ-1≤1/η ∧ η≤1-θ := by
  obtain ⟨d,hd,price⟩:=hu.price_margins A
  let δ:=d/4
  have pos : 0<δ := div_pos hd (by norm_num)
  refine ⟨δ,δ,pos,pos,?_⟩
  intro a ha b v θ
  obtain ⟨upper,winning⟩:=price a ha
  have bn : 0≤b := (hu.slope a ha.1).1
  have room : θ+3*δ≤1 := by dsimp [θ,b,δ];linarith
  have advantage : θ+2*δ≤v-δ := by dsimp [θ,v,b,δ];linarith
  have dt : δ≤θ := by dsimp [θ];linarith
  have tp:=pos.trans_le dt
  have one : θ<1 := by linarith
  have mul : (1+δ)*θ≤θ+δ := by nlinarith [mul_nonneg pos.le (sub_nonneg.mpr one.le)]
  have floor : 1+δ≤1/θ := (le_div_iff₀ tp).mpr (by linarith)
  have ceiling : 1/θ≤1/δ := one_div_le_one_div_of_le pos dt
  exact ⟨tp,dt,one,by linarith,by linarith,by linarith,by linarith,by linarith⟩

/-- A smooth trial function that improves both alternatives in the packing
maximum whenever the width-one exponent is positive. Its derivative is
constant to the left of the transition and zero to the right. -/
private theorem exists_improving_le_one {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ u : ℝ → ℝ, Admissible s u ∧ ∃ a A : ℝ, 1<a ∧ 1≤A ∧
      1-1/a+u a/a<s ∧ 1-1/a+u A<s := by
  let b := 1-s/2
  let t := s/16
  let e := s*t/4
  let m := 1+s/2
  let N := 1+3*s/4
  have hb : 0<b := by dsimp [b]; linarith
  have hb1 : b<1 := by dsimp [b]; linarith
  have ht : 0<t := by dsimp [t]; positivity
  have he : 0<e := by dsimp [e]; positivity
  have hm : 1<m := by dsimp [m]; linarith
  have hmN : m<N := by dsimp [m,N]; linarith
  let f := fun x : ℝ => Real.smoothTransition ((N-x)/(N-m))
  have hf : ContDiff ℝ ∞ f := Real.smoothTransition.contDiff.comp (by fun_prop)
  have c := hf.continuous
  let area := fun x : ℝ => ∫ z in (1:ℝ)..x, f z
  have diff (x : ℝ) : HasDerivAt area (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (c.intervalIntegrable 1 x)
      c.stronglyMeasurable.stronglyMeasurableAtFilter c.continuousAt
  have smooth : ContDiff ℝ ∞ area := by
    apply contDiff_infty_iff_deriv.mpr
    have eq : deriv area=f := funext fun x=>(diff x).deriv
    exact ⟨fun x=>(diff x).differentiableAt,by simpa only [eq] using hf⟩
  let u := fun x : ℝ => s+e-b*area x
  have du (x : ℝ) : HasDerivAt u (-(b*f x)) x := by
    simpa [u] using (diff x).const_mul b |>.const_sub (s+e)
  have nonneg (x : ℝ) : 0≤f x := Real.smoothTransition.nonneg _
  have limit (x : ℝ) : f x≤1 := Real.smoothTransition.le_one _
  have bounds (x : ℝ) : 0 ≤ -deriv u x ∧ -deriv u x < 1 := by
    rw [(du x).deriv,neg_neg]
    exact ⟨mul_nonneg hb.le (nonneg x),(mul_le_of_le_one_right hb.le (limit x)).trans_lt hb1⟩
  have decreasing : Antitone u := antitone_of_deriv_nonpos (fun x=>(du x).differentiableAt)
    (fun x=>by linarith [(bounds x).1])
  have lowerSlope : Monotone (fun x : ℝ=>u x+x) := by
    apply monotone_of_deriv_nonneg (fun x=>(du x).differentiableAt.add differentiableAt_id)
    intro x
    have d := (du x).add (hasDerivAt_id x)
    change 0 ≤ deriv (u + id) x
    rw [d.deriv]
    have h := (bounds x).2
    rw [(du x).deriv,neg_neg] at h
    linarith
  have linear (x : ℝ) (hx : 1≤x) (hxm : x≤m) : u x = s+e-b*(x-1) := by
    have all : EqOn f (fun _ : ℝ=>1) (uIcc 1 x) := by
      rw [uIcc_of_le hx]
      intro z hz
      exact Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hmN)).mpr (by linarith [hz.2]))
    change s+e-b*(∫ z in (1:ℝ)..x,f z)=_
    rw [intervalIntegral.integral_congr all,intervalIntegral.integral_const]
    simp
  have flat (x : ℝ) (hx : N≤x) : u x=u N := by
    have all : EqOn f (fun _ : ℝ=>0) (uIcc N x) := by
      rw [uIcc_of_le hx]
      intro z hz
      exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [hz.1])
        (sub_nonneg.mpr hmN.le))
    have none : (∫ z in N..x,f z) = 0 := by rw [intervalIntegral.integral_congr all];simp
    have chain := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (c.intervalIntegrable 1 N) (c.intervalIntegrable N x)
    change s+e-b*(∫ z in (1:ℝ)..x,f z)=s+e-b*(∫ z in (1:ℝ)..N,f z)
    rw [←chain,none,add_zero]
  have u1 : u 1=s+e := by simp [u,area]
  have uN : 0<u N := by
    have slope := lowerSlope (hm.le.trans hmN.le)
    change u 1+1≤u N+N at slope
    rw [u1] at slope
    dsimp [N] at slope
    linarith
  refine ⟨u,⟨contDiff_const.sub (contDiff_const.mul smooth),?_,by linarith,fun a _=>bounds a,
    ⟨N,hm.trans hmN,flat⟩⟩,1+t,m,by linarith,hm.le,?_,?_⟩
  · intro x hx
    by_cases h : N≤x
    · rwa [flat x h]
    · exact uN.trans_le (decreasing (le_of_not_ge h))
  · rw [linear (1+t) (by linarith) (by dsimp [t,m];linarith)]
    have denom : 0<1+t := by linarith
    rw [show 1-1/(1+t)+(s+e-b*(1+t-1))/(1+t)=(t+s+e-b*t)/(1+t) by
      field_simp [denom.ne'];ring]
    apply (div_lt_iff₀ denom).mpr
    dsimp [e,b,t]
    nlinarith [sq_pos_of_pos hs]
  · rw [linear m hm.le le_rfl]
    have frac : 1-1/(1+t) ≤ t := by
      have pos : 0<1+t := by linarith
      have inv : 1-t ≤ 1/(1+t) := (le_div_iff₀ pos).mpr (by nlinarith [sq_nonneg t])
      linarith
    have esmall : e≤s/64 := by
      dsimp [e,t]
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs1)]
    have margin : t+(s+e-b*(m-1))<s := by
      dsimp [m,b,t]
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs1)]
    linarith

/-- Translating the trial function gives strict improvements for every
positive starting profile value, independently of the initial size bound. -/
theorem exists_improving {s : ℝ} (hs : 0 < s) :
    ∃ u : ℝ → ℝ, Admissible s u ∧ ∃ a A : ℝ, 1<a ∧ 1≤A ∧
      1-1/a+u a/a<s ∧ 1-1/a+u A<s := by
  by_cases small : s ≤ 1
  · exact exists_improving_le_one hs small
  obtain ⟨u,trial,a,A,ha,hA,first,second⟩ := exists_improving_le_one zero_lt_one le_rfl
  let v := fun a : ℝ => u a+(s-1)
  have dv (x : ℝ) : deriv v x = deriv u x :=
    ((trial.smooth.differentiable (by simp) x).hasDerivAt.add_const _).deriv
  obtain ⟨B,hB,flat⟩ := trial.plateau
  have t : 0 ≤ s-1 := by linarith
  have d : (s-1)/a ≤ s-1 := div_le_self t ha.le
  refine ⟨v,⟨trial.smooth.add contDiff_const,?_,?_,?_,?_⟩,a,A,ha,hA,?_,?_⟩
  · exact fun x hx => add_pos_of_pos_of_nonneg (trial.positive x hx) t
  · dsimp [v];linarith [trial.initial]
  · intro x hx
    rw [dv]
    exact trial.slope x hx
  · exact ⟨B,hB,fun x hx => congrArg (·+(s-1)) (flat x hx)⟩
  · dsimp [v]
    rw [add_div]
    linarith
  · dsimp [v];linarith

/-- Packing plus the admissible upper bounds on every fixed width force the
threshold at width one to vanish. -/
theorem squeeze (r : ℝ → ℝ) (rInfinity : ℝ) (nonneg : 0≤r 1)
    (inf_le : ∀ A : ℝ,1≤A → rInfinity≤r A)
    (packing : ∀ a : ℝ,1<a → r 1≤1-1/a+max (r a/a) rInfinity)
    (majorizes : ∀ u : ℝ→ℝ,Admissible (r 1) u → ∀ a : ℝ,1≤a → r a≤u a) :
    r 1=0 := by
  refine le_antisymm ?_ nonneg
  by_contra! positive
  obtain ⟨u,hu,a,A,ha,hA,hfirst,hsecond⟩:=exists_improving positive
  have h₁:=div_le_div_of_nonneg_right (majorizes u hu a ha.le) (by linarith : 0≤a)
  have h₂:=(inf_le A hA).trans (majorizes u hu A hA)
  have h:=packing a ha
  rcases le_total (r a/a) rInfinity with hmax | hmax
  · rw [max_eq_right hmax] at h
    linarith
  · rw [max_eq_left hmax] at h
    linarith

end
end Hierarchy.TaggedWidthProfile

end OAI
