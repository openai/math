import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI
/-! # Uniform change of the tagged size allowance under shorter calls -/

namespace Hierarchy.TaggedWidthProfile
open Real Set Filter
open scoped ContDiff Topology BigOperators
noncomputable section

private theorem secant_between {u : ℝ→ℝ} (hu : Differentiable ℝ u) (a b : ℝ) :
    ∃ c ∈ uIcc a b, u b-u a=deriv u c*(b-a) := by
  rcases lt_trichotomy a b with h | h | h
  · obtain ⟨c,hc,e⟩:=exists_deriv_eq_slope u h hu.continuous.continuousOn hu.differentiableOn
    exact ⟨c,by simpa [uIcc_of_le h.le] using And.intro hc.1.le hc.2.le,
      ((eq_div_iff (sub_ne_zero.mpr h.ne')).mp e).symm⟩
  · subst b
    exact ⟨a,left_mem_uIcc,by simp⟩
  · obtain ⟨c,hc,e⟩:=exists_deriv_eq_slope u h hu.continuous.continuousOn hu.differentiableOn
    refine ⟨c,by simpa [uIcc_of_ge h.le] using And.intro hc.1.le hc.2.le,?_⟩
    have eq:=(eq_div_iff (sub_ne_zero.mpr h.ne')).mp e
    linarith only [eq]

/-- Here `H` is the logarithm of the shorter address height, `α` is the log
height ratio and `β` is the log payload ratio. The conclusion holds uniformly
over all width exponents and all ratios with the stated common bound. -/
theorem uniform_log_error {u : ℝ→ℝ} (hu : ContDiff ℝ 1 u) (lo hi C ε : ℝ)
    (hC : 0≤C) (hε : 0<ε) :
    ∃ H₀ : ℝ, 0≤H₀ ∧ ∀ a ∈ Icc lo hi, ∀ b ∈ Icc lo hi, ∀ H α β : ℝ,
      H₀<H → H*(b-a)=β-a*α → |β-a*α|≤C →
      |H*u b-(H-α)*u a - ((u a-a*deriv u a)*α+deriv u a*β)|<ε := by
  let η:=ε/(C+1)
  have positive : 0<C+1 := by linarith
  have hη : 0<η := div_pos hε positive
  have smooth : UniformContinuousOn (deriv u) (Icc lo hi) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hu.continuous_deriv (by decide)).continuousOn
  obtain ⟨δ,hδ,near⟩:=Metric.uniformContinuousOn_iff.mp smooth η hη
  refine ⟨C/δ,div_nonneg hC hδ.le,?_⟩
  intro a ha b hb H α β large scale budget
  have hH : 0<H := (div_nonneg hC hδ.le).trans_lt large
  have short : |b-a|<δ := by
    have B:=budget
    rw [←scale,abs_mul,abs_of_pos hH] at B
    have h : C<H*δ := (div_lt_iff₀ hδ).mp large
    by_contra! big
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_left big hH.le)) (B.trans_lt h)
  obtain ⟨c,hc,secant⟩:=secant_between (hu.differentiable (by decide)) a b
  have hc' : c∈Icc lo hi := uIcc_subset_Icc ha hb hc
  have distance : dist c a<δ := by
    rw [Real.dist_eq]
    exact (abs_sub_left_of_mem_uIcc hc).trans_lt short
  have slope := near c hc' a ha distance
  rw [Real.dist_eq] at slope
  have exactError :
      H*u b-(H-α)*u a-((u a-a*deriv u a)*α+deriv u a*β)=
      (deriv u c-deriv u a)*(β-a*α) := by
    linear_combination H * secant + (deriv u c) * scale
  rw [exactError,abs_mul]
  calc
    _ ≤ η*C := mul_le_mul slope.le budget (abs_nonneg _) hη.le
    _ < η*(C+1) := by nlinarith only [hη]
    _ = ε := by dsimp [η];field_simp

/-- The actual size allowance multiplies a payload width by a height power. -/
def allowance (u : ℝ→ℝ) (h w : ℝ) := w * h^(u (log w/log h))

/-- Splitting a wide payload into finitely many slices preserves the total
allowance once all of their width exponents belong to the plateau. -/
theorem allowance_split {ι : Type*} (slices : Finset ι) (width : ι → ℝ)
    (u : ℝ → ℝ) (h w A : ℝ) (flat : ∀ x, A ≤ x → u x = u A)
    (total : ∑ i ∈ slices, width i = w) (whole : A ≤ log w/log h)
    (parts : ∀ i ∈ slices, A ≤ log (width i)/log h) :
    ∑ i ∈ slices, allowance u h (width i) = allowance u h w := calc
  _ = ∑ i ∈ slices, width i*h^(u A) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [allowance, flat _ (parts i hi)]
  _ = _ := by rw [← Finset.sum_mul, total, allowance, flat _ whole]

/-- The estimate in logarithmic coordinates applies to the ratio of the actual
allowances. Thus exponentially small rounding in address lengths or payloads
can be incorporated through their *actual* ratios h'/h and w'/w. -/
theorem uniform_allowance_ratio {u : ℝ→ℝ} (hu : ContDiff ℝ 1 u) (lo hi C ε : ℝ)
    (hC : 0≤C) (hε : 0<ε) :
    ∃ H₀ : ℝ, 0≤H₀ ∧ ∀ h w hp wp : ℝ, 1<h → 0<w → 1<hp → 0<wp →
      let a:=log w/log h
      let b:=log wp/log hp
      let α:=log (hp/h)
      let β:=log (wp/w)
      a∈Icc lo hi → b∈Icc lo hi → H₀<log hp → |β-a*α|≤C →
      |log (allowance u hp wp/allowance u h w) -
        ((u a-a*deriv u a)*α+(1+deriv u a)*β)|<ε := by
  obtain ⟨H₀,nn,estimate⟩:=uniform_log_error hu lo hi C ε hC hε
  refine ⟨H₀,nn,?_⟩
  intro h w hp wp hh hw hp' hw' a b α β ha hb large bound
  have hpos : 0<h := lt_trans zero_lt_one hh
  have hpos' : 0<hp := lt_trans zero_lt_one hp'
  have hl := Real.log_pos hh
  have hl' := Real.log_pos hp'
  have hal : a*log h=log w := div_mul_cancel₀ _ hl.ne'
  have hbl : b*log hp=log wp := div_mul_cancel₀ _ hl'.ne'
  have hα : α=log hp-log h := Real.log_div hpos'.ne' hpos.ne'
  have hβ : β=log wp-log w := Real.log_div hw'.ne' hw.ne'
  have scale : log hp*(b-a)=β-a*α := by rw [hα,hβ];linear_combination hbl-hal
  have h1 := estimate a ha b hb (log hp) α β large scale bound
  have price (x y : ℝ) (hx : 0<x) (hy : 0<y) :
      log (allowance u x y)=log y+u (log y/log x)*log x := by
    rw [allowance,Real.log_mul hy.ne' (Real.rpow_pos_of_pos hx _).ne',Real.log_rpow hx]
  have pn (x y : ℝ) (hx : 0<x) (hy : 0<y) : allowance u x y ≠ 0 :=
    (mul_pos hy (Real.rpow_pos_of_pos hx _)).ne'
  rw [Real.log_div (pn hp wp hpos' hw') (pn h w hpos hw),price hp wp hpos' hw',price h w hpos hw]
  change |log wp+u b*log hp-(log w+u a*log h)-((u a-a*deriv u a)*α+(1+deriv u a)*β)|<ε
  convert h1 using 2
  rw [hα,hβ]
  ring

/-- A factor strictly greater than one absorbs rounding in both coordinates
of every type. The same threshold and log tolerance work for the whole
compact interval, and hence for every member of a fixed finite menu. -/
theorem uniform_menu_allowance {u : ℝ→ℝ} (hu : ContDiff ℝ 1 u) {lo hi C factor : ℝ}
    (interval : lo≤hi) (hC : 0≤C) (slack : 1<factor) :
    ∃ H₀ δ : ℝ, 0≤H₀ ∧ 0<δ ∧ ∀ h w hp wp T Y : ℝ,
      1<h → 0<w → 1<hp → 0<wp → 0<T → 0<Y →
      let a:=log w/log h
      let b:=log wp/log hp
      a∈Icc lo hi → b∈Icc lo hi → H₀<log hp →
      |log (wp/w)-a*log (hp/h)|≤C → |log (hp/h)-log T|<δ → |log (wp/w)-log Y|<δ →
      allowance u hp wp/allowance u h w < factor*T^(u a-a*deriv u a)*Y^(1+deriv u a) := by
  let V := fun a : ℝ=>u a-a*deriv u a
  let Z := fun a : ℝ=>1+deriv u a
  let K := fun a : ℝ=>|V a|+|Z a|
  have dv := hu.continuous_deriv (by decide)
  have cv : Continuous V := hu.continuous.sub (continuous_id.mul dv)
  have cz : Continuous Z := continuous_const.add dv
  obtain ⟨a₀,ha₀,maximal⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr interval)
    (cv.abs.add cz.abs).continuousOn
  have Bnonneg : 0≤K a₀ := add_nonneg (abs_nonneg _) (abs_nonneg _)
  let B:=K a₀+1
  have Bpos : 0<B := by dsimp [B];linarith
  let e:=log factor/2
  have ep : 0<e := by dsimp [e]; exact div_pos (log_pos slack) (by norm_num)
  obtain ⟨H₀,Hnn,test⟩:=uniform_allowance_ratio hu lo hi C e hC ep
  refine ⟨H₀,e/B,Hnn,div_pos ep Bpos,?_⟩
  intro h w hp wp T Y hh hw hh' hw' hT hY a b ha hb large shift nearT nearY
  let α:=log (hp/h)
  let β:=log (wp/w)
  have exactPrice:=test h w hp wp hh hw hh' hw' ha hb large shift
  change |log (allowance u hp wp/allowance u h w)-(V a*α+Z a*β)|<e at exactPrice
  have bounded : |V a|+|Z a|≤K a₀ := maximal ha
  have αerr : V a*(α-log T)≤|V a| * (e/B) := calc
    _≤|V a*(α-log T)|:=le_abs_self _
    _=|V a| * |α-log T|:=abs_mul ..
    _≤_:=mul_le_mul_of_nonneg_left nearT.le (abs_nonneg (V a))
  have βerr : Z a*(β-log Y)≤|Z a| * (e/B) := calc
    _≤|Z a*(β-log Y)|:=le_abs_self _
    _=|Z a| * |β-log Y|:=abs_mul ..
    _≤_:=mul_le_mul_of_nonneg_left nearY.le (abs_nonneg (Z a))
  have δnn : 0≤e/B := div_nonneg ep.le Bpos.le
  have combined : V a*(α-log T)+Z a*(β-log Y)≤e := calc
    _ ≤ (|V a|+|Z a|)*(e/B) := by
      rw [add_mul (|V a|) (|Z a|) (e/B)]
      exact add_le_add αerr βerr
    _ ≤ B*(e/B) := mul_le_mul_of_nonneg_right (bounded.trans (by dsimp [B];linarith)) δnn
    _ = e := by field_simp
  have posPrice (x y : ℝ) (hx : 0<x) (hy : 0<y) : 0<allowance u x y :=
    mul_pos hy (rpow_pos_of_pos hx _)
  have fac := lt_trans zero_lt_one slack
  apply (log_lt_log_iff (div_pos (posPrice _ _ (by linarith) hw') (posPrice _ _ (by linarith) hw))
    (mul_pos (mul_pos fac (rpow_pos_of_pos hT _)) (rpow_pos_of_pos hY _))).mp
  rw [log_mul (mul_pos fac (rpow_pos_of_pos hT _)).ne' (rpow_pos_of_pos hY _).ne',
    log_mul fac.ne' (rpow_pos_of_pos hT _).ne',log_rpow hT,log_rpow hY]
  change log (allowance u hp wp/allowance u h w) < log factor+V a*log T+Z a*log Y
  have ce := (abs_lt.mp exactPrice).2
  dsimp only [e] at combined ce
  linarith

/-- Along arbitrary format sequences, relative rounding errors that converge
to zero yield a uniform factor on the unsplit shorter calls. -/
theorem eventually_allowance {ι : Type*} {l : Filter ι} {u : ℝ→ℝ} (hu : ContDiff ℝ 1 u)
    {lo hi factor T Y : ℝ} (interval : lo≤hi) (slack : 1<factor) (hT : 0<T) (hY : 0<Y)
    (h w hp wp : ι→ℝ) (scale : Tendsto hp l atTop)
    (height : Tendsto (fun i => hp i/h i) l (𝓝 T))
    (payload : Tendsto (fun i => wp i/w i) l (𝓝 Y))
    (formats : ∀ᶠ i in l,1<h i ∧ 0<w i ∧ 0<wp i ∧
      log (w i)/log (h i)∈Icc lo hi ∧ log (wp i)/log (hp i)∈Icc lo hi) :
    ∀ᶠ i in l,let a:=log (w i)/log (h i);
      allowance u (hp i) (wp i)/allowance u (h i) (w i) <
        factor*T^(u a-a*deriv u a)*Y^(1+deriv u a) := by
  let M:=|lo|+|hi|
  let C:=(|log Y|+1)+M*(|log T|+1)
  have nn : 0≤C := by dsimp [C,M];positivity
  obtain ⟨H,δ,_,hδ,one⟩:=uniform_menu_allowance hu interval nn slack
  have α: Tendsto (fun i=>log (hp i/h i)) l (𝓝 (log T)) := height.log hT.ne'
  have β: Tendsto (fun i=>log (wp i/w i)) l (𝓝 (log Y)) := payload.log hY.ne'
  have rad : 0<min 1 δ := lt_min (by norm_num) hδ
  filter_upwards [formats,scale.eventually_gt_atTop 1,(tendsto_log_atTop.comp scale).eventually_gt_atTop H,
    (Metric.tendsto_nhds.mp α) _ rad,(Metric.tendsto_nhds.mp β) _ rad] with i fmt hp' bound dα dβ
  rw [Real.dist_eq] at dα dβ
  let a:=log (w i)/log (h i)
  have ha : |a|≤M := by
    obtain ⟨left,right⟩:=fmt.2.2.2.1
    exact abs_le.mpr ⟨by dsimp [a,M];linarith [neg_abs_le lo,abs_nonneg hi],
      by dsimp [a,M];linarith [le_abs_self hi,abs_nonneg lo]⟩
  have small (x y : ℝ) (d : |x-y|<min 1 δ) : |x|≤|y|+1 := by
    calc |x|=|(x-y)+y|:=by ring_nf
         _≤|x-y|+|y|:=abs_add_le ..
         _≤_:=by linarith [d.trans_le (min_le_left _ _)]
  have size : |log (wp i/w i)-a*log (hp i/h i)|≤C := calc
    _≤|log (wp i/w i)|+|a*log (hp i/h i)|:=abs_sub ..
    _ ≤ C := by
      rw [abs_mul]
      exact add_le_add (small _ _ dβ)
        (mul_le_mul ha (small _ _ dα) (abs_nonneg _) (by dsimp [M];positivity))
  exact one _ _ _ _ _ _ fmt.1 fmt.2.1 hp' fmt.2.2.1 hT hY fmt.2.2.2.1 fmt.2.2.2.2 bound size
    (dα.trans_le (min_le_right _ _)) (dβ.trans_le (min_le_right _ _))

/-- If the shorter types have total weighted size at most εn, their complete
amplified work is at most factor·C_amp·εn eventually. -/
theorem finite_menu_work {ι κ : Type*} [Fintype κ] {l : Filter ι} {u : ℝ→ℝ}
    (hu : ContDiff ℝ 1 u) {lo hi factor amp : ℝ} (interval : lo≤hi) (slack : 1<factor)
    (amp_nn : 0≤amp) (h w budget : ι→ℝ) (T Y : κ→ℝ) (hp wp S : κ→ι→ℝ)
    (types : ∀ k,0<T k ∧ 0<Y k)
    (heights : ∀ k,Tendsto (hp k) l atTop)
    (height : ∀ k,Tendsto (fun i=>hp k i/h i) l (𝓝 (T k)))
    (payload : ∀ k,Tendsto (fun i=>wp k i/w i) l (𝓝 (Y k)))
    (formats : ∀ k,∀ᶠ i in l,1<h i ∧ 0<w i ∧ 0<wp k i ∧
      log (w i)/log (h i)∈Icc lo hi ∧ log (wp k i)/log (hp k i)∈Icc lo hi)
    (counts : ∀ i k,0≤S k i)
    (pruned : ∀ᶠ i in l,let a:=log (w i)/log (h i);
      ∑ k,S k i*(T k^(u a-a*deriv u a)*Y k^(1+deriv u a))≤budget i) :
    ∀ᶠ i in l,∑ k,amp*S k i*(allowance u (hp k i) (wp k i)/allowance u (h i) (w i))≤
      amp*factor*budget i := by
  have menu:=Filter.eventually_all.mpr (fun k=>eventually_allowance hu interval slack (types k).1
    (types k).2 h w (hp k) (wp k) (heights k) (height k) (payload k) (formats k))
  filter_upwards [pruned,menu] with i bound per
  let a:=log (w i)/log (h i)
  let price:=fun k=>T k^(u a-a*deriv u a)*Y k^(1+deriv u a)
  change ∑ k,S k i*price k≤budget i at bound
  calc
    _≤∑ k,amp*factor*(S k i*price k):= by
      apply Finset.sum_le_sum
      intro k _
      have localPrice: allowance u (hp k i) (wp k i)/allowance u (h i) (w i)≤factor*price k := by
        simpa only [price,mul_assoc] using (per k).le
      exact (mul_le_mul_of_nonneg_left localPrice (mul_nonneg amp_nn (counts i k))).trans_eq (by ring)
    _=amp*factor*∑k,S k i*price k:=by rw [Finset.mul_sum]
    _≤_:=mul_le_mul_of_nonneg_left bound (mul_nonneg amp_nn (by linarith))

end
end Hierarchy.TaggedWidthProfile

end OAI
