import OAI.Hierarchy.TaggedShorterChoice
import OAI.Hierarchy.TaggedWidthProfile
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace OAI
/-! # Numerical geometry and prices of the actual paired shorter-call banks -/

namespace Hierarchy.TaggedShorterBudget

open Real Set Finset Filter
open scoped Topology BigOperators
noncomputable section

/-- Price of one installed dyadic type at parent width exponent a. -/
def typeFraction (u : ℝ→ℝ) (δ ξ a : ℝ) (i : ℕ×ℕ) :=
  fraction ξ (u a+a*(-deriv u a)-δ) (1-(-deriv u a)-δ) i.1 i.2

/-- Two equal-width tagged calls for each of the whole modules. -/
def bankCopies (c : ℝ) (h t : ℕ) : ℕ := 2*⌈6*c*(2:ℝ)^h/(2:ℝ)^t⌉₊

theorem bank_slots (c : ℝ) (h t : ℕ) :
    (bankCopies c h t:ℝ)*(2:ℝ)^t =
      ((2*installed c ((2:ℝ)^h) (2^t):ℕ):ℝ) := by
  simp [bankCopies,installed,Nat.cast_mul,mul_assoc]

/-- Subtracting a fixed dyadic offset d from the supergroup address preserves
the scale limit. Ceiling the requested width preserves the payload ratio. -/
theorem bank_limits {ι : Type*} {l : Filter ι} {T Y : ℝ} (hT : 0<T) (hY : 0≤Y)
    (h w g : ι→ℕ) (d : ℕ) (high : Tendsto (fun i=>(h i:ℝ)) l atTop)
    (wide : Tendsto (fun i=>(w i:ℝ)) l atTop)
    (geometry : Tendsto (fun i=>(g i:ℝ)/h i) l (𝓝 T)) :
    Tendsto (fun i=>((g i-d:ℕ):ℝ)) l atTop ∧
    Tendsto (fun i=>((g i-d:ℕ):ℝ)/h i) l (𝓝 T) ∧
    Tendsto (fun i=>(⌈Y*w i⌉₊:ℝ)/w i) l (𝓝 Y) := by
  have grow := high.num hT geometry
  have tiny : Tendsto (fun i=>(d:ℝ)/(h i:ℝ)) l (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      (tendsto_const_nhds (x := (d:ℝ))).mul (tendsto_inv_atTop_zero.comp high)
  have cut : Tendsto (fun i=>((g i-d:ℕ):ℝ)/h i) l (𝓝 T) := by
    have sub := geometry.sub tiny
    rw [sub_zero] at sub
    apply sub.congr'
    filter_upwards [grow.eventually_ge_atTop (d:ℝ)] with i ge
    rw [Nat.cast_sub (by exact_mod_cast ge : d≤g i),sub_div]
  exact ⟨high.num hT cut,cut,(tendsto_nat_ceil_mul_div_atTop hY).comp wide⟩

/-- Because t/h tends to a positive number at most one half, 2^t eventually
fits even an arbitrarily small fixed fraction of the parent slots. -/
theorem eventually_bank_small {ι : Type*} {l : Filter ι} {T c : ℝ}
    (hT : 0<T) (small : T≤1/2) (hc : 0<c) (h t : ι→ℕ)
    (high : Tendsto (fun i=>(h i:ℝ)) l atTop)
    (ratio : Tendsto (fun i=>(t i:ℝ)/h i) l (𝓝 T)) :
    ∀ᶠ i in l, ((2^t i:ℕ):ℝ)≤c*(2:ℝ)^h i := by
  obtain ⟨d,hd⟩ := exists_pow_lt_of_lt_one hc (show (1/2:ℝ)<1 by norm_num)
  filter_upwards [(high.num hT ratio).eventually_ge_atTop (2*(d:ℝ)),
    high.eventually_gt_atTop 0,ratio.eventually (eventually_lt_nhds (show T<2/3 by linarith))]
    with i late positive near
  have offset : t i+d≤h i := by
    have hr := (div_lt_iff₀ positive).mp near
    exact_mod_cast (show (t i:ℝ)+d≤h i by linarith)
  have pp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) offset
  rw [pow_add] at pp
  have cancel : (2:ℝ)^d*(1/2:ℝ)^d=1 := by rw [←mul_pow]; norm_num
  push_cast
  calc
    (2:ℝ)^t i = ((2:ℝ)^t i*2^d)*(1/2:ℝ)^d := by rw [mul_assoc,cancel,mul_one]
    _ ≤ (2:ℝ)^h i*(1/2:ℝ)^d := mul_le_mul_of_nonneg_right pp (by positivity)
    _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hd.le (show 0≤(2:ℝ)^h i by positivity)

/-- Continuity on the parent interval bounds every fixed type's bank fraction
uniformly, including in the transition to the profile plateau. -/
theorem typeFraction_bounded {s : ℝ} {u : ℝ→ℝ} (profile : TaggedWidthProfile.Admissible s u)
    (A δ ξ : ℝ) (i : ℕ×ℕ) :
    ∃ U : ℝ,0<U ∧ ∀ a∈Icc 1 A,typeFraction u δ ξ a i≤U := by
  have der := profile.smooth.continuous_deriv (by simp)
  have e : Continuous (fun a=>u a+a*(-deriv u a)-δ) :=
    (profile.smooth.continuous.add (continuous_id.mul der.neg)).sub continuous_const
  have f : Continuous (fun a=>1-(-deriv u a)-δ) :=
    (continuous_const.sub der.neg).sub continuous_const
  have he := (continuous_const_rpow (dyadic_pos i.1).ne').comp e
  have hf := (continuous_const_rpow (dyadic_pos i.2).ne').comp f
  have cont : Continuous (fun a=>typeFraction u δ ξ a i) :=
    continuous_const.div (he.mul hf) (fun a=>mul_ne_zero (rpow_pos_of_pos (dyadic_pos _) _).ne'
      (rpow_pos_of_pos (dyadic_pos _) _).ne')
  obtain ⟨K,bound⟩ := (isCompact_Icc (a:=(1:ℝ)) (b:=A)).bddAbove_image cont.continuousOn
  exact ⟨max 1 K,zero_lt_one.trans_le (le_max_left _ _),fun a ha=>
    (bound (mem_image_of_mem _ ha)).trans (le_max_right _ _)⟩

/-- On a fixed dyadic ray the number of physical copies is positive and its
binary logarithm is at most the square of the shorter address eventually. -/
theorem eventually_bank_log {ι : Type*} {l : Filter ι} {T U : ℝ}
    (hT : 0<T) (hU : 0<U) (h t : ι→ℕ) (c : ι→ℝ)
    (high : Tendsto (fun i=>(h i:ℝ)) l atTop)
    (ratio : Tendsto (fun i=>(t i:ℝ)/h i) l (𝓝 T))
    (bounded : ∀ᶠ i in l,0<c i ∧ c i≤U) :
    ∀ᶠ i in l,0<bankCopies (c i) (h i) (t i) ∧
      logb 2 (bankCopies (c i) (h i) (t i)) ≤ (t i:ℝ)^(2:ℝ) := by
  let D := 12*U+2
  have hD : 0<D := by dsimp [D]; positivity
  have tall := high.num hT ratio
  filter_upwards [bounded,high.eventually_gt_atTop 0,tall.eventually_ge_atTop (logb 2 D),
    tall.eventually_ge_atTop (2/T+1),ratio.eventually (eventually_gt_nhds (show T/2<T by linarith))]
    with i coeff hh large linear scale
  let n := (2:ℝ)^h i
  let K := (2:ℝ)^t i
  have n1 : 1≤n := one_le_pow₀ (by norm_num)
  have K1 : 1≤K := one_le_pow₀ (by norm_num)
  have cj : 0<c i := coeff.1
  have raw : 0<6*c i*n/K := by dsimp [n,K]; positivity
  have cp : 0<bankCopies (c i) (h i) (t i) := Nat.mul_pos (by decide) (Nat.ceil_pos.mpr raw)
  have upper : (bankCopies (c i) (h i) (t i):ℝ)≤D*n := by
    have q := Nat.ceil_lt_add_one raw.le
    have tail := div_le_self (show 0≤6*c i*n by positivity) K1
    change ((2*⌈6*c i*n/K⌉₊:ℕ):ℝ)≤D*n
    push_cast
    dsimp only [D]
    nlinarith [mul_le_mul_of_nonneg_right coeff.2 (zero_le_one.trans n1)]
  have price := logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (Nat.cast_pos.mpr cp) upper
  have logn : logb 2 n = h i := by
    change logb 2 ((2:ℝ)^h i) = _
    rw [logb_pow,logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one]
  rw [logb_mul hD.ne' (zero_lt_one.trans_le n1).ne',logn] at price
  have near := (lt_div_iff₀ hh).mp scale
  have H : (h i:ℝ)≤2/T*(t i:ℝ) := by
    rw [div_mul_eq_mul_div,le_div_iff₀ hT]
    linarith
  refine ⟨cp,?_⟩
  rw [rpow_two]
  nlinarith [mul_le_mul_of_nonneg_right linear (Nat.cast_nonneg (t i) : (0:ℝ)≤t i)]

/-- Normalized slot fractions and the per-type lower bound count exactly both
paired calls in each purchased bank. -/
theorem Choice.bank_menu {u : ℝ→ℝ} {A ε p q Q σ L δ η ξ : ℝ}
    (choice : Choice u A (ε/2) p q Q σ L δ η ξ) {a : ℝ} (ha : a∈Icc 1 A)
    (h : ℕ) (menu : Finset (ℕ×ℕ)) (t : ℕ×ℕ→ℕ)
    (small : ∀ i∈menu,((2^t i:ℕ):ℝ)≤3*ξ*(2:ℝ)^h) :
    let c := typeFraction u δ ξ a
    let cp := fun i => bankCopies (c i) h (t i)
    (∀ i∈menu,36*ξ*(2:ℝ)^h≤(cp i:ℝ)*2^t i) ∧
    ∑ i∈menu,((cp i:ℝ)*2^t i/(2:ℝ)^h)*
      (dyadic i.1^(u a-a*deriv u a)*dyadic i.2^(1+deriv u a))≤ε := by
  intro c cp
  obtain ⟨low,total⟩ := choice.paired_menu ha (show 0≤(2:ℝ)^h by positivity) menu
    (fun i=>2^t i) (fun i hi=>⟨by positivity,small i hi⟩)
  refine ⟨fun i hi=>?_,?_⟩
  · rw [show (cp i:ℝ)*(2:ℝ)^t i=((2*installed (c i) ((2:ℝ)^h) (2^t i):ℕ):ℝ)
      from bank_slots _ _ _]
    exact low i hi
  · apply le_of_mul_le_mul_right (a := (2:ℝ)^h) _ (by positivity)
    rw [Finset.sum_mul]
    apply le_trans _ total
    apply le_of_eq (sum_congr rfl ?_)
    intro i hi
    let price := dyadic i.1^(u a-a*deriv u a)*dyadic i.2^(1+deriv u a)
    change (_/(2:ℝ)^h)*price*2^h = _
    rw [div_mul_eq_mul_div,div_mul_cancel₀ _ (show (2:ℝ)^h≠0 by positivity)]
    have E : u a-a*deriv u a=u a+a*(-deriv u a) := by ring
    have F : 1+deriv u a=1-(-deriv u a) := by ring
    dsimp only [price]
    rw [E,F,show (cp i:ℝ)*(2:ℝ)^t i = ((2*installed (c i) ((2:ℝ)^h) (2^t i):ℕ):ℝ) from bank_slots _ _ _]
    rfl

end
end Hierarchy.TaggedShorterBudget

end OAI
