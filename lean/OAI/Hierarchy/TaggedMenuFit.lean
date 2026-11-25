import OAI.Hierarchy.TaggedWidthInduction
import OAI.Hierarchy.TaggedWidthSliceLimit
import OAI.Hierarchy.TaggedWidthSlices
import OAI.Hierarchy.TaggedWidthVariation

namespace OAI
/-! # Integer shorter-call work for the exposed tagged approximation -/

noncomputable section
namespace Hierarchy.Tagged

open Filter Real
open scoped Topology BigOperators
open TaggedWidthProfile

/-- Fraction of all parent slots occupied by copies of a shorter format. -/
def slotFraction (h child copies : ℕ) : ℝ :=
  (copies : ℝ) * (2 : ℝ) ^ child / (2 : ℝ) ^ h

theorem unitWork_eq_allowance (u : ℝ → ℝ) (h w : ℕ) :
    unitWork u h w = (2 : ℝ)^h * allowance u h w := by
  unfold unitWork work allowance Real.logb
  ring

/-- Dividing a shorter payload into the actual balanced integer slices
preserves its total unit work. Below capacity there is a single slice. -/
theorem sum_balanced_unitWork (u : ℝ → ℝ) {start : ℝ} {h w C : ℕ}
    (flat : ∀ a, start ≤ a → u a = u start) (hh : 1 < (h : ℝ))
    (hw : 0 < w) (hC : 0 < C)
    (formats : ∀ v : ℕ, v ≤ C → C ≤ 2*(v+1) → start ≤ log (v:ℝ) / log (h:ℝ)) :
    (∑ j : Fin (TaggedWidthSlices.count w C), unitWork u h (TaggedWidthSlices.width w C j)) =
      unitWork u h w := by
  by_cases small : w ≤ C
  · have one : TaggedWidthSlices.count w C = 1 :=
      le_antisymm (TaggedWidthSlices.count_le hC (by simpa using small)) (TaggedWidthSlices.count_pos hw hC)
    have size (j : Fin (TaggedWidthSlices.count w C)) : TaggedWidthSlices.width w C j = w := by
      simp [TaggedWidthSlices.width,one]; omega
    simp only [size, Finset.sum_const, Finset.card_univ, Fintype.card_fin, one, one_nsmul]
  · have wide : C ≤ w := (lt_of_not_ge small).le
    have vp := (formats C le_rfl (by omega)).trans (div_le_div_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast hC) (by exact_mod_cast wide : (C:ℝ) ≤ w)) (Real.log_pos hh).le)
    have add := allowance_split Finset.univ (fun j => (TaggedWidthSlices.width w C j : ℝ))
      u h w start flat (by exact_mod_cast TaggedWidthSlices.sum_width (w:=w) hC) vp
      (fun j _ => formats _ (TaggedWidthSlices.width_le hC j) (TaggedWidthSlices.cap_le_twice_succ_width hC wide j))
    simp only [unitWork_eq_allowance,← Finset.mul_sum,add]

/-- A fixed multiplicative change in the height and payload leaves the width
exponent in a common compact interval, even when the parent width varies. -/
theorem eventually_menu_width {ι : Type*} {l : Filter ι} {lo hi T Y η : ℝ}
    (hT : 0 < T) (hY : 0 < Y) (hη : 0 < η) (h w hp wp : ι → ℝ)
    (large : Tendsto hp l atTop) (height : Tendsto (fun i => hp i/h i) l (𝓝 T))
    (payload : Tendsto (fun i => wp i/w i) l (𝓝 Y))
    (formats : ∀ᶠ i in l, 1 < h i ∧ 0 < w i ∧ 0 < wp i ∧
      logb (h i) (w i) ∈ Set.Icc lo hi) :
    ∀ᶠ i in l, logb (hp i) (wp i) ∈ Set.Icc (lo-η) (hi+η) := by
  let M := |lo|+|hi|
  let C := (|log Y|+1)+M*(|log T|+1)
  have α := height.log hT.ne'
  have β := payload.log hY.ne'
  filter_upwards [formats,large.eventually_gt_atTop 1,
    (tendsto_log_atTop.comp large).eventually_gt_atTop (C/η),
    (Metric.tendsto_nhds.mp α) 1 zero_lt_one,(Metric.tendsto_nhds.mp β) 1 zero_lt_one]
    with i fmt short full nearT nearY
  rw [Real.dist_eq] at nearT nearY
  let a := logb (h i) (w i)
  let b := logb (hp i) (wp i)
  have aBound : |a| ≤ M := abs_le.mpr
    ⟨by dsimp [a,M];linarith [fmt.2.2.2.1,neg_abs_le lo,abs_nonneg hi],
     by dsimp [a,M];linarith [fmt.2.2.2.2,le_abs_self hi,abs_nonneg lo]⟩
  have bounded {x y : ℝ} (d : |x-y| < 1) : |x| ≤ |y|+1 := calc
    _ = |(x-y)+y| := by ring_nf
    _ ≤ |x-y|+|y| := abs_add_le ..
    _ ≤ _ := by linarith
  have budget : |log (wp i/w i)-a*log (hp i/h i)| ≤ C := calc
    _ ≤ |log (wp i/w i)| + |a*log (hp i/h i)| := abs_sub ..
    _ ≤ _ := by
      rw [abs_mul]
      exact add_le_add (bounded nearY)
        (mul_le_mul aBound (bounded nearT) (abs_nonneg _) (by dsimp [M];positivity))
  have d₁ : a*log (h i)=log (w i) := div_mul_cancel₀ _ (Real.log_pos fmt.1).ne'
  have d₂ : b*log (hp i)=log (wp i) := div_mul_cancel₀ _ (Real.log_pos short).ne'
  have eq : log (hp i)*(b-a)=log (wp i/w i)-a*log (hp i/h i) := by
    rw [log_div fmt.2.2.1.ne' fmt.2.1.ne',log_div (zero_lt_one.trans short).ne'
      (zero_lt_one.trans fmt.1).ne']
    linear_combination d₂-d₁
  rw [←eq,abs_mul,abs_of_pos (Real.log_pos short)] at budget
  change C/η < log (hp i) at full
  have tight : |b-a| < η := by
    have room := (div_lt_iff₀ hη).mp full
    by_contra! wide
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_left wide (Real.log_pos short).le)) (budget.trans_lt room)
  have near := abs_lt.mp tight
  change lo-η ≤ b ∧ b ≤ hi+η
  have bounds : a ∈ Set.Icc lo hi := fmt.2.2.2
  exact ⟨by linarith [near.1,bounds.1], by linarith [near.2,bounds.2]⟩

/-- The complete finite menu is charged in physical copies. The pruning
bound counts slots, so each child's copy count is multiplied by its own
power of two before division by the parent's number of slots. The conclusion
uses the real integer slice sizes in each of these copies. -/
theorem eventually_menu_fit {ι κ : Type*} [Fintype κ] {l : Filter ι} {u : ℝ → ℝ}
    (smooth : ContDiff ℝ 1 u) {lo hi start cap amp ε : ℝ} (interval : lo ≤ hi)
    (hs : 0 ≤ start) (gap : start < cap) (flat : ∀ a, start ≤ a → u a = u start)
    (amplifier : 0 ≤ amp) (small : amp*ε ≤ 1/4)
    (h w : ι → ℕ) (hp wp copies : κ → ι → ℕ) (T Y : κ → ℝ)
    (types : ∀ k, 0 < T k ∧ 0 < Y k)
    (large : ∀ k, Tendsto (fun i => (hp k i : ℝ)) l atTop)
    (height : ∀ k, Tendsto (fun i => (hp k i : ℝ) / h i) l (𝓝 (T k)))
    (payload : ∀ k, Tendsto (fun i => (wp k i : ℝ) / w i) l (𝓝 (Y k)))
    (parents : ∀ᶠ i in l, 1 < (h i : ℝ) ∧ 0 < w i ∧ logb (h i) (w i) ∈ Set.Icc lo hi)
    (positive : ∀ k, ∀ᶠ i in l, 0 < wp k i)
    (pruned : ∀ᶠ i in l, let a := logb (h i) (w i);
      ∑ k, slotFraction (h i) (hp k i) (copies k i) *
        (T k ^ (u a-a*deriv u a) * Y k ^ (1+deriv u a)) ≤ ε) :
    ∀ᶠ i in l, ∑ k, (amp*(copies k i : ℝ)) *
      (∑ j : Fin (TaggedWidthSlices.count (wp k i) ⌊(hp k i : ℝ)^cap⌋₊),
        unitWork u (hp k i) (TaggedWidthSlices.width (wp k i) ⌊(hp k i : ℝ)^cap⌋₊ j)) ≤
        unitWork u (h i) (w i) / 2 := by
  let S := fun k i => slotFraction (h i) (hp k i) (copies k i)
  have formats (k : κ) := eventually_menu_width (η:=1) (types k).1 (types k).2 zero_lt_one
    (fun i => (h i : ℝ)) (fun i => (w i : ℝ)) (fun i => (hp k i : ℝ)) (fun i => (wp k i : ℝ))
    (large k) (height k) (payload k) (by
      filter_upwards [parents,positive k] with i p q
      exact ⟨p.1,by exact_mod_cast p.2.1,by exact_mod_cast q,p.2.2⟩)
  have wider : lo-1 ≤ hi+1 := by linarith
  have charged := finite_menu_work (l:=l) (factor:=2) (amp:=amp) smooth wider (by norm_num) amplifier
    (fun i => ↑(h i)) (fun i => ↑(w i)) (fun _ => ε) T Y
    (fun k i => ↑(hp k i)) (fun k i => ↑(wp k i)) S types large height payload
    (fun k => by
      filter_upwards [parents,positive k,formats k] with i p q f
      exact ⟨p.1,by exact_mod_cast p.2.1,by exact_mod_cast q,
        Set.Icc_subset_Icc (by linarith) (by linarith) p.2.2,f⟩)
    (fun i k => by dsimp [S,slotFraction]; positivity) pruned
  have slices (k : κ) : ∀ᶠ i in l,
      (∑ j : Fin (TaggedWidthSlices.count (wp k i) ⌊(hp k i : ℝ)^cap⌋₊),
        unitWork u (hp k i) (TaggedWidthSlices.width (wp k i) ⌊(hp k i : ℝ)^cap⌋₊ j)) =
        unitWork u (hp k i) (wp k i) := by
    filter_upwards [positive k, (large k).eventually_gt_atTop 1,
      (large k).eventually (eventually_slice_formats start cap hs gap)] with i fmt child part
    exact sum_balanced_unitWork u flat child fmt (Nat.floor_pos.mpr
      (Real.one_le_rpow child.le (hs.trans gap.le))) (fun v a b => (part v a b).1)
  filter_upwards [parents, charged, Filter.eventually_all.mpr slices] with i p budget conserve
  simp only [conserve]
  let N := (2 : ℝ) ^ h i
  let W := allowance u (h i) (w i)
  have npos : 0 < N := by dsimp [N]; positivity
  have wpos : 0 < W := mul_pos (by exact_mod_cast p.2.1)
    (Real.rpow_pos_of_pos (zero_lt_one.trans p.1) _)
  let ratio := fun k => allowance u (hp k i) (wp k i) / W
  change ∑ k, amp*S k i*ratio k ≤ amp*2*ε at budget
  have term_eq (k : κ) : (amp*(copies k i : ℝ))*unitWork u (hp k i) (wp k i) =
      (amp*S k i*ratio k)*(N*W) := by
    rw [unitWork_eq_allowance]
    change _ = (amp*((copies k i : ℝ)*(2:ℝ)^hp k i/N)*(allowance u (hp k i) (wp k i)/W))*(N*W)
    field_simp [npos.ne', wpos.ne']
  simp_rw [term_eq]
  rw [← Finset.sum_mul, unitWork_eq_allowance]
  change _ ≤ N*W/2
  have scaled := mul_le_mul_of_nonneg_right budget (mul_pos npos wpos).le
  have half : amp*2*ε ≤ 1/2 := by linarith
  have last := mul_le_mul_of_nonneg_right half (mul_pos npos wpos).le
  linarith only [scaled,last]

/-- The polynomial-log overhead and the width-one control terms fit the
other half of the real parent allowance uniformly in integer formats. -/
theorem eventually_fixed_work {ι : Type*} {l : Filter ι} {s A power control K : ℝ}
    {u : ℝ → ℝ} (profile : Admissible s u) (hcontrol : control < u 1) (hK : 0 < K)
    (h w : ι → ℕ) (fixed : ι → ℝ) (large : Tendsto (fun i => (h i : ℝ)) l atTop)
    (format : ∀ᶠ i in l, 1 < (h i : ℝ) ∧ 0 < w i ∧ logb (h i) (w i) ∈ Set.Icc 1 A)
    (bill : ∀ᶠ i in l, fixed i ≤ K*((2:ℝ)^h i*w i*(log (h i))^power +
      (2:ℝ)^h i*(h i:ℝ)^(1+control)*(log (h i))^power)) :
    ∀ᶠ i in l, fixed i ≤ unitWork u (h i) (w i)/2 := by
  have tol : 0 < 1/(2*K) := by positivity
  filter_upwards [format,bill,large.eventually (profile.ordinary_control_work A power hcontrol tol)]
    with i fmt pay bound
  have test := bound _ fmt.2.2 ((2:ℝ)^h i) (by positivity)
  have eq := Real.rpow_logb (zero_lt_one.trans fmt.1) fmt.1.ne' (by exact_mod_cast fmt.2.1 : 0<(w i:ℝ))
  rw [eq] at test
  have both := pay.trans (mul_le_mul_of_nonneg_left test hK.le)
  change _ ≤ (2:ℝ)^h i*w i*(h i:ℝ)^u (logb (h i) (w i))/2
  refine both.trans_eq ?_
  field_simp [hK.ne']

/-- Reindex the child calls in the physical assembly by their shorter type
and payload slice. An upper bound on the actual multiplicities suffices. -/
theorem ShorterCalls.fitsWork_of_menu {F τ : Type*} [Field F] [Fintype τ]
    {k h w : ℕ} {A C amp : ℝ} (u : ℝ → ℝ) (r : ShorterCalls F k h w A C)
    (slices height copies : τ → ℕ) (payload : (t : τ) → Fin (slices t) → ℕ)
    (index : Fin r.types ≃ Σ t, Fin (slices t))
    (height_eq : ∀ i, r.height i = height (index i).1)
    (width_eq : ∀ i, r.payload i = payload (index i).1 (index i).2)
    (multiplicity_le : ∀ i, (r.multiplicity i : ℝ) ≤ amp * (copies (index i).1 : ℝ))
    (fixed : r.fixedWork ≤ unitWork u h w / 2)
    (budget : ∑ t, (amp*(copies t : ℝ)) * (∑ j, unitWork u (height t) (payload t j))
      ≤ unitWork u h w / 2) : FitsWork u r := by
  classical
  let charge := fun x : Σ t, Fin (slices t) =>
    (amp*(copies x.1 : ℝ)) * unitWork u (height x.1) (payload x.1 x.2)
  refine ⟨fixed,?_⟩
  calc
    _ ≤ ∑ i, charge (index i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [height_eq i,width_eq i]
      apply mul_le_mul_of_nonneg_right (multiplicity_le i)
      unfold unitWork work
      positivity
    _ = ∑ x, charge x := index.sum_comp charge
    _ = ∑ t, (amp*(copies t : ℝ)) * (∑ j, unitWork u (height t) (payload t j)) := by
      rw [Fintype.sum_sigma]
      simp only [charge, Finset.mul_sum]
    _ ≤ _ := budget

end Hierarchy.Tagged

end
end OAI
