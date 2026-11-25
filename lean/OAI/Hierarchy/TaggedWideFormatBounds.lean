import OAI.Hierarchy.TaggedWidthSlices
import OAI.Hierarchy.TaggedWidthSliceLimit
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OAI
/-! # Uniform integer bounds for every balanced shorter-call slice -/

namespace Hierarchy.Tagged
open Filter Real Finset TaggedWidthSlices TaggedWidthProfile
open scoped Topology BigOperators

/-- Above the wide-parent threshold, the child payload eventually exceeds the
child address length. This also covers the branch with a single uncut slice. -/
private theorem single_type_formats {ι : Type*} {l : Filter ι} {κ A T Y : ℝ}
    (hk : 0<κ) (hA : 1<A) (ht : 0<T) (short : T≤1/2) (hy : 0<Y)
    (h w hp wp : ι→ℕ) (large : Tendsto (fun i=>(hp i:ℝ)) l atTop)
    (height : Tendsto (fun i=>(hp i:ℝ)/h i) l (𝓝 T))
    (payload : Tendsto (fun i=>(wp i:ℝ)/w i) l (𝓝 Y))
    (parents : ∀ᶠ i in l, 1<(h i:ℝ) ∧ 0<w i ∧
      Real.logb (h i) (w i)∈Set.Icc (1+κ) A) :
    ∃ B : ℕ, ∀ᶠ i in l,
      let C := ⌊(hp i:ℝ)^A⌋₊
      3*hp i ≤ 2*h i ∧ count (wp i) C ≤ B ∧
      ∀ j,2≤hp i ∧ hp i≤width (wp i) C j ∧ (width (wp i) C j:ℝ)≤(hp i:ℝ)^A := by
  have hA0 := zero_lt_one.trans hA
  have parent_positive : ∀ᶠ i in l,0<(h i:ℝ) :=
    parents.mono fun _ z => zero_lt_one.trans z.1
  obtain ⟨B,limit⟩ := eventually_slice_count hA0 ht (show 0≤Y+1 by linarith)
    (fun i=>(h i:ℝ)) (fun i=>(hp i:ℝ)) large height parent_positive
  refine ⟨B,?_⟩
  filter_upwards [parents,limit,large.eventually_gt_atTop 1,
    ((tendsto_rpow_atTop hk).comp large).eventually_gt_atTop (2/Y),
    height.eventually (eventually_lt_nhds (show T<2/3 by linarith)),
    payload.eventually (eventually_gt_nhds (show Y/2<Y by linarith)),
    payload.eventually (eventually_lt_nhds (show Y<Y+1 by linarith)),
    large.eventually (eventually_slice_formats 1 A zero_le_one hA)] with i parent countBound child many hRatio yLow yHigh slices
  intro C
  have hpos := zero_lt_one.trans parent.1
  have wpos : 0<(w i:ℝ) := Nat.cast_pos.mpr parent.2.1
  have upperW := (logb_le_iff_le_rpow parent.1 wpos).mp parent.2.2.2
  have lowerW := (le_logb_iff_rpow_le parent.1 wpos).mp parent.2.2.1
  have shortR := (div_lt_iff₀ hpos).mp hRatio
  have shrink : 3*hp i≤2*h i := by
    exact_mod_cast (show 3*(hp i:ℝ)≤2*(h i:ℝ) by linarith)
  have below : (hp i:ℝ)≤h i := by linarith
  change 2/Y<(hp i:ℝ)^κ at many
  have growth := many.trans_le (rpow_le_rpow (Nat.cast_nonneg _) below hk.le)
  rw [rpow_add hpos,rpow_one] at lowerW
  have enough := (div_lt_iff₀ hy).mp growth
  have lhs := (lt_div_iff₀ wpos).mp yLow
  have tall : (hp i:ℝ)≤wp i := by
    nlinarith [mul_le_mul_of_nonneg_left lowerW hy.le,
      mul_le_mul_of_nonneg_left enough.le hpos.le]
  have wpp : 0<wp i := by exact_mod_cast ((zero_lt_one.trans child).trans_le tall)
  have pos : 0<C := Nat.floor_pos.mpr (one_le_rpow child.le hA0.le)
  have y : (wp i:ℝ)≤(Y+1)*w i := ((div_lt_iff₀ wpos).mp yHigh).le
  have bc : wp i≤⌈(Y+1)*w i⌉₊ := by exact_mod_cast y.trans (Nat.le_ceil _)
  have capCount : wp i ≤ C*B := bc.trans (countBound (w i) upperW)
  refine ⟨shrink,count_le pos (by simpa only [Nat.mul_comm B C] using capCount),?_⟩
  intro j
  have bound := width_le pos j
  have upper : (width (wp i) C j:ℝ)≤(hp i:ℝ)^A := (Nat.cast_le.mpr bound).trans
    (Nat.floor_le (rpow_nonneg (Nat.cast_nonneg _) _))
  have childNat : 1<hp i := by exact_mod_cast child
  refine ⟨by omega,?_,upper⟩
  by_cases under : wp i≤C
  · have one : count (wp i) C=1 := le_antisymm
      (count_le pos (by simpa using under)) (count_pos wpp pos)
    have same : width (wp i) C j=wp i := by simp [width,one,Nat.mod_one]
    rw [same]
    exact_mod_cast tall
  · have inPlateau := (slices (width (wp i) C j) bound
      (cap_le_twice_succ_width pos (le_of_not_ge under) j)).1
    have pp : 0<(width (wp i) C j:ℝ) := Nat.cast_pos.mpr (width_pos wpp pos j)
    have part : (hp i:ℝ)^(1:ℝ) ≤ width (wp i) C j :=
      (le_logb_iff_rpow_le child pp).mp inPlateau
    rw [rpow_one] at part
    exact_mod_cast part

/-- One bound controls the slice count across the entire finite type menu. -/
theorem wide_format_bounds {ι τ : Type*} [Fintype τ] {l : Filter ι} {κ A : ℝ}
    (hk : 0<κ) (hA : 1<A) (h w : ι→ℕ) (hp wp : τ→ι→ℕ) (T Y : τ→ℝ)
    (types : ∀ k, 0<T k ∧ T k≤1/2 ∧ 0<Y k)
    (large : ∀ k,Tendsto (fun i=>(hp k i:ℝ)) l atTop)
    (height : ∀ k,Tendsto (fun i=>(hp k i:ℝ)/h i) l (𝓝 (T k)))
    (payload : ∀ k,Tendsto (fun i=>(wp k i:ℝ)/w i) l (𝓝 (Y k)))
    (parents : ∀ᶠ i in l, 1<(h i:ℝ) ∧ 0<w i ∧
      Real.logb (h i) (w i)∈Set.Icc (1+κ) A) :
    ∃ B : ℕ, ∀ᶠ i in l, ∀ k,
      let C := ⌊(hp k i:ℝ)^A⌋₊
      3*hp k i≤2*h i ∧ count (wp k i) C≤B ∧
      ∀ j,2≤hp k i ∧ hp k i≤width (wp k i) C j ∧ (width (wp k i) C j:ℝ)≤(hp k i:ℝ)^A := by
  classical
  choose B bounded using fun k => single_type_formats hk hA (types k).1 (types k).2.1 (types k).2.2
    h w (hp k) (wp k) (large k) (height k) (payload k) parents
  refine ⟨∑ k,B k,?_⟩
  filter_upwards [Filter.eventually_all.mpr bounded] with i all k
  exact ⟨(all k).1,(all k).2.1.trans (single_le_sum (fun j _=>Nat.zero_le (B j)) (mem_univ k)),
    (all k).2.2⟩

end Hierarchy.Tagged

end OAI
