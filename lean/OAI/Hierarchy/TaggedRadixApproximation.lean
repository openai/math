import OAI.Hierarchy.TaggedGapScale
import OAI.Hierarchy.TaggedRadixScales
import OAI.Hierarchy.TaggedRadixPrice

namespace OAI
/-! # Specialization of exposed approximations to both radix grids -/

namespace Hierarchy.Tagged.Radix

open Filter

/-- Ceiling division uses the available pass-index bits and incurs exactly
the pass exponent used in the total price. -/
theorem GridScales.pass_count {a B : ℝ} {h : ℕ} (g : GridScales a B h) (ha : 1 ≤ a) :
    let p := ⌈(h:ℝ)/(digitBits a h:ℝ)⌉₊
    p ≤ 2^(passBits h) ∧ (p:ℝ) ≤ 3*(h:ℝ)^(1-1/a) := by
  dsimp only
  have one : (1:ℝ) ≤ h := by exact_mod_cast g.positive
  have digits := g.digit_room
  have floorOne : (1:ℝ) ≤ digitBits a h := by exact_mod_cast (show 1 ≤ digitBits a h by omega)
  have ratio : (h:ℝ)/(digitBits a h:ℝ) ≤ h := div_le_self (by positivity) floorOne
  constructor
  · exact (Nat.ceil_le.mpr ratio).trans ((Nat.le_succ h).trans g.passes)
  · exact pass_count_factor one ha g.digit_lo (Nat.ceil_lt_add_one (by positivity)).le

/-- The selected number of passes reads every bit of an h-bit key. -/
theorem GridScales.pass_cover {a B : ℝ} {h : ℕ} (g : GridScales a B h) :
    h ≤ ⌈(h:ℝ)/(digitBits a h:ℝ)⌉₊*digitBits a h := by
  have digits := g.digit_room
  have positive : (0:ℝ) < digitBits a h := by exact_mod_cast (show 0 < digitBits a h by omega)
  have upper := Nat.le_ceil ((h:ℝ)/(digitBits a h:ℝ))
  exact_mod_cast (div_le_iff₀ positive).mp upper

/-- The same four constants work on every pass and for every pair of padded
block and pack heights. Both networks retain the catalysts from feasibility. -/
theorem feasible_grids {F : Type*} [Field F] {k : ℕ} {a B r R : ℝ}
    (ha : 1<a) (hB : 1<B) (blocks : Feasible F k a r) (packs : Feasible F k B R) :
    ∃ A C U V : ℝ, 0<A ∧ 0<C ∧ 0<U ∧ 0<V ∧ ∀ᶠ h : ℕ in atTop,
      GridScales a B h ∧ ∀ t u : ℕ, 2*digitBits a h ≤ t → h-packBits B h ≤ u →
      ∃ X : Catalyst.Approximation F k (pins t (width t a)),
      ∃ Y : Catalyst.Approximation F k (pins u (width u B)),
        (X.size:ℝ) ≤ A*work t (width t a) r ∧ X.Gap (coeff F t (width t a)) (gap C t) ∧
        (Y.size:ℝ) ≤ U*work u (width u B) R ∧ Y.Gap (coeff F u (width u B)) (gap V u) := by
  obtain ⟨A,C,hA,hC,localCalls⟩ := blocks
  obtain ⟨U,V,hU,hV,wideCalls⟩ := packs
  refine ⟨A,C,U,V,hA,hC,hU,hV,?_⟩
  filter_upwards [eventual_grid_scales ha hB,
    eventual_grid_components ha hB localCalls wideCalls] with h scales usable
  refine ⟨scales,?_⟩
  intro t u ht hu
  obtain ⟨⟨X,px,gx⟩,⟨Y,py,gy⟩⟩ := usable t u ht hu
  exact ⟨X,Y,px,gx,py,gy⟩

/-- Fixed additive losses on either component, such as slicing tiebreak fields,
can be paid before the local amplification. The amplified and wide calls each
retain twice the final gap for subsequent substitutions. -/
theorem eventual_packing_gaps_with_losses {a B C V D m K : ℝ} (ha : 1<a) (hB : 1<B)
    (hD : 6≤D) (localMargin : C≤D) (wideNonneg : 0≤V) (wideMargin : V<D)
    (hm : 0<m) (hK : 0≤K) (d k : ℕ) (L W : ℝ) :
    ∀ᶠ h : ℕ in atTop, ∀ (t u : ℕ) (s H : ℝ),
      2*digitBits a h ≤ t → t ≤ 2*digitBits a h+d → h-packBits B h ≤ u →
      m*(2:ℝ)^h ≤ s*(2:ℝ)^t → 0<H → H≤K*((t:ℝ)+1)^2 →
      2*gap D h ≤ s*(gap C t-L)/(2*H) ∧ 2*gap D h ≤ gap V u-W ∧
      4*(k:ℝ)*(Real.logb 2 H+3) ≤ gap C t-L := by
  have small := (GapScale.eventual_interface_threshold C (2*k) hK).and
    (GapScale.eventual_polynomial C (2*L) 0 le_rfl)
  have threshold := eventual_grid_components ha hB small
    (Filter.Eventually.of_forall (fun _ : ℕ => True.intro))
  filter_upwards [eventual_grid_scales ha hB,threshold,eventually_ge_atTop (3*d),
    eventually_ge_atTop (2:ℕ),GapScale.eventual_polynomial D W 0 le_rfl,
    GapScale.eventual_shorter_amplification hD hm hK (by norm_num : (0:ℝ)≤4),
    GapScale.eventual_log_shift (J:=B) wideNonneg wideMargin (by norm_num : (0:ℝ)≤1)]
    with h scales correct padding two wideLoss amplified shifted
  intro t u s H lo hi wide mass hp cap
  have frac := scales.digit_fraction
  have short : 3*t ≤ 2*h := by omega
  have sn : 0 ≤ s := nonneg_of_mul_nonneg_left ((mul_nonneg hm.le (by positivity)).trans mass)
    (by positivity : 0 < (2:ℝ)^t)
  have den : 0 < 2*H := by positivity
  have localBound := (le_div_iff₀ den).mp (amplified t s H short mass hp cap)
  have ⟨thresholdAt,offset⟩ := (correct t u lo wide).1
  simp only [Real.rpow_zero,mul_one] at offset wideLoss
  have hc := thresholdAt H hp.le cap
  push_cast at hc
  have half : gap D t ≤ 2*(gap C t-L) := by
    linarith only [GapScale.antitone_coefficient localMargin t,offset]
  refine ⟨(le_div_iff₀ den).mpr ?_,?_,by linarith only [hc,offset]⟩
  · linarith only [localBound,mul_le_mul_of_nonneg_left half sn]
  · have packed := shifted u (scales.pack_shift hB wide)
    rw [Real.rpow_one] at packed
    have height : (2:ℝ) ≤ h := by exact_mod_cast two
    linarith only [wideLoss,packed,
      mul_le_mul_of_nonneg_right (show (3:ℝ)≤2*(h:ℝ) by linarith) (gap_pos D h).le]

/-- Specialize to an unpadded local payload and the number of shared-tag
slices needed for the packed payload. -/
theorem eventual_packing_gaps {a B C V D m K : ℝ} (ha : 1<a) (hB : 1<B)
    (hD : 6≤D) (localMargin : C≤D) (wideNonneg : 0≤V) (wideMargin : V<D)
    (hm : 0<m) (hK : 0≤K) (d k : ℕ) :
    ∀ᶠ h : ℕ in atTop, ∀ (t u : ℕ) (s H : ℝ),
      2*digitBits a h ≤ t → t ≤ 2*digitBits a h+d → h-packBits B h ≤ u →
      m*(2:ℝ)^h ≤ s*(2:ℝ)^t → 0<H → H≤K*((t:ℝ)+1)^2 →
      2*gap D h ≤ s*gap C t/(2*H) ∧
      2*gap D h ≤ gap V u-2*(k:ℝ)*(⌈2*(2:ℝ)^B⌉₊:ℝ) ∧
      4*(k:ℝ)*(Real.logb 2 H+3) ≤ gap C t := by
  simpa only [sub_zero] using eventual_packing_gaps_with_losses ha hB hD localMargin
    wideNonneg wideMargin hm hK d k 0 (2*(k:ℝ)*(⌈2*(2:ℝ)^B⌉₊:ℝ))

end Hierarchy.Tagged.Radix

end OAI
