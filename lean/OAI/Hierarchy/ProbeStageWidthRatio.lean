import OAI.Hierarchy.ProbeStageScale
import OAI.Hierarchy.TaggedShorterBudget
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI
/-! # Address ratios of the actual positive-scale probe groups -/

namespace Hierarchy.ProbeStage
open Filter Real TaggedShorterBudget
open scoped Topology

/-- Every address with a uniformly bounded additive offset from the nine radix
digits tends to the requested dyadic fraction of the parent address. The
offset may vary with both the parent and the site. -/
theorem stage_address_ratio {ι : Type*} {l : Filter ι} (W E : ℕ) (h extra : ι→ℕ)
    (high : Tendsto h l atTop) (bounded : ∀ᶠ x in l,extra x≤E) :
    Tendsto (fun x=>((9*digit (h x) (2^W)+extra x:ℕ):ℝ)/h x) l (𝓝 (dyadic W)) := by
  let d := 2^W
  have dn : 0<d := pow_pos (by decide) _
  have dd : 0<(d:ℝ) := Nat.cast_pos.mpr dn
  have price : dyadic W=1/(d:ℝ) := by simp [dyadic,d]
  rw [price,tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) _ ((tendsto_const_div_atTop_nhds_zero_nat ((E:ℝ)+9)).comp high)
  filter_upwards [high.eventually_gt_atTop 0,bounded] with x positive room
  have hp : 0<(h x:ℝ) := Nat.cast_pos.mpr positive
  let r := h x%(9*d)
  let f := digit (h x) d
  have exactN : (9*d)*f+r=h x := Nat.div_add_mod ..
  have exactR : (9*(d:ℝ))*(f:ℝ)+(r:ℝ)=h x := by exact_mod_cast exactN
  have remN : r<9*d := Nat.mod_lt _ (by positivity)
  have remR : (r:ℝ)/(d:ℝ)≤9 := (div_le_iff₀ dd).mpr (by exact_mod_cast remN.le)
  have rem0 := div_nonneg (Nat.cast_nonneg r : (0:ℝ)≤r) dd.le
  have eq : (h x:ℝ)/(d:ℝ)=9*(f:ℝ)+(r:ℝ)/d := by
    apply (div_eq_iff dd.ne').mpr
    rw [add_mul,div_mul_cancel₀ _ dd.ne']
    nlinarith only [exactR]
  have ext : (extra x:ℝ)≤E := by exact_mod_cast room
  have er : |((9*f+extra x:ℕ):ℝ)-(h x:ℝ)/d|≤(E:ℝ)+9 := by
    rw [eq]
    push_cast
    exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg (extra x) (α:=ℝ),Nat.cast_nonneg E (α:=ℝ)],by linarith⟩
  change dist (((9*f+extra x:ℕ):ℝ)/h x) (1/(d:ℝ)) ≤ ((E:ℝ)+9)/h x
  rw [Real.dist_eq,show ((9*f+extra x:ℕ):ℝ)/(h x:ℝ)-1/(d:ℝ) =
      (((9*f+extra x:ℕ):ℝ)-(h x:ℝ)/d)/h x by field_simp [hp.ne',dd.ne'],
      abs_div,abs_of_pos hp]
  exact div_le_div_of_nonneg_right er hp.le

/-- Address for a uniform dyadic supergroup, including a fixed role/duplication
offset. It simultaneously fits every outer and every central group. -/
def superAddress (W pad h : ℕ) : ℕ :=
  9*digit h (2^W)+(9*2^W+18*(2^W-1)+2+pad)

theorem outer_address_fits (W pad h : ℕ) :
    9*digit h (2^W)+2+pad ≤ superAddress W pad h := by unfold superAddress; omega

theorem center_address_fits (W pad h : ℕ) :
    widthLog h (2^W) (rounds (2^W))+pad ≤ superAddress W pad h := by
  rw [center_width]
  have rem := Nat.mod_lt h (show 0<9*2^W by positivity)
  unfold superAddress
  omega

theorem superAddress_ratio {ι : Type*} {l : Filter ι} (W pad : ℕ) (h : ι→ℕ)
    (high : Tendsto h l atTop) :
    Tendsto (fun x=>(superAddress W pad (h x):ℝ)/h x) l (𝓝 (dyadic W)) :=
  stage_address_ratio W _ h (fun _=>9*2^W+18*(2^W-1)+2+pad) high (Eventually.of_forall fun _=>le_rfl)

theorem outer_address_ratio {ι : Type*} {l : Filter ι} (W pad : ℕ) (h : ι→ℕ)
    (high : Tendsto h l atTop) :
    Tendsto (fun x=>((9*digit (h x) (2^W)+2+pad:ℕ):ℝ)/h x) l (𝓝 (dyadic W)) := by
  simpa only [Nat.add_assoc] using
    stage_address_ratio W (2+pad) h (fun _=>2+pad) high (Eventually.of_forall fun _=>le_rfl)

theorem center_address_ratio {ι : Type*} {l : Filter ι} (W pad : ℕ) (h : ι→ℕ)
    (high : Tendsto h l atTop) :
    Tendsto (fun x=>((widthLog (h x) (2^W) (rounds (2^W))+pad:ℕ):ℝ)/h x) l (𝓝 (dyadic W)) := by
  have rem (x : ι) := Nat.mod_lt (h x) (show 0<9*2^W by positivity)
  simpa only [center_width,Nat.add_assoc] using stage_address_ratio W (9*2^W+18*(2^W-1)+pad) h
    (fun x=>h x%(9*2^W)+(18*(2^W-1)+pad)) high (Eventually.of_forall fun x=>by have := rem x;omega)

end Hierarchy.ProbeStage

end OAI
