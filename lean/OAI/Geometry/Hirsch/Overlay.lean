import OAI.Geometry.Hirsch.Normalization
import OAI.Geometry.Hirsch.Readings

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

structure Placement (Index : Type) where
  speed : ℝ
  positive : 0 < speed
  center : Index → ℝ
  separated : ∀ {first last}, first ≠ last → 4 ≤ |center first - center last|

namespace Placement

variable {Index Coord Row : Type} (place : Placement Index)

def axis (time : ℝ) := place.speed * (time - 1/4)
def localTime (idx : Index) (time : ℝ) := 2 * (place.axis time - place.center idx) + 1/2
def window (idx : Index) := {time | |place.axis time - place.center idx| ≤ 1/4}
def influence (idx : Index) := {time | |place.axis time - place.center idx| < 1}
def gap (idx : Index) (side : Bool) := place.center idx + if side then 1 else -1
def tangent (site time : ℝ) := 2 * site * place.axis time - site ^ 2

theorem dominates {idx : Index} {site time : ℝ} (ht : time ∈ place.window idx)
    (hs : 1 ≤ |place.center idx - site|) :
    place.tangent site time + 1/2 ≤ place.tangent (place.center idx) time := by
  change |place.axis time - place.center idx| ≤ 1/4 at ht
  rw [abs_le] at ht
  unfold tangent
  rcases le_abs.mp hs with hh | hh <;> nlinarith

theorem gap_separated (idx other : Index) (side : Bool) :
    1 ≤ |place.center idx - place.gap other side| := by
  by_cases he : idx = other
  · subst other
    cases side <;> simp [gap]
  have hs := place.separated he
  cases side <;> simp only [gap, Bool.false_eq_true, ↓reduceIte] <;> grind

theorem dominated {idx : Index} {time : ℝ} (ht : time ∉ place.influence idx) :
    ∃ side, place.tangent (place.center idx) time + 1 ≤ place.tangent (place.gap idx side) time := by
  change ¬ |place.axis time - place.center idx| < 1 at ht
  rcases le_abs.mp (le_of_not_gt ht) with hh | hh
  · exact ⟨true, by simp only [tangent, gap, ↓reduceIte]; linarith⟩
  · exact ⟨false, by simp only [tangent, gap, Bool.false_eq_true, ↓reduceIte]; linarith⟩

variable (block : Blocking Coord Row)

def raw (idx : Index) (row : Row) (time : ℝ) :=
  block.slope row * place.localTime idx time + block.offset row

def Bounded (cap bound : ℝ) : Prop :=
  ∀ idx row time, |time| ≤ cap → |place.raw block idx row time| ≤ bound

theorem bounded [Finite Index] [Finite Row] (cap : ℝ) :
    ∃ bound, 0 < bound ∧ place.Bounded block cap bound := by
  have hh : ∀ pair : Index × Row, ∃ val, ∀ time ∈ Icc (-cap) cap,
      |place.raw block pair.1 pair.2 time| ≤ val := by
    intro pair
    have hc : Continuous (fun time => |place.raw block pair.1 pair.2 time|) := by
      unfold raw localTime axis
      fun_prop
    obtain ⟨val, hv⟩ := (isCompact_Icc.image hc).bddAbove
    exact ⟨val, fun _ ht => hv (mem_image_of_mem _ ht)⟩
  choose val hv using hh
  obtain ⟨bound, hb⟩ := Finite.bddAbove_range val
  exact ⟨max 1 bound, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun idx row time ht =>
    ((hv (idx, row) time (abs_le.mp ht)).trans (hb (mem_range_self _))).trans (le_max_right _ _)⟩

abbrev Rows (Index Coord Row : Type) := (Index × Row) ⊕ (Index × Bool × Coord)

def height (bound : ℝ) (row : Rows Index Coord Row) (time : ℝ) : ℝ :=
  match row with
  | .inl (idx, src) => place.raw block idx src time + 8 * bound * place.tangent (place.center idx) time
  | .inr (idx, side, _) => 8 * bound * place.tangent (place.gap idx side) time

theorem affine (bound : ℝ) (row : Rows Index Coord Row) (time : ℝ) :
    (place.height block bound row 1 - place.height block bound row 0) * time +
      place.height block bound row 0 = place.height block bound row time := by
  rcases row with ⟨idx, src⟩ | ⟨idx, side, coord⟩ <;>
    simp only [height, raw, localTime, tangent, axis] <;> ring

variable [Nonempty Index]

def overlay (bound : ℝ) : Blocking Coord (Rows Index Coord Row) where
  coeff
    | .inl pair => block.coeff pair.2
    | .inr triple => LinearMap.proj triple.2.2
  slope row := place.height block bound row 1 - place.height block bound row 0
  offset row := place.height block bound row 0
  monotone := by
    rintro (pair | triple)
    · exact block.monotone _
    · exact fun _ _ hh => hh _
  positive := by
    rintro (pair | triple)
    · exact block.positive _
    · exact zero_lt_one
  individual idx := ⟨.inr (Classical.arbitrary _, false, idx), 1, one_pos, (one_smul _ _).symm⟩

theorem unit (hu : block.UnitWeights) (bound : ℝ) : (place.overlay block bound).UnitWeights := by
  rintro (pair | triple)
  · exact hu _
  · rfl

def shift (bound : ℝ) (idx : Index) (time : ℝ) :=
  8 * bound * place.tangent (place.center idx) time

def decode (bound : ℝ) (idx : Index) (pt : Timed Coord) : Timed Coord :=
  (place.localTime idx pt.1, pt.2 - fun _ => place.shift bound idx pt.1)

theorem copy_slack (hu : block.UnitWeights) (bound : ℝ) (idx : Index) (row : Row) (pt : Timed Coord) :
    (place.overlay block bound).slack (.inl (idx, row)) pt = block.slack row (place.decode bound idx pt) := by
  simp only [Blocking.slack, overlay, affine, decode, map_sub, hu.constant]
  unfold height raw shift
  ring

theorem blank_slack (bound : ℝ) (idx : Index) (side : Bool) (coord : Coord) (pt : Timed Coord) :
    (place.overlay block bound).slack (.inr (idx, side, coord)) pt =
      pt.2 coord - 8 * bound * place.tangent (place.gap idx side) pt.1 := by
  simp only [Blocking.slack, overlay, affine, LinearMap.proj_apply]
  rfl

variable {bound cap : ℝ} {pt : Timed Coord} {idx : Index}

theorem decode_feasible (hu : block.UnitWeights) (hp : pt ∈ (place.overlay block bound).system.body) :
    place.decode bound idx pt ∈ block.system.body := by
  apply (block.feasible _).mpr
  intro row
  rw [← place.copy_slack block hu]
  exact ((place.overlay block bound).feasible _).mp hp _

theorem copy_influence (hu : block.UnitWeights) (hb : 0 < bound) (hm : place.Bounded block cap bound)
    (ht : |pt.1| ≤ cap) (hp : pt ∈ (place.overlay block bound).system.body) {row : Row}
    (ha : Sum.inl (idx, row) ∈ (place.overlay block bound).system.active pt) :
    pt.1 ∈ place.influence idx := by
  by_contra hn
  obtain ⟨side, hs⟩ := place.dominated hn
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 8 * bound)
  have hl : ∀ coord, 8 * bound * place.tangent (place.gap idx side) pt.1 ≤ pt.2 coord := by
    intro coord
    have hv := ((place.overlay block bound).feasible _).mp hp (.inr (idx, side, coord))
    rwa [blank_slack, sub_nonneg] at hv
  have he := ((place.overlay block bound).tight _ _).mp ha
  simp only [Blocking.slack, overlay, affine] at he
  change block.coeff row pt.2 - (place.raw block idx row pt.1 +
    8 * bound * place.tangent (place.center idx) pt.1) = 0 at he
  linarith [hu.lower row hl, (abs_le.mp (hm idx row _ ht)).2]

theorem strict_other (hu : block.UnitWeights) (hb : 0 < bound) (hm : place.Bounded block cap bound)
    (ht : |pt.1| ≤ cap) (hw : pt.1 ∈ place.window idx)
    (hp : place.decode bound idx pt ∈ block.system.body) (row : Rows Index Coord Row)
    (hn : ∀ src, row ≠ .inl (idx, src)) : 0 < (place.overlay block bound).slack row pt := by
  have hl : ∀ coord, place.shift bound idx pt.1 - bound ≤ pt.2 coord := by
    intro coord
    obtain ⟨src, he⟩ := hu.individual coord
    have hh := (block.feasible _).mp hp src
    rw [Blocking.slack, he] at hh
    change 0 ≤ pt.2 coord - place.shift bound idx pt.1 - place.raw block idx src pt.1 at hh
    linarith [(abs_le.mp (hm idx src _ ht)).1]
  have hd : ∀ site, 1 ≤ |place.center idx - site| →
      8 * bound * place.tangent site pt.1 + 4 * bound ≤ place.shift bound idx pt.1 := by
    intro site hs
    unfold shift
    linarith [mul_le_mul_of_nonneg_left (place.dominates hw hs) (by positivity : 0 ≤ 8 * bound)]
  rcases row with ⟨other, src⟩ | ⟨other, side, coord⟩
  · have he : idx ≠ other := by rintro rfl; exact hn src rfl
    have hh := hd _ (le_trans (by norm_num) (place.separated he))
    simp only [Blocking.slack, overlay, affine]
    change 0 < block.coeff src pt.2 - (place.raw block other src pt.1 +
      8 * bound * place.tangent (place.center other) pt.1)
    linarith [hu.lower src hl, (abs_le.mp (hm other src _ ht)).2]
  · rw [blank_slack]
    linarith [hd _ (place.gap_separated idx other side), hl coord]

theorem decode_admissible [Finite Coord] (hu : block.UnitWeights) (hb : 0 < bound)
    (hm : place.Bounded block cap bound) (ht : |pt.1| ≤ cap) (hw : pt.1 ∈ place.window idx)
    {viable : Set Coord → Prop} {limit : ℕ}
    (hp : pt ∈ (place.overlay block bound).admissible viable limit) :
    place.decode bound idx pt ∈ block.admissible viable limit := by
  have hf := place.decode_feasible block hu (idx := idx) hp.1
  apply block.admissible_of_tight hp hf
  ext normal
  constructor
  · rintro ⟨src, hs, rfl⟩
    refine ⟨.inl (idx, src), ?_, rfl⟩
    rwa [Blocking.tight, copy_slack _ _ hu, ← Blocking.tight]
  · rintro ⟨row, hr, rfl⟩
    have hex : ∃ src, row = .inl (idx, src) := by
      by_contra! hn
      exact (place.strict_other block hu hb hm ht hw hf row hn).ne' (((place.overlay block bound).tight _ _).mp hr)
    obtain ⟨src, rfl⟩ := hex
    refine ⟨src, ?_, rfl⟩
    rwa [Blocking.tight, copy_slack _ _ hu, ← Blocking.tight] at hr

end Placement
end OAI.Geometry.Hirsch
