import OAI.Geometry.Hirsch.Clock
import OAI.Geometry.Hirsch.Restriction

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

variable {Coord Row Resource ResRow : Type}

abbrev Triple (Row ResRow : Type) := Option Row × Option Row × ResRow

def Triple.side (triple : Triple Row ResRow) (side : Bool) := if side then triple.2.1 else triple.1

namespace Coupler

variable (cp : Coupler Coord Row Resource ResRow) (triple : Triple Row ResRow)

def slope (side : Bool) := (cp.upper 0 side).slope (triple.side side)

def factor := Readings.weight (cp.slope triple false) (cp.slope triple true)
  (cp.rho * cp.res.slope triple.2.2)

def multiplier (side : Bool) := if side then 2 - cp.factor triple else cp.factor triple

theorem mult_pos (side : Bool) : 0 < cp.multiplier triple side := by
  have hh := Readings.weights ((cp.upper 0 false).small triple.1) ((cp.upper 0 true).small triple.2.1)
    (cp.resTune.slope triple.2.2)
  cases side
  · exact hh.1
  · exact sub_pos.mpr hh.2.1

def intercept (vec : Clocks Coord) (side : Bool) :=
  (cp.upper vec side).intercept (triple.side side)

def combined (vec : Clocks Coord) (slacks : Vec Resource) :=
  cp.multiplier triple false * cp.intercept triple vec false +
  cp.multiplier triple true * cp.intercept triple vec true +
    cp.res.coeff triple.2.2 slacks - cp.rho * cp.res.offset triple.2.2

variable [Fintype Row]

theorem upper_eq (vec : Clocks Coord) (side : Bool) :
    cp.upperSlack vec side (triple.side side) =
      cp.intercept triple vec side - cp.slope triple side * cp.time vec - cp.read vec side := rfl

theorem expansion (vec : Clocks Coord) (slacks : Vec Resource) :
    cp.combined triple vec slacks =
      cp.multiplier triple false * cp.upperSlack vec false (triple.side false) +
      cp.multiplier triple true * cp.upperSlack vec true (triple.side true) +
      cp.rho * cp.res.slack triple.2.2 (cp.resPt vec slacks) := by
  have hh := Readings.eliminate ((cp.upper 0 false).small (triple.side false))
    ((cp.upper 0 true).small (triple.side true)) (cp.resTune.slope triple.2.2)
    (cp.intercept triple vec false) (cp.intercept triple vec true)
    (cp.res.coeff triple.2.2 slacks - cp.rho * cp.res.offset triple.2.2)
    (cp.read vec false) (cp.read vec true)
  rw [upper_eq, upper_eq, resPt, cp.resTune.slack, Tuned.line_some, cp.time_eq]
  unfold combined multiplier factor slope
  simp only [Bool.false_eq_true, ↓reduceIte, Blocking.slice]
  linear_combination hh

def Active (vec : Clocks Coord) (slacks : Vec Resource) : Prop :=
  (∀ side, cp.upperSlack vec side (triple.side side) = 0) ∧
    triple.2.2 ∈ cp.res.system.active (cp.resPt vec slacks)

theorem nonneg {vec : Clocks Coord} {slacks : Vec Resource}
    (hf : cp.resPt vec slacks ∈ cp.res.system.body) : 0 ≤ cp.combined triple vec slacks := by
  rw [cp.expansion]
  exact add_nonneg (add_nonneg (mul_nonneg (cp.mult_pos _ _).le (cp.upper_nonneg ..))
    (mul_nonneg (cp.mult_pos _ _).le (cp.upper_nonneg ..)))
    (mul_nonneg cp.resTune.positive.le ((cp.res.feasible _).mp hf _))

theorem zero_iff {vec : Clocks Coord} {slacks : Vec Resource}
    (hf : cp.resPt vec slacks ∈ cp.res.system.body) :
    cp.combined triple vec slacks = 0 ↔ cp.Active triple vec slacks := by
  have hh := fun side => mul_nonneg (cp.mult_pos triple side).le (cp.upper_nonneg vec side (triple.side side))
  have hr := mul_nonneg cp.resTune.positive.le ((cp.res.feasible _).mp hf triple.2.2)
  rw [expansion, add_eq_zero_iff_of_nonneg (add_nonneg (hh false) (hh true)) hr,
    add_eq_zero_iff_of_nonneg (hh false) (hh true)]
  simp [Active, Bool.forall_bool, Blocking.tight, (cp.mult_pos triple _).ne', cp.resTune.positive.ne']

theorem feasible_of_combined {vec : Clocks Coord} {slacks : Vec Resource}
    (hh : ∀ triple, 0 ≤ cp.combined triple vec slacks) : cp.resPt vec slacks ∈ cp.res.system.body := by
  obtain ⟨left, hl⟩ := cp.upper_attained vec false
  obtain ⟨right, hr⟩ := cp.upper_attained vec true
  apply (cp.res.feasible _).mpr
  intro row
  have hv := hh (left, right, row)
  rw [expansion] at hv
  simpa [Triple.side, hl, hr, mul_nonneg_iff_of_pos_left cp.resTune.positive] using hv

theorem active_of_resource {vec : Clocks Coord} {slacks : Vec Resource} {row : ResRow}
    (hr : row ∈ cp.res.system.active (cp.resPt vec slacks)) :
    ∃ triple, cp.Active triple vec slacks ∧ triple.2.2 = row := by
  obtain ⟨left, hl⟩ := cp.upper_attained vec false
  obtain ⟨right, hh⟩ := cp.upper_attained vec true
  exact ⟨(left, right, row), ⟨by rintro (_ | _) <;> assumption, hr⟩, rfl⟩

theorem active_of_clock {vec : Clocks Coord} {slacks : Vec Resource} {side : Bool} {row : Row}
    (ha : ∃ triple, cp.Active triple vec slacks)
    (hr : row ∈ (cp.clock side).system.active (cp.clockPt vec side)) :
    ∃ triple, cp.Active triple vec slacks ∧ triple.side side = some row := by
  obtain ⟨tr, hh, hres⟩ := ha
  have ht := (cp.clock_tight vec side row).mpr hr
  cases side
  · exact ⟨(some row, tr.2), ⟨by rintro (_ | _); exacts [ht, hh true], hres⟩, rfl⟩
  · exact ⟨(tr.1, some row, tr.2.2), ⟨by rintro (_ | _); exacts [hh false, ht], hres⟩, rfl⟩

theorem affine_read {first mid last : Clocks Coord}
    (hav : mid = (1/2 : ℝ) • (first + last))
    (hf : ∀ side, cp.upperSlack first side (triple.side side) = 0)
    (hm : ∀ side, cp.upperSlack mid side (triple.side side) = 0)
    (hl : ∀ side, cp.upperSlack last side (triple.side side) = 0) :
    cp.time mid = (cp.time first + cp.time last) / 2 ∧
      ∀ side, cp.read mid side = (cp.read first side + cp.read last side) / 2 := by
  have hint : ∀ side, 2 * cp.intercept triple mid side =
      cp.intercept triple first side + cp.intercept triple last side := by
    intro side
    unfold intercept upper Tuned.upper
    dsimp only
    cases triple.side side <;> simp [hav, map_smul, map_add] <;> ring
  simp only [upper_eq] at hf hm hl
  have diff : ∀ side, 2 * cp.read mid side - cp.read first side - cp.read last side =
      -cp.slope triple side * (2 * cp.time mid - cp.time first - cp.time last) := by
    intro side
    linarith [hint side, hf side, hm side, hl side]
  have he : (1 + cp.slope triple false - cp.slope triple true) *
      (2 * cp.time mid - cp.time first - cp.time last) = 0 := by
    linarith [diff false, diff true, cp.time_eq first, cp.time_eq mid, cp.time_eq last]
  have hn := Readings.denom_pos (cp.upper 0 false) (cp.upper 0 true) (triple.side false) (triple.side true)
  have hz := (mul_eq_zero.mp he).resolve_left hn.ne'
  refine ⟨by linarith, fun side => ?_⟩
  have hh := diff side
  rw [hz, mul_zero] at hh
  linarith

end Coupler
end OAI.Geometry.Hirsch
