import OAI.Geometry.Hirsch.Overlay

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

variable {Coord Row : Type}

structure Tuned (block : Blocking Coord Row) (cap rho : ℝ) : Prop where
  unit : block.UnitWeights
  positive : 0 < rho
  slope : ∀ row, |rho * block.slope row| < 1/4
  rhs : ∀ row time, |time| ≤ cap → |rho * (block.slice time).rhs row| ≤ 1/32

theorem tune [Finite Row] {block : Blocking Coord Row} (hu : block.UnitWeights) (cap : ℝ) :
    ∃ eps > 0, ∀ rho : ℝ, 0 < rho → rho ≤ eps → Tuned block cap rho := by
  obtain ⟨bound, hb⟩ := Finite.bddAbove_range
    (fun row => |block.slope row| * (1 + |cap|) + |block.offset row|)
  let val := max 1 bound
  have hv : 0 < val := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hh : ∀ row, |block.slope row| * (1 + |cap|) + |block.offset row| ≤ val :=
    fun row => (hb (mem_range_self row)).trans (le_max_right _ _)
  refine ⟨(1/32) / val, by positivity, fun rho hp hle => ⟨hu, hp, ?_, ?_⟩⟩
  · intro row
    have ht : |block.slope row| ≤ val := by
      nlinarith [hh row, abs_nonneg (block.offset row), abs_nonneg (block.slope row), abs_nonneg cap]
    rw [abs_mul, abs_of_pos hp]
    linarith [mul_le_mul_of_nonneg_left ht hp.le, (le_div_iff₀ hv).mp hle]
  · intro row time ht
    have hr : |(block.slice time).rhs row| ≤ val := calc
      _ ≤ |block.slope row * time| + |block.offset row| := abs_add_le _ _
      _ ≤ |block.slope row| * (1 + |cap|) + |block.offset row| := by
        rw [abs_mul]
        gcongr
        linarith [le_abs_self cap]
      _ ≤ _ := hh row
    rw [abs_mul, abs_of_pos hp]
    exact (mul_le_mul_of_nonneg_left hr hp.le).trans ((le_div_iff₀ hv).mp hle)

namespace Tuned

variable {block : Blocking Coord Row} {cap rho : ℝ} (tune : Tuned block cap rho)

def upper (vec : Vec Coord) : Readings.Upper (Option Row) where
  slope row := row.elim 0 (fun src => rho * block.slope src)
  intercept row := row.elim cap (fun src => block.coeff src vec - rho * block.offset src)
  small := by rintro (_ | row); exacts [by norm_num, tune.slope row]

theorem line_some (vec : Vec Coord) (time : ℝ) (row : Row) :
    (tune.upper vec).line time (some row) = block.coeff row vec - rho * (block.slice time).rhs row := by
  simp [Readings.Upper.line, upper, Blocking.slice]
  ring

@[simp] theorem line_none (vec : Vec Coord) (time : ℝ) :
    (tune.upper vec).line time none = cap := by simp [Readings.Upper.line, upper]

def image (vec : Vec Coord) (time reading : ℝ) : Timed Coord :=
  (time, rho⁻¹ • (vec - fun _ => reading))

theorem slack (vec : Vec Coord) (time reading : ℝ) (row : Row) :
    rho * block.slack row (image (rho := rho) vec time reading) =
      (tune.upper vec).line time (some row) - reading := by
  rw [line_some]
  simp only [Blocking.slack, image, map_smul, map_sub, tune.unit.constant, smul_eq_mul, Blocking.slice]
  field_simp [tune.positive.ne']
  ring

variable [Fintype Row]

theorem lower {vec : Vec Coord} {time floor : ℝ} (ht : |time| ≤ cap)
    (hf : ∀ idx, floor ≤ vec idx) (hc : floor ≤ cap) :
    floor - 1/32 ≤ (tune.upper vec).bound time := by
  apply le_least
  rintro (_ | row)
  · rw [line_none]; linarith
  · rw [line_some]
    linarith [tune.unit.lower row hf, (abs_le.mp (tune.rhs row time ht)).2]

theorem upper_of_attained {vec : Vec Coord} {time floor : ℝ} (ht : |time| ≤ cap)
    (hf : ∃ idx, vec idx = floor) : (tune.upper vec).bound time ≤ floor + 1/32 := by
  obtain ⟨idx, hi⟩ := hf
  obtain ⟨row, hr⟩ := tune.unit.individual idx
  apply (least_le _ (some row)).trans
  rw [line_some, hr, LinearMap.proj_apply, hi]
  linarith [(abs_le.mp (tune.rhs row time ht)).1]

theorem bound_mem {vec : Vec Coord} (hf : ∀ idx, 1 ≤ vec idx) (hc : 1 ≤ cap) :
    ∀ time ∈ Icc (-cap) cap, (tune.upper vec).bound time ∈ Icc 0 cap := by
  intro time ht
  exact ⟨(by norm_num : (0 : ℝ) ≤ 1 - 1/32).trans (tune.lower (abs_le.mpr ht) hf hc),
    (least_le _ none).trans_eq (tune.line_none vec time)⟩

theorem image_feasible (vec : Vec Coord) (time : ℝ) :
    image (rho := rho) vec time ((tune.upper vec).bound time) ∈ block.system.body := by
  apply (block.feasible _).mpr
  intro row
  apply (mul_nonneg_iff_of_pos_left tune.positive).mp
  rw [tune.slack]
  exact sub_nonneg.mpr (least_le _ _)

end Tuned

structure Coupler (Coord Row Resource ResRow : Type) where
  clock : Bool → Blocking Coord Row
  res : Blocking Resource ResRow
  cap : ℝ
  cap_ge : 1 ≤ cap
  rho : ℝ
  clockTune : ∀ side, Tuned (clock side) cap rho
  resTune : Tuned res cap rho

namespace Coupler

variable {Resource ResRow : Type} [Fintype Row] (cp : Coupler Coord Row Resource ResRow)

abbrev Clocks (Coord : Type) := Bool → Vec Coord

def upper (vec : Clocks Coord) (side : Bool) := (cp.clockTune side).upper (vec side)

def time (vec : Clocks Coord) := Readings.clock (cp.upper vec false) (cp.upper vec true)

def read (vec : Clocks Coord) (side : Bool) := (cp.upper vec side).bound (cp.time vec)

theorem time_eq (vec : Clocks Coord) : cp.time vec = cp.read vec false - cp.read vec true :=
  (Readings.fixed_point _ _ _).mp rfl

theorem continuous_time [Fintype Coord] : Continuous cp.time := by
  have hi : ∀ side row, Continuous (fun vec => (cp.upper vec side).intercept row) := by
    rintro side (_ | row)
    · exact continuous_const
    · exact (((cp.clock side).coeff row).continuous_of_finiteDimensional.comp
        (continuous_apply side)).sub continuous_const
  exact Readings.continuous_clock (hi false) (hi true)
    (fun _ => continuous_const) (fun _ => continuous_const)

theorem time_bound {vec : Clocks Coord} (hf : ∀ side idx, 1 ≤ vec side idx) :
    |cp.time vec| ≤ cp.cap :=
  abs_le.mpr (Readings.bounded _ _ (zero_le_one.trans cp.cap_ge)
    ((cp.clockTune false).bound_mem (hf false) cp.cap_ge)
    ((cp.clockTune true).bound_mem (hf true) cp.cap_ge))

def clockPt (vec : Clocks Coord) (side : Bool) :=
  Tuned.image (rho := cp.rho) (vec side) (cp.time vec) (cp.read vec side)

def resPt (vec : Clocks Coord) (slacks : Vec Resource) : Timed Resource :=
  Tuned.image (rho := cp.rho) slacks (cp.time vec) (-(cp.read vec false + cp.read vec true))

def upperSlack (vec : Clocks Coord) (side : Bool) (row : Option Row) :=
  (cp.upper vec side).line (cp.time vec) row - cp.read vec side

theorem upper_nonneg (vec : Clocks Coord) (side : Bool) (row : Option Row) :
    0 ≤ cp.upperSlack vec side row := sub_nonneg.mpr (least_le _ _)

theorem upper_attained (vec : Clocks Coord) (side : Bool) :
    ∃ row, cp.upperSlack vec side row = 0 := by
  obtain ⟨row, hr⟩ := least_attained ((cp.upper vec side).line (cp.time vec))
  exact ⟨row, sub_eq_zero.mpr hr.symm⟩

theorem clock_tight (vec : Clocks Coord) (side : Bool) (row : Row) :
    cp.upperSlack vec side (some row) = 0 ↔ row ∈ (cp.clock side).system.active (cp.clockPt vec side) := by
  rw [Blocking.tight, upperSlack, upper, ← Tuned.slack, mul_eq_zero]
  simp [cp.resTune.positive.ne', clockPt]

end Coupler
end OAI.Geometry.Hirsch
