import OAI.Geometry.Hirsch.Programs

noncomputable section

open Set Module

namespace OAI.Geometry.Hirsch.Blocking

variable {Coord Row Other : Type} (block : Blocking Coord Row)

def UnitWeights : Prop := ∀ row, block.coeff row 1 = 1

theorem UnitWeights.constant {block : Blocking Coord Row} (hu : block.UnitWeights)
    (row : Row) (value : ℝ) : block.coeff row (fun _ => value) = value := by
  rw [show (fun _ : Coord => value) = value • 1 by ext; simp, map_smul, hu row, smul_eq_mul, mul_one]

theorem UnitWeights.lower {block : Blocking Coord Row} (hu : block.UnitWeights)
    (row : Row) {vec : Vec Coord} {value : ℝ} (hh : ∀ idx, value ≤ vec idx) :
    value ≤ block.coeff row vec :=
  (hu.constant row value).symm.trans_le (block.monotone row hh)

theorem UnitWeights.individual {block : Blocking Coord Row} (hu : block.UnitWeights) (idx : Coord) :
    ∃ row, block.coeff row = LinearMap.proj idx := by
  obtain ⟨row, weight, _, he⟩ := block.individual idx
  have hh := hu row
  simp [he] at hh
  exact ⟨row, by simp [he, hh]⟩

def normalize : Blocking Coord Row where
  coeff row := (block.coeff row 1)⁻¹ • block.coeff row
  slope row := (block.coeff row 1)⁻¹ * block.slope row
  offset row := (block.coeff row 1)⁻¹ * block.offset row
  monotone row := fun _ _ hh => mul_le_mul_of_nonneg_left (block.monotone row hh)
    (inv_nonneg.mpr (block.positive row).le)
  positive row := mul_pos (inv_pos.mpr (block.positive row)) (block.positive row)
  individual idx := by
    obtain ⟨row, weight, hw, he⟩ := block.individual idx
    exact ⟨row, _, mul_pos (inv_pos.mpr (block.positive row)) hw, by rw [he, smul_smul]⟩

theorem unit_normalize : block.normalize.UnitWeights := fun row => inv_mul_cancel₀ (block.positive row).ne'

def slack (row : Row) (pt : Timed Coord) := block.coeff row pt.2 - (block.slope row * pt.1 + block.offset row)

theorem feasible (pt : Timed Coord) : pt ∈ block.system.body ↔ ∀ row, 0 ≤ block.slack row pt := by
  rw [← mem_slice]
  simp [System.body, slice, slack]

theorem tight (pt : Timed Coord) (row : Row) :
    row ∈ block.system.active pt ↔ block.slack row pt = 0 := by
  rw [← active_slice]
  simp [slice, System.active, slack, sub_eq_zero]

theorem slack_normalize (row : Row) (pt : Timed Coord) :
    block.normalize.slack row pt = (block.coeff row 1)⁻¹ * block.slack row pt := by
  simp only [slack, normalize, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem support_normalize (row : Row) : block.normalize.support row = block.support row := by
  ext idx
  simp [support, normalize, (block.positive row).ne']

theorem admissible_normalize (viable : Set Coord → Prop) (limit : ℕ) :
    block.normalize.admissible viable limit = block.admissible viable limit := by
  have ha : ∀ pt, block.normalize.system.active pt = block.system.active pt := by
    intro pt
    ext row
    simp [tight, slack_normalize, (block.positive row).ne']
  have hb : block.normalize.system.body = block.system.body := by
    ext pt
    simp only [feasible, slack_normalize, mul_nonneg_iff_of_pos_left (inv_pos.mpr (block.positive _))]
  have hk : ∀ rows, (block.normalize.slice 0).directions rows = (block.slice 0).directions rows := by
    intro rows
    ext dir
    simp [System.mem_directions, slice, normalize, (block.positive _).ne']
  have hr : ∀ pt usable, finrank ℝ (block.normalize.nullspace (block.normalize.system.active pt) usable) =
      finrank ℝ (block.nullspace (block.system.active pt) usable) := by
    intro pt usable
    rw [nullspace, hk, ha]
    rfl
  simp only [admissible, certified, hr, ha, hb, support_normalize]

theorem admissible_of_tight [Finite Coord] {other : Blocking Coord Other}
    {viable : Set Coord → Prop} {limit : ℕ} {src dst : Timed Coord}
    (hp : src ∈ other.admissible viable limit) (hf : dst ∈ block.system.body)
    (hw : block.coeff '' block.system.active dst = other.coeff '' other.system.active src) :
    dst ∈ block.admissible viable limit := by
  obtain ⟨_, usable, hv, hs, hd⟩ := hp
  refine ⟨hf, usable, hv, ?_, le_trans (Submodule.finrank_mono ?_) hd⟩
  · intro row hr
    obtain ⟨idx, hi, he⟩ := hw.subset (mem_image_of_mem _ hr)
    simpa [support, he] using hs idx hi
  · rintro dir ⟨hu, hh⟩
    refine ⟨hu, (System.mem_directions _).mpr (fun row hr => ?_)⟩
    obtain ⟨idx, hi, he⟩ := hw.symm.subset (mem_image_of_mem _ hr)
    change other.coeff row dir = 0
    rw [← he]
    exact (System.mem_directions _).mp hh idx hi

end OAI.Geometry.Hirsch.Blocking
