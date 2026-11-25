import OAI.Geometry.Hirsch.Overlay
import OAI.Geometry.Hirsch.Nesting

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

abbrev Kind := Option Bool

def Kind.position : Kind → ℝ
  | some false => 2
  | some true => 6
  | none => 10

theorem Kind.bounds (kind : Kind) : 2 ≤ kind.position ∧ kind.position ≤ 10 := by
  rcases kind with _ | (_ | _) <;> norm_num [position]

namespace Windows

variable {count : ℕ} (hc : 0 < count)

def center (kind : Kind) (idx : Fin count) := 16 * (idx.val : ℝ) + kind.position

theorem separated {kind other : Kind} {idx pos : Fin count} (hn : (kind, idx) ≠ (other, pos)) :
    4 ≤ |center kind idx - center other pos| := by
  unfold center
  obtain ⟨hl, hu⟩ := kind.bounds
  obtain ⟨hl', hu'⟩ := other.bounds
  rcases lt_trichotomy idx pos with hh | rfl | hh
  · have he : (idx.val : ℝ) + 1 ≤ pos.val := by exact_mod_cast hh
    rw [le_abs]; right; linarith
  · rcases kind with _ | (_ | _) <;> rcases other with _ | (_ | _) <;>
      simp_all [Kind.position] <;> norm_num
  · have he : (pos.val : ℝ) + 1 ≤ idx.val := by exact_mod_cast hh
    rw [le_abs]; left; linarith

def place (kind : Kind) : Placement (Fin count) where
  speed := 32 * count
  positive := by positivity
  center := center kind
  separated := fun hn => separated (fun he => hn (Prod.mk.inj he).2)

theorem disjoint {kind other : Kind} {idx pos : Fin count} {time : ℝ}
    (hf : time ∈ (place hc kind).influence idx) (hl : time ∈ (place hc other).influence pos) :
    (kind, idx) = (other, pos) := by
  by_contra hn
  have he := separated hn
  change |32 * (count : ℝ) * (time - 1/4) - center kind idx| < 1 at hf
  change |32 * (count : ℝ) * (time - 1/4) - center other pos| < 1 at hl
  rw [abs_lt] at hf hl
  rcases le_abs.mp he <;> linarith

def atPos (count : ℕ) (pos : ℝ) := 1/4 + pos / (32 * count)

include hc in
theorem increasing : StrictMono (atPos count) := by
  intro first last hh
  unfold atPos
  gcongr

theorem axis_at (kind : Kind) (pos : ℝ) : (place hc kind).axis (atPos count pos) = pos := by
  unfold Placement.axis atPos place
  dsimp only
  field_simp
  ring

def start (idx : Fin count) := atPos count (16 * idx.val + 1)
def stop (idx : Fin count) := atPos count (16 * idx.val + 13)

theorem start_gt (idx : Fin count) : 1/4 < start idx := by
  have hp := idx.isLt
  unfold start atPos
  have : 0 < count := by omega
  exact lt_add_of_pos_right _ (by positivity)

theorem stop_lt (idx : Fin count) : stop idx < 3/4 := by
  have hp : (idx.val : ℝ) + 1 ≤ count := by exact_mod_cast idx.isLt
  have hh : 0 < (count : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) idx.val]
  unfold stop atPos
  have he : (16 * (idx.val : ℝ) + 13) / (32 * count) < 1/2 :=
    (div_lt_iff₀ (by positivity)).mpr (by linarith)
  linarith

def work : Episodes count where
  left := start
  right := stop
  positive idx := lt_trans (by norm_num) (start_gt idx)
  interior idx := lt_trans (stop_lt idx) (by norm_num)
  width idx := increasing hc (by linarith)
  ordered := by
    intro first last hh
    have he : (first.val : ℝ) + 1 ≤ last.val := by exact_mod_cast hh
    exact increasing hc (by linarith)

variable (kind : Kind) (idx : Fin count)

def left := atPos count (center kind idx - 1/4)
def right := atPos count (center kind idx + 1/4)

include hc in
theorem bounds : start idx ≤ left kind idx ∧ left kind idx < right kind idx ∧ right kind idx ≤ stop idx := by
  obtain ⟨hl, hu⟩ := kind.bounds
  exact ⟨(increasing hc (by unfold center; linarith)).le, increasing hc (by linarith),
    (increasing hc (by unfold center; linarith)).le⟩

theorem local_left : (place hc kind).localTime idx (left kind idx) = 0 := by
  rw [Placement.localTime, left, axis_at]
  change 2 * (center kind idx - 1/4 - center kind idx) + 1/2 = 0
  ring

theorem local_right : (place hc kind).localTime idx (right kind idx) = 1 := by
  rw [Placement.localTime, right, axis_at]
  change 2 * (center kind idx + 1/4 - center kind idx) + 1/2 = 1
  ring

theorem in_window {time : ℝ} (ht : time ∈ Icc (left kind idx) (right kind idx)) :
    time ∈ (place hc kind).window idx := by
  have hm : Monotone (place hc kind).axis := by
    intro first last hh
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hh _) (place hc kind).positive.le
  have hl := hm ht.1
  have hr := hm ht.2
  rw [left, axis_at] at hl
  rw [right, axis_at] at hr
  change |(place hc kind).axis time - center kind idx| ≤ 1/4
  rw [abs_le]
  constructor <;> linarith

end Windows
end OAI.Geometry.Hirsch
