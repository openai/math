import OAI.Geometry.Hirsch.Blocking

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

variable {Index : Type} [Fintype Index] [Nonempty Index]

def least (values : Index → ℝ) := Finset.univ.inf' Finset.univ_nonempty values

theorem least_le (values : Index → ℝ) (idx : Index) : least values ≤ values idx :=
  Finset.inf'_le values (Finset.mem_univ idx)

theorem le_least {values : Index → ℝ} {lower : ℝ} (hh : ∀ idx, lower ≤ values idx) :
    lower ≤ least values :=
  Finset.le_inf' _ _ (fun idx _ => hh idx)

theorem least_attained (values : Index → ℝ) : ∃ idx, least values = values idx := by
  obtain ⟨idx, _, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty values
  exact ⟨idx, he⟩

theorem continuous_least {Space : Type} [TopologicalSpace Space] {values : Index → Space → ℝ}
    (hc : ∀ idx, Continuous (values idx)) : Continuous (fun pt => least (fun idx => values idx pt)) :=
  Continuous.finset_inf'_apply _ (fun idx _ => hc idx)

theorem least_close {first last : Index → ℝ} {eps : ℝ}
    (hh : ∀ idx, |first idx - last idx| ≤ eps) : |least first - least last| ≤ eps := by
  obtain ⟨left, hl⟩ := least_attained first
  obtain ⟨right, hr⟩ := least_attained last
  rw [abs_le]
  constructor
  · linarith [least_le last left, (abs_le.mp (hh left)).1]
  · linarith [least_le first right, (abs_le.mp (hh right)).2]

theorem least_concave {first mid last : Index → ℝ}
    (hh : ∀ idx, (first idx + last idx) / 2 ≤ mid idx) :
    (least first + least last) / 2 ≤ least mid := by
  apply le_least
  intro idx
  linarith [hh idx, least_le first idx, least_le last idx]

def peak (values : Index → ℝ) := -least (-values)

theorem le_peak (values : Index → ℝ) (idx : Index) : values idx ≤ peak values := by
  simpa [peak] using neg_le_neg (least_le (-values) idx)

theorem peak_attained (values : Index → ℝ) : ∃ idx, peak values = values idx := by
  obtain ⟨idx, hh⟩ := least_attained (-values)
  exact ⟨idx, by simp [peak, hh]⟩

theorem continuous_peak {Space : Type} [TopologicalSpace Space] {values : Index → Space → ℝ}
    (hc : ∀ idx, Continuous (values idx)) : Continuous (fun pt => peak (fun idx => values idx pt)) :=
  (continuous_least fun idx => (hc idx).neg).neg

namespace Readings

structure Upper (Index : Type) where
  slope : Index → ℝ
  intercept : Index → ℝ
  small : ∀ idx, |slope idx| < 1 / 4

def Upper.line (upper : Upper Index) (time : ℝ) (idx : Index) :=
  upper.intercept idx - upper.slope idx * time

def Upper.bound (upper : Upper Index) (time : ℝ) := least (upper.line time)

variable {Left Right : Type} [Fintype Left] [Nonempty Left] [Fintype Right] [Nonempty Right]
  (early : Upper Left) (late : Upper Right)

def root (left : Left) (right : Right) :=
  (early.intercept left - late.intercept right) / (1 + early.slope left - late.slope right)

def clock := least fun left => peak (root early late left)

omit [Fintype Left] [Nonempty Left] [Fintype Right] [Nonempty Right] in
theorem denom_pos (left : Left) (right : Right) : 0 < 1 + early.slope left - late.slope right := by
  linarith [(abs_lt.mp (early.small left)).1, (abs_lt.mp (late.small right)).2]

omit [Fintype Left] [Nonempty Left] [Fintype Right] [Nonempty Right] in
theorem le_root (time : ℝ) (left : Left) (right : Right) :
    time ≤ root early late left right ↔ time ≤ early.line time left - late.line time right := by
  rw [root, le_div_iff₀ (denom_pos early late left right)]
  unfold Upper.line
  constructor <;> intro hh <;> linarith

omit [Fintype Left] [Nonempty Left] [Fintype Right] [Nonempty Right] in
theorem root_le (time : ℝ) (left : Left) (right : Right) :
    root early late left right ≤ time ↔ early.line time left - late.line time right ≤ time := by
  rw [root, div_le_iff₀ (denom_pos early late left right)]
  unfold Upper.line
  constructor <;> intro hh <;> linarith

theorem le_clock (time : ℝ) :
    time ≤ clock early late ↔ time ≤ early.bound time - late.bound time := by
  unfold clock Upper.bound
  constructor
  · intro hh
    obtain ⟨left, hl⟩ := least_attained (early.line time)
    obtain ⟨right, hr⟩ := peak_attained (root early late left)
    have he := (le_root early late time left right).mp
      ((hh.trans (least_le _ left)).trans_eq hr)
    linarith [least_le (late.line time) right]
  · intro hh
    obtain ⟨right, hr⟩ := least_attained (late.line time)
    refine le_least fun left => le_trans ?_ (le_peak _ right)
    apply (le_root early late time left right).mpr
    linarith [least_le (early.line time) left]

theorem clock_le (time : ℝ) :
    clock early late ≤ time ↔ early.bound time - late.bound time ≤ time := by
  unfold clock Upper.bound
  constructor
  · intro hh
    obtain ⟨left, hl⟩ := least_attained (fun left => peak (root early late left))
    obtain ⟨right, hr⟩ := least_attained (late.line time)
    rw [hl] at hh
    have he := (root_le early late time left right).mp ((le_peak _ right).trans hh)
    linarith [least_le (early.line time) left]
  · intro hh
    obtain ⟨left, hl⟩ := least_attained (early.line time)
    obtain ⟨right, hr⟩ := peak_attained (root early late left)
    apply (least_le _ left).trans
    rw [hr]
    apply (root_le early late time left right).mpr
    linarith [least_le (late.line time) right]

theorem fixed_point (time : ℝ) :
    time = clock early late ↔ time = early.bound time - late.bound time := by
  simp only [le_antisymm_iff, le_clock, clock_le]

theorem bounded {cap : ℝ} (hc : 0 ≤ cap)
    (he : ∀ time ∈ Icc (-cap) cap, early.bound time ∈ Icc 0 cap)
    (hl : ∀ time ∈ Icc (-cap) cap, late.bound time ∈ Icc 0 cap) :
    clock early late ∈ Icc (-cap) cap := by
  have hh : -cap ≤ cap := by linarith
  refine ⟨(le_clock ..).mpr ?_, (clock_le ..).mpr ?_⟩
  · linarith [(he _ ⟨le_rfl, hh⟩).1, (hl _ ⟨le_rfl, hh⟩).2]
  · linarith [(he _ ⟨hh, le_rfl⟩).2, (hl _ ⟨hh, le_rfl⟩).1]

theorem continuous_clock {Space : Type} [TopologicalSpace Space]
    {early : Space → Upper Left} {late : Space → Upper Right}
    (he : ∀ idx, Continuous (fun pt => (early pt).intercept idx))
    (hl : ∀ idx, Continuous (fun pt => (late pt).intercept idx))
    (he' : ∀ idx, Continuous (fun pt => (early pt).slope idx))
    (hl' : ∀ idx, Continuous (fun pt => (late pt).slope idx)) :
    Continuous (fun pt => clock (early pt) (late pt)) := by
  apply continuous_least
  intro left
  apply continuous_peak
  intro right
  exact ((he left).sub (hl right)).div ((continuous_const.add (he' left)).sub (hl' right))
    (fun pt => (denom_pos _ _ _ _).ne')

def weight (early late res : ℝ) := (1 - res - 2 * late) / (1 + early - late)

theorem weights {early late res : ℝ} (he : |early| < 1/4) (hl : |late| < 1/4) (hr : |res| < 1/4) :
    0 < weight early late res ∧ weight early late res < 2 ∧
    weight early late res * (1 + early - late) = 1 - res - 2 * late := by
  rw [abs_lt] at he hl hr
  have hh : 0 < 1 + early - late := by linarith
  exact ⟨div_pos (by linarith) hh, (div_lt_iff₀ hh).mpr (by linarith), div_mul_cancel₀ _ hh.ne'⟩

theorem eliminate {early late res : ℝ} (he : |early| < 1/4) (hl : |late| < 1/4)
    (hr : |res| < 1/4) (first last resource s u : ℝ) :
    let factor := weight early late res
    factor * first + (2 - factor) * last + resource =
      factor * (first - early * (s - u) - s) + (2 - factor) * (last - late * (s - u) - u) +
        (resource - res * (s - u) + s + u) := by
  dsimp only
  linear_combination (s - u) * (weights he hl hr).2.2

end Readings
end OAI.Geometry.Hirsch
