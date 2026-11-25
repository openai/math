import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! # Splitting a quadratic chirp into consecutive nonstationary runs

A set of at most `2a` increments spaced by `1/a` meets at most three
integer strips of width one. Cutting each strip at distance `δ` from
the central integer costs at most `2aδ+1` exceptional summands.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Chirp
open Finset

/-- A consecutive range on which the increment avoids the integers can be
estimated by a single summation-by-parts bound. -/
theorem partition_sum_bound (a m : ℕ) (ha : 0 < a) (hm : m ≤ 2 * a)
    (β δ R : ℝ) (hδ : 0 ≤ δ) (hR : 0 ≤ R) (u : ℕ → ℂ)
    (hu : ∀ i < m, ‖u i‖ ≤ 1)
    (run : ∀ (j : ℤ) (l r : ℕ), r ≤ m →
      (∀ i ∈ Ico l r, (j : ℝ) + δ ≤ β - (i : ℝ) / a ∧
        β - (i : ℝ) / a ≤ j + 1 - δ) → ‖∑ i ∈ Ico l r, u i‖ ≤ R) :
    ‖∑ i ∈ range m, u i‖ ≤ 3 * (2 * (a : ℝ) * δ + 1 + R) := by
  classical
  have apos : (0 : ℝ) < a := by exact_mod_cast ha
  let α (i : ℕ) := β - (i : ℝ) / a
  let label (i : ℕ) := ⌊α i + δ⌋
  let top := ⌊β + δ⌋
  let labels := Icc (top - 2) top
  have anti : Antitone α := by
    intro i k hik
    dsimp [α]
    gcongr
  have hb (i : ℕ) : (label i : ℝ) ≤ α i + δ ∧ α i + δ < label i + 1 :=
    ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  have labels_mem : ∀ i ∈ range m, label i ∈ labels := by
    intro i hi
    have hir : (i : ℝ) < 2 * a := by exact_mod_cast (lt_of_lt_of_le (mem_range.mp hi) hm)
    have hid : (i : ℝ) / a < 2 := (div_lt_iff₀ apos).2 hir
    apply mem_Icc.mpr
    constructor
    · apply Int.le_floor.mpr
      dsimp [top, α]
      push_cast
      linarith [Int.floor_le (β + δ)]
    · apply Int.floor_le_floor
      dsimp [α]
      linarith [div_nonneg (Nat.cast_nonneg (α := ℝ) i) apos.le]
  let fiber (j : ℤ) := (range m).filter (fun i => label i = j)
  have sum_fib : ∑ j ∈ labels, ∑ i ∈ fiber j, u i = ∑ i ∈ range m, u i :=
    sum_fiberwise_of_maps_to labels_mem u
  have one_fiber (j : ℤ) : ‖∑ i ∈ fiber j, u i‖ ≤ 2 * (a : ℝ) * δ + 1 + R := by
    let bad := (fiber j).filter (fun i => α i < j + δ)
    let good := (fiber j).filter (fun i => ¬ α i < j + δ)
    have hbad (i) (hi : i ∈ bad) : i < m ∧ (j : ℝ) - δ ≤ α i ∧ α i < j + δ := by
      obtain ⟨hi, hl⟩ := mem_filter.mp hi
      obtain ⟨hi, he⟩ := mem_filter.mp hi
      exact ⟨mem_range.mp hi, by linarith [he ▸ (hb i).1], hl⟩
    have hcard : (bad.card : ℝ) ≤ 2 * a * δ + 1 := by
      by_cases hh : bad.Nonempty
      · let l := bad.min' hh
        let r := bad.max' hh
        have hl := hbad l (bad.min'_mem hh)
        have hr := hbad r (bad.max'_mem hh)
        have hsub : bad ⊆ Icc l r := fun i hi =>
          mem_Icc.mpr ⟨min'_le _ _ hi, le_max' _ _ hi⟩
        have hlr : l ≤ r := le_max' _ _ (bad.min'_mem hh)
        have hcard' := card_le_card hsub
        rw [Nat.card_Icc] at hcard'
        have hc : (bad.card : ℝ) ≤ (r : ℝ) + 1 - l := by
          apply (le_sub_iff_add_le).mpr
          exact_mod_cast (show bad.card + l ≤ r + 1 by omega)
        have hd : ((r : ℝ) - l) / a ≤ 2 * δ := by
          rw [sub_div]
          dsimp [α] at hl hr
          linarith
        linarith [(div_le_iff₀ apos).mp hd]
      · rw [not_nonempty_iff_eq_empty.mp hh]
        simp only [card_empty, Nat.cast_zero]
        positivity
    have badBound : ‖∑ i ∈ bad, u i‖ ≤ 2 * a * δ + 1 := by
      calc
        _ ≤ ∑ _i ∈ bad, (1 : ℝ) := norm_sum_le_of_le _ fun i hi => hu i (hbad i hi).1
        _ ≤ _ := by simpa using hcard
    have good_iff (i : ℕ) : i ∈ good ↔
        i < m ∧ (j : ℝ) + δ ≤ α i ∧ α i < j + 1 - δ := by
      simp only [good, fiber, mem_filter, mem_range, not_lt]
      constructor
      · rintro ⟨⟨hi, he⟩, h⟩
        exact ⟨hi, h, by linarith [he ▸ (hb i).2]⟩
      · rintro ⟨hi, h, h'⟩
        exact ⟨⟨hi, Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩⟩, h⟩
    have goodBound : ‖∑ i ∈ good, u i‖ ≤ R := by
      by_cases hh : good.Nonempty
      · let l := good.min' hh
        let r := good.max' hh
        have hl := (good_iff l).mp (good.min'_mem hh)
        have hr := (good_iff r).mp (good.max'_mem hh)
        have heq : good = Ico l (r + 1) := by
          ext i
          constructor
          · intro hi
            exact mem_Ico.mpr ⟨min'_le _ _ hi, Nat.lt_succ_of_le (le_max' _ _ hi)⟩
          · intro hi
            obtain ⟨hil, hir⟩ := mem_Ico.mp hi
            have hir' := Nat.le_of_lt_succ hir
            exact (good_iff i).mpr ⟨lt_of_le_of_lt hir' hr.1,
              hr.2.1.trans (anti hir'), lt_of_le_of_lt (anti hil) hl.2.2⟩
        rw [heq]
        apply run j l (r + 1) hr.1
        intro i hi
        obtain ⟨_, h, h'⟩ := (good_iff i).mp (heq ▸ hi)
        exact ⟨h, h'.le⟩
      · simpa [not_nonempty_iff_eq_empty.mp hh] using hR
    rw [← sum_filter_add_sum_filter_not (fiber j) (fun i => α i < j + δ)]
    exact (norm_add_le ..).trans (add_le_add badBound goodBound)
  rw [← sum_fib]
  calc
    _ ≤ ∑ _j ∈ labels, (2 * (a : ℝ) * δ + 1 + R) :=
      norm_sum_le_of_le _ fun j _ => one_fiber j
    _ = _ := by simp [labels, Int.card_Icc]; ring

end Chirp

end NearSquareRoot
end Computability
end OAI
