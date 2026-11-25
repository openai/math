import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open Finset

variable {ι : Type*} [DecidableEq ι]

private theorem sum_abs_lt_of_doubling (f : ι → ℝ) (s : Finset ι) :
    (∀ i ∈ s, f i ≠ 0) →
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 * |f i| < |f j| ∨ 2 * |f j| < |f i|) →
    ∀ b : ℝ, 0 < b → (∀ i ∈ s, 2 * |f i| < b) → ∑ i ∈ s, |f i| < b := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro hn h b hb hu
    by_cases hs : s.Nonempty
    · obtain ⟨m, hm, hmax⟩ := s.exists_max_image (fun i => |f i|) hs
      have hmpos : 0 < |f m| := abs_pos.mpr (hn m hm)
      have hlow (i) (hi : i ∈ s.erase m) : 2 * |f i| < |f m| := by
        obtain ⟨him, his⟩ := Finset.mem_erase.mp hi
        exact (h i his m hm him).resolve_right (by linarith [hmax i his])
      have hrest := ih (s.erase m) (Finset.erase_ssubset hm)
        (fun i hi => hn i (Finset.mem_of_mem_erase hi))
        (fun i hi j hj => h i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj))
        |f m| hmpos hlow
      rw [← Finset.sum_erase_add _ _ hm]
      linarith [hu m hm]
    · simpa [Finset.not_nonempty_iff_eq_empty.mp hs] using hb

private theorem sum_ne_zero_of_doubling (s : Finset ι) (f : ι → ℝ) (hs : s.Nonempty)
    (hn : ∀ i ∈ s, f i ≠ 0)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 * |f i| < |f j| ∨ 2 * |f j| < |f i|) :
    ∑ i ∈ s, f i ≠ 0 := by
  obtain ⟨m, hm, hmax⟩ := s.exists_max_image (fun i => |f i|) hs
  have hmpos : 0 < |f m| := abs_pos.mpr (hn m hm)
  have hrest := sum_abs_lt_of_doubling f (s.erase m)
    (fun i hi => hn i (Finset.mem_of_mem_erase hi))
    (fun i hi j hj => h i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj))
    |f m| hmpos (fun i hi => by
      obtain ⟨him, his⟩ := Finset.mem_erase.mp hi
      exact (h i his m hm him).resolve_right (by linarith [hmax i his]))
  intro hz
  have hcancel : ∑ i ∈ s.erase m, f i = -f m := by
    linarith [Finset.sum_erase_add s f hm]
  have htriangle := Finset.abs_sum_le_sum_abs f (s.erase m)
  rw [hcancel, abs_neg] at htriangle
  exact hrest.not_ge htriangle

/-- If the absolute values of the nonzero terms are pairwise separated by a factor of two,
then every subset has a distinct sum, even if the terms have different signs. -/
theorem subsetSum_injOn_of_doubling (s : Finset ι) (f : ι → ℝ) (hn : ∀ i ∈ s, f i ≠ 0)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2 * |f i| < |f j| ∨ 2 * |f j| < |f i|) :
    Set.InjOn (fun t : Finset ι => ∑ i ∈ t, f i) (↑s.powerset : Set (Finset ι)) := by
  intro a ha b hb heq
  have ha' := Finset.mem_powerset.mp ha
  have hb' := Finset.mem_powerset.mp hb
  let g (i : ι) := (if i ∈ a then f i else 0) - (if i ∈ b then f i else 0)
  let d := s.filter fun i => g i ≠ 0
  have hsum (t : Finset ι) (ht : t ⊆ s) :
      (∑ i ∈ s, if i ∈ t then f i else 0) = ∑ i ∈ t, f i := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    exact Finset.mem_filter.trans ⟨And.right, fun hi => ⟨ht hi, hi⟩⟩
  have hzero : ∑ i ∈ d, g i = 0 := calc
    _ = ∑ i ∈ s, g i := Finset.sum_subset (Finset.filter_subset _ _) (fun i hi hd => by
      by_contra hgi
      exact hd (Finset.mem_filter.mpr ⟨hi, hgi⟩))
    _ = 0 := by simp [g, Finset.sum_sub_distrib, hsum a ha', hsum b hb', heq]
  have hneq (i) (hi : i ∈ d) : g i ≠ 0 := (Finset.mem_filter.mp hi).2
  have hgabs (i) (hi : i ∈ d) : |g i| = |f i| := by
    have hgi := hneq i hi
    by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp_all [g]
  have hg0 (i) (hi : i ∈ s) : g i = 0 := by
    by_contra hgi
    have hd : d.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
    apply sum_ne_zero_of_doubling d g hd hneq _ hzero
    intro j hj k hk hjk
    simpa only [hgabs j hj, hgabs k hk] using
      h j (Finset.mem_filter.mp hj).1 k (Finset.mem_filter.mp hk).1 hjk
  ext i
  constructor
  · intro hai
    by_contra hbi
    simpa [g, hai, hbi, hn i (ha' hai)] using hg0 i (ha' hai)
  · intro hbi
    by_contra hai
    simpa [g, hai, hbi, hn i (hb' hbi)] using hg0 i (hb' hbi)

end Compression
end LinearProgramming
end Optimization
end OAI
