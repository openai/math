import OAI.Optimization.LinearProgramming.PriceGame.Phases
import OAI.Optimization.LinearProgramming.PriceGame.PhasesOrder
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Real.Basic

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Phases
open Finset

theorem no_event_since_origin (miss : ℕ → ℕ → Bool) (t : ℕ) :
    ∀ k, origin miss t ≤ k → k < t → exceptional miss k = false := by
  induction t with
  | zero => intro k _ hk; omega
  | succ t ih =>
    intro k hlo hhi
    rw [origin_succ] at hlo
    cases he : exceptional miss t
    · simp [he] at hlo
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hhi) with hlt | rfl
      · exact ih k hlo hlt
      · exact he
    · simp [he] at hlo
      omega

theorem count_const (miss : ℕ → ℕ → Bool) {u v : ℕ} (huv : u ≤ v)
    (good : ∀ k, u ≤ k → k < v → exceptional miss k = false) :
    (events miss v).card = (events miss u).card := by
  induction v, huv using Nat.le_induction with
  | base => rfl
  | succ v huv ih =>
    rw [count_succ, good v huv (Nat.lt_succ_self _)]
    exact ih (fun k h₁ h₂ => good k h₁ (Nat.lt_succ_of_lt h₂))

theorem tag_at_origin {miss : ℕ → ℕ → Bool} {T E : ℕ} {bound : (events miss T).card ≤ E}
    {b : Fin (E+1)} {t : Fin T} (good : tag miss T E bound t = some b) :
    tag miss T E bound ⟨origin miss t, (origin_le miss _).trans_lt t.isLt⟩ = some b := by
  obtain ⟨ht, hc⟩ := (tag_some t b).mp good
  let first := origin miss t
  have hl : first ≤ t.val := origin_le miss t
  apply (tag_some _ _).mpr
  refine ⟨?_, ?_⟩
  · change exceptional miss first = false
    rcases lt_or_eq_of_le hl with hh | hh
    · exact no_event_since_origin miss t first le_rfl hh
    · exact hh ▸ ht
  · exact (count_const miss hl (no_event_since_origin miss t)).symm.trans hc

/-- A contiguous nonempty good fiber expressed in the natural-number coordinates used by
the fixed-share score bound. The first trial's selected IDs were allocated at that trial. -/
structure Segment {T E : ℕ} (miss : ℕ → ℕ → Bool) (bound : (events miss T).card ≤ E)
    (b : Fin (E+1)) where
  first : Fin T
  length : ℕ
  finish_le : first.val + length ≤ T
  good_first : tag miss T E bound first = some b
  origin_first : origin miss first = first.val
  tick_iff : ∀ t : Fin T, tag miss T E bound t = some b ↔ first.val ≤ t.val ∧ t.val < first.val + length
  card_eq : (univ.filter fun t => tag miss T E bound t = some b).card = length
  sum_eq : ∀ F : ℕ → ℝ, (∑ t ∈ univ.filter (fun t => tag miss T E bound t = some b), F t.val) =
    ∑ i ∈ range length, F (first.val + i)

def segment {T E : ℕ} (miss : ℕ → ℕ → Bool) (bound : (events miss T).card ≤ E)
    (b : Fin (E+1)) (hs : (univ.filter fun t => tag miss T E bound t = some b).Nonempty) :
    Segment miss bound b := by
  let s : Finset (Fin T) := univ.filter fun t => tag miss T E bound t = some b
  let a := s.min' hs
  let d := s.max' hs
  have mem (t : Fin T) : t ∈ s ↔ tag miss T E bound t = some b := by simp [s]
  have ha : a ∈ s := s.min'_mem hs
  have hd : d ∈ s := s.max'_mem hs
  have cv : ∀ u ∈ s, ∀ w ∈ s, ∀ v, u ≤ v → v ≤ w → v ∈ s := by
    intro u hu w hw v huv hvw
    exact (mem v).mpr (good_interval huv hvw ((mem u).mp hu) ((mem w).mp hw))
  have mapEq : s.map Fin.valEmbedding = Ico a.val (d.val+1) := convex_map_val_eq_Ico s hs cv
  have had : a.val ≤ d.val := s.min'_le _ hd
  have finish : a.val + (d.val+1 - a.val) = d.val+1 := by omega
  refine ⟨a, d.val+1-a.val, finish.trans_le d.isLt, (mem a).mp ha, ?_, ?_,
    card_convex_eq_length s hs cv, ?_⟩
  · let j : Fin T := ⟨origin miss a, (origin_le miss _).trans_lt a.isLt⟩
    have hj : j ∈ s := (mem j).mpr (tag_at_origin ((mem a).mp ha))
    exact Nat.le_antisymm (origin_le miss a) (s.min'_le _ hj)
  · intro t
    rw [← mem t, finish]
    have ht : t ∈ s ↔ t.val ∈ s.map Fin.valEmbedding := by
      constructor
      · intro h
        exact Finset.mem_map.mpr ⟨t,h,rfl⟩
      · intro h
        obtain ⟨v,hv,hvt⟩ := Finset.mem_map.mp h
        exact (Fin.ext hvt : v = t) ▸ hv
    simpa [mapEq] using ht
  · intro F
    calc
      _ = ∑ j ∈ s.map Fin.valEmbedding, F j := by simp [s]
      _ = _ := by rw [mapEq, sum_Ico_eq_sum_range]

end Phases
end PriceGame
end LinearProgramming
end Optimization
end OAI
