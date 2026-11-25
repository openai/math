import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-!
# Positions of the end markers in a sorted list of parameter uses

A marker is sorted after all uses of its own label. Its zero-based position
is the number of earlier markers plus the number of uses at labels through
this label. Thus adjacent marker positions recover the entire histogram,
even for an empty run. Lower sort-key fields may carry guessed marker
positions: the check against the actual output position forces those guesses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchCounts

variable {U P : Type*} [Fintype U] [Fintype P] {k L : ℕ}

/-- Original unsorted rows consist of uses, one end marker per key, and padding. -/
abbrev Rows (U : Type*) (k : ℕ) (P : Type*) := U ⊕ (Fin k ⊕ P)

/-- Uses precede their marker; all padding lies at the end. -/
def key (label : U → Fin k) : Rows U k P → ℕ
  | .inl u => 2 * (label u).val
  | .inr (.inl i) => 2 * i.val + 1
  | .inr (.inr _) => 2 * k

/-- Number of uses of a given parameter label. -/
def useCount (label : U → Fin k) (i : Fin k) : ℕ :=
  (Finset.univ.filter (fun u => label u = i)).card

/-- The required position of a given end marker. -/
def markerRank (label : U → Fin k) (i : Fin k) : ℕ :=
  (Finset.univ.filter (fun u => label u ≤ i)).card + i.val

private theorem filter_lt {n : ℕ} (j : Fin n) :
    Finset.univ.filter (fun i => i < j) = Finset.Iio j := by
  ext i
  simp

/-- A sorted bijection of all the records places each marker at its prescribed
rank. There is no choice of order within an equal run that can alter this rank. -/
theorem marker_rank_eq (label : U → Fin k) (order : Fin L ≃ Rows U k P)
    (hm : Monotone (fun j => key label (order j))) (i : Fin k) :
    (order.symm (.inr (.inl i))).val = markerRank label i := by
  classical
  let m := order.symm (.inr (.inl i))
  have atMarker : key label (order m) = 2 * i.val + 1 := by simp [m, key]
  have only {z : Rows U k P} (hz : key label z = 2 * i.val + 1) : z = .inr (.inl i) := by
    rcases z with u | j | p
    · simp only [key] at hz; omega
    · simp only [key] at hz
      have : j = i := Fin.ext (by omega)
      simp [this]
    · simp only [key] at hz; omega
  have comp (j : Fin L) : j < m ↔ key label (order j) < 2 * i.val + 1 := by
    constructor
    · intro h
      have hle := (hm h.le).trans (le_of_eq atMarker)
      apply lt_of_le_of_ne hle
      intro he
      exact h.ne (order.injective ((only he).trans (order.apply_symm_apply _).symm))
    · intro h
      by_contra! hj
      exact (not_lt_of_ge ((le_of_eq atMarker.symm).trans (hm hj))) h
  have left : (Finset.Iio m).card =
      ∑ j : Fin L, if key label (order j) < 2 * i.val + 1 then 1 else 0 := by
    simp_rw [← comp]
    simp [filter_lt]
  rw [Fin.card_Iio] at left
  change m.val = _
  rw [left, order.sum_comp (fun z => if key label z < 2 * i.val + 1 then 1 else 0),
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  have uses (u : U) : 2 * (label u).val < 2 * i.val + 1 ↔ label u ≤ i := by
    change _ ↔ (label u).val ≤ i.val
    omega
  have markers (j : Fin k) : 2 * j.val + 1 < 2 * i.val + 1 ↔ j < i := by
    change _ ↔ j.val < i.val
    omega
  have pad : ¬ (2 * k < 2 * i.val + 1) := by omega
  simp [key, uses, markers, pad, markerRank, filter_lt]

/-- The first marker has no preceding marker; its position is the first count. -/
theorem markerRank_zero {k : ℕ} (label : U → Fin (k + 1)) :
    markerRank label 0 = useCount label 0 := by
  simp [markerRank, useCount]

/-- Adjacent end markers have one position of their own between the two cumulative counts. -/
theorem markerRank_succ {k : ℕ} (label : U → Fin (k + 1)) (i : Fin k) :
    markerRank label i.succ = markerRank label i.castSucc + 1 + useCount label i.succ := by
  classical
  let s := Finset.univ.filter (fun u => label u ≤ i.castSucc)
  let t := Finset.univ.filter (fun u => label u = i.succ)
  have hset : Finset.univ.filter (fun u => label u ≤ i.succ) = s ∪ t := by
    ext u
    simp only [s, t, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    change (label u).val ≤ i.val + 1 ↔ (label u).val ≤ i.val ∨ label u = i.succ
    rw [Fin.ext_iff]
    simp only [Fin.val_succ]
    omega
  have disj : Disjoint s t := by
    refine Finset.disjoint_left.mpr fun u hu ht => ?_
    have hle : label u ≤ i.castSucc := (Finset.mem_filter.mp hu).2
    have he : label u = i.succ := (Finset.mem_filter.mp ht).2
    rw [he] at hle
    exact Fin.castSucc_lt_succ.not_ge hle
  simp only [markerRank, useCount, hset, Finset.card_union_of_disjoint disj, Fin.val_succ, Fin.val_castSucc]
  change s.card + t.card + (i.val + 1) = s.card + i.val + 1 + t.card
  omega

end ParseBatchCounts

end BorderVNP
end Computability
end OAI
