import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

namespace OAI
/-! # Sorted passage ordinals from prefix counts -/

namespace Hierarchy.GridPassageRank

variable {α : Type*} [LinearOrder α] {B : ℕ}

/-- In the full increasing enumeration, the elements preceding index `j`
are the image of the initial interval below `j`. -/
theorem rank_orderEmbOfFin (s : Finset α) (j : Fin s.card) :
    (s.filter (· < s.orderEmbOfFin rfl j)).card = j.val := by
  classical
  let f := s.orderEmbOfFin rfl
  have range_f : Set.range f = (s : Set α) := s.range_orderEmbOfFin rfl
  have initial : s.filter (· < f j) = (Finset.Iio j).map f.toEmbedding := by
    ext a
    constructor
    · intro h
      obtain ⟨ha, hlt⟩ := Finset.mem_filter.mp h
      have inRange : a ∈ Set.range f := by
        rw [range_f]
        exact ha
      obtain ⟨i, rfl⟩ := inRange
      exact Finset.mem_map.mpr ⟨i, Finset.mem_Iio.mpr (f.lt_iff_lt.mp hlt), rfl⟩
    · intro h
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp h
      exact Finset.mem_filter.mpr ⟨s.orderEmbOfFin_mem rfl i, f.strictMono (Finset.mem_Iio.mp hi)⟩
  change (s.filter (· < f j)).card = j.val
  rw [initial, Finset.card_map, Fin.card_Iio]

theorem rank_orderEmbOfCardLe (s : Finset α) (h : B ≤ s.card) (i : Fin B) :
    (s.filter (· < s.orderEmbOfCardLe h i)).card = i.val :=
  rank_orderEmbOfFin s (i.castLE h)

/-- The rail whose prefix count is `i` is exactly rail `i` in the
mathematically selected initial block. -/
theorem orderEmbOfCardLe_eq_iff_rank (s : Finset α) (h : B ≤ s.card) (i : Fin B) {e : α}
    (he : e ∈ s) :
    s.orderEmbOfCardLe h i = e ↔ (s.filter (· < e)).card = i.val := by
  constructor
  · rintro rfl
    exact rank_orderEmbOfCardLe s h i
  · intro hr
    have member : e ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [s.range_orderEmbOfFin rfl]
      exact he
    obtain ⟨j, hj⟩ := member
    have same : i.castLE h = j := Fin.ext (show i.val = j.val by
      rw [← rank_orderEmbOfFin s j, hj, hr])
    change s.orderEmbOfFin rfl (i.castLE h) = e
    exact (congrArg (s.orderEmbOfFin rfl) same).trans hj

theorem orderEmbOfCardLe_eq_of_rank (s : Finset α) (h : B ≤ s.card) (i : Fin B) {e : α}
    (he : e ∈ s) (hr : (s.filter (· < e)).card = i.val) : s.orderEmbOfCardLe h i = e :=
  (orderEmbOfCardLe_eq_iff_rank s h i he).mpr hr

end Hierarchy.GridPassageRank

end OAI
