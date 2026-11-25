import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Max

/-!
# Directed rectangles for distinct binary letters

An ordered pair of distinct `k`-bit letters determines its first differing bit,
its common prefix, and the bit on the source side. These data index rectangles
partitioning the unequal pairs. Each letter occurs in exactly `k` rectangles on
each side, even though the alphabet has `2 ^ k` letters.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LetterRectangles

abbrev Letter (k : ℕ) := Fin k → Bool

abbrev Key (k : ℕ) := (i : Fin k) × ((Fin i.val → Bool) × Bool)

private def letterPrefix {k : ℕ} (x : Letter k) (i : Fin k) : Fin i.val → Bool :=
  fun j => x ⟨j, lt_trans j.isLt i.isLt⟩

/-- The orientation of the key is always the source letter's bit. -/
def keyAt {k : ℕ} (side : Bool) (x : Letter k) (i : Fin k) : Key k :=
  ⟨i, letterPrefix x i, if side then !(x i) else x i⟩

/-- `false` selects the source side and `true` the destination side. -/
def Incident {k : ℕ} (side : Bool) (r : Key k) (x : Letter k) : Prop :=
  r = keyAt side x r.1

instance {k : ℕ} (side : Bool) (r : Key k) (x : Letter k) : Decidable (Incident side r x) :=
  inferInstanceAs (Decidable (r = keyAt side x r.1))

/-- For a fixed source or destination letter there is exactly one incident key
at every possible differing bit position. -/
def incidentEquiv {k : ℕ} (side : Bool) (x : Letter k) :
    {r : Key k // Incident side r x} ≃ Fin k where
  toFun r := r.val.1
  invFun i := ⟨keyAt side x i, rfl⟩
  left_inv r := Subtype.ext r.property.symm
  right_inv _ := rfl

theorem card_incident {k : ℕ} (side : Bool) (x : Letter k) :
    Fintype.card {r : Key k // Incident side r x} = k := by
  simpa using Fintype.card_congr (incidentEquiv side x)

private theorem first_difference {k : ℕ} {x y : Letter k} {r : Key k}
    (hx : Incident false r x) (hy : Incident true r y) :
    x r.1 ≠ y r.1 ∧ ∀ j < r.1, x j = y j := by
  obtain ⟨i, pre, b⟩ := r
  simp only [Incident, keyAt, Bool.false_eq_true, ↓reduceIte, Sigma.mk.inj_iff,
    heq_eq_eq, true_and, Prod.mk.injEq] at hx hy
  constructor
  · have hb := hx.2.symm.trans hy.2
    cases hx' : x i <;> cases hy' : y i <;> simp_all
  · intro j hj
    exact congrFun (hx.1.symm.trans hy.1) ⟨j, hj⟩

theorem unequal_of_incident {k : ℕ} {x y : Letter k} {r : Key k}
    (hx : Incident false r x) (hy : Incident true r y) : x ≠ y := by
  intro h
  exact (first_difference hx hy).1 (congrFun h _)

theorem unequal_iff_unique {k : ℕ} (x y : Letter k) :
    x ≠ y ↔ ∃! r : Key k, Incident false r x ∧ Incident true r y := by
  classical
  constructor
  · intro h
    let s := Finset.univ.filter fun i => x i ≠ y i
    have hs : s.Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let i := s.min' hs
    have hi : i ∈ s := Finset.min'_mem _ _
    have hxy : x i ≠ y i := (Finset.mem_filter.mp hi).2
    have hpre : ∀ j < i, x j = y j := by
      intro j hj
      by_contra hne
      exact (not_le_of_gt hj) (s.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩))
    have hdest : Incident true (keyAt false x i) y := by
      unfold Incident keyAt
      congr 2
      · funext j
        exact hpre ⟨j, lt_trans j.isLt i.isLt⟩ j.isLt
      · cases hx' : x i <;> cases hy' : y i <;> simp_all
    refine ⟨keyAt false x i, ⟨rfl, hdest⟩, ?_⟩
    intro r hr
    have hr' := first_difference hr.1 hr.2
    have hri : r.1 = i := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · exact hr'.1 (hpre _ hlt)
      · exact hxy (hr'.2 _ hgt)
    exact hr.1.trans (congrArg (keyAt false x) hri)
  · rintro ⟨r, hr, _⟩
    exact unequal_of_incident hr.1 hr.2

end LetterRectangles

end NearSquareRoot
end Computability
end OAI
