import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators

/-! # Pair names for the binary equality filter

For a nonzero direction, eliminate one pivot coordinate by adding a multiple of the
direction. Deleting this coordinate then names the coset of the two-element subgroup.
-/

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Binary

abbrev Word (b : ℕ) := Fin b → ZMod 2
abbrev Direction (b : ℕ) := {p : Word b // p ≠ 0}

@[simp] theorem card_word (b : ℕ) : Fintype.card (Word b) = 2 ^ b := by
  simp [Word, ZMod.card]

@[simp] theorem card_direction (b : ℕ) : Fintype.card (Direction b) = 2 ^ b - 1 := by
  classical
  rw [show Fintype.card (Direction b) = _ from Fintype.card_subtype_compl (· = (0 : Word b))]
  simp

instance {b : ℕ} : Nonempty (Direction (b + 1)) :=
  ⟨⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0)⟩⟩

private theorem has_pivot {b : ℕ} (p : Direction b) : ∃ i, p.val i = 1 := by
  by_contra! h
  exact p.property (funext fun i =>
    (show ∀ a : ZMod 2, a ≠ 1 → a = 0 by decide) _ (h i))

noncomputable def pivot {b : ℕ} (p : Direction b) : Fin b :=
  Classical.choose (has_pivot p)

@[simp] theorem pivot_bit {b : ℕ} (p : Direction b) : p.val (pivot p) = 1 :=
  Classical.choose_spec (has_pivot p)

/-- The smaller alphabet names each unordered pair in direction `p`. -/
noncomputable def pairName {b : ℕ} (p : Direction (b + 1)) (x : Word (b + 1)) : Word b :=
  fun i => x ((pivot p).succAbove i) + x (pivot p) * p.val ((pivot p).succAbove i)

theorem pairName_eq_iff {b : ℕ} (p : Direction (b + 1)) (x y : Word (b + 1)) :
    pairName p x = pairName p y ↔ x = y ∨ p.val = x + y := by
  constructor
  · intro he
    have hn (i) : x i + x (pivot p) * p.val i = y i + y (pivot p) * p.val i := by
      rcases (pivot p).eq_self_or_eq_succAbove i with rfl | ⟨j, rfl⟩
      · rw [pivot_bit]
        exact (show ∀ a b : ZMod 2, a + a * 1 = b + b * 1 by decide) _ _
      · exact congrFun he j
    by_cases hs : x (pivot p) = y (pivot p)
    · exact Or.inl (funext fun i => add_right_cancel ((hs ▸ hn i) : _))
    · exact Or.inr (funext fun i =>
        (show ∀ a b c d e : ZMod 2, a ≠ b → c + a * e = d + b * e → e = c + d by decide)
          _ _ _ _ _ hs (hn i))
  · rintro (rfl | he)
    · rfl
    · have hp : 1 = x (pivot p) + y (pivot p) := (pivot_bit p).symm.trans (congrFun he _)
      funext i
      simp only [pairName, he, Pi.add_apply]
      exact (show ∀ a b c d : ZMod 2, 1 = a + b →
        c + a * (c + d) = d + b * (c + d) by decide) _ _ _ _ hp

@[simp] theorem word_add_self {b : ℕ} (x : Word b) : x + x = 0 :=
  funext fun i => (show ∀ a : ZMod 2, a + a = 0 by decide) (x i)

/-- Adding the same binary word twice recovers the other summand. -/
@[simp] theorem word_add_cancel_right {b : ℕ} (x y : Word b) : x + y + y = x := by
  rw [add_assoc, word_add_self, add_zero]

/-- The unique direction pairing two different words. -/
def difference {b : ℕ} (x y : Word b) (h : x ≠ y) : Direction b :=
  ⟨x + y, fun hz => h (funext fun i =>
    (show ∀ a b : ZMod 2, a + b = 0 → a = b by decide) _ _ (congrFun hz i))⟩

@[simp] theorem difference_val {b : ℕ} (x y : Word b) (h : x ≠ y) :
    (difference x y h).val = x + y := rfl

theorem pairName_eq_iff_direction {b : ℕ} (p : Direction (b + 1)) (x y : Word (b + 1))
    (h : x ≠ y) : pairName p x = pairName p y ↔ p = difference x y h := by
  rw [pairName_eq_iff, or_iff_right h, Subtype.ext_iff]
  rfl

/-- Summing any coefficient over the directions whose pair names match keeps all
directions on equal inputs and exactly the difference direction on unequal inputs. -/
theorem matchingSum {b : ℕ} {M : Type*} [AddCommMonoid M] (x y : Word (b + 1))
    (f : Direction (b + 1) → M) :
    (∑ p, if pairName p x = pairName p y then f p else 0) =
      if h : x = y then ∑ p, f p else f (difference x y h) := by
  classical
  by_cases h : x = y
  · simp [h]
  · simp [h, pairName_eq_iff_direction _ _ _ h]

end Binary
end Sunflower
end Combinatorics
end OAI
