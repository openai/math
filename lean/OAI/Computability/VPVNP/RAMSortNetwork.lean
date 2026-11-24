import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.MinMax

/-!
# Batcher's bitonic sorting network

Lemma 10.1 of *VP and VNP differ over every field* sorts records by phases.
A phase on a block of size `2^(b+1)` compares its two halves at stride
`2^b`, then continues the merge in parallel in the two halves. The phase
begins with an ascending left half and a descending right half.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

/-- A contiguous block of records in the network. -/
abbrev Wires (b : ℕ) (α : Type*) := Fin (2 ^ b) → α

private theorem double_width (b : ℕ) : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by
  rw [Nat.pow_succ, Nat.mul_two]

/-- Read the first half of a block. -/
def lo {b : ℕ} {α : Type*} (x : Wires (b + 1) α) (i : Fin (2 ^ b)) : α :=
  x ⟨i, by rw [double_width]; omega⟩

/-- Read the second half of a block. -/
def hi {b : ℕ} {α : Type*} (x : Wires (b + 1) α) (i : Fin (2 ^ b)) : α :=
  x ⟨i + 2 ^ b, by rw [double_width]; omega⟩

/-- Write the two halves of a block. -/
def join {b : ℕ} {α : Type*} (x y : Wires b α) (i : Fin (2 ^ (b + 1))) : α :=
  if h : (i : ℕ) < 2 ^ b then x ⟨i, h⟩
  else y ⟨i - 2 ^ b, by have := double_width b; have := i.isLt; omega⟩

@[simp] theorem lo_join {b : ℕ} {α : Type*} (x y : Wires b α) :
    lo (join x y) = x := by funext i; simp [lo, join, i.isLt]

@[simp] theorem hi_join {b : ℕ} {α : Type*} (x y : Wires b α) :
    hi (join x y) = y := by funext i; simp [hi, join]

@[simp] theorem join_lo_hi {b : ℕ} {α : Type*} (x : Wires (b + 1) α) :
    join (lo x) (hi x) = x := by
  funext i
  simp only [join, lo, hi]
  split <;> congr 1
  apply Fin.ext
  change i.val - 2 ^ b + 2 ^ b = i.val
  omega

/-- Equality of blocks can be checked separately on each half. -/
theorem eq_of_halves {b : ℕ} {α : Type*} {x y : Wires (b + 1) α}
    (h₀ : lo x = lo y) (h₁ : hi x = hi y) : x = y := by
  rw [← join_lo_hi x, ← join_lo_hi y, h₀, h₁]

variable {α : Type*} [LinearOrder α]

/-- Value written at the smaller index of a comparator. -/
def lower (up : Bool) (x y : α) : α := if up then min x y else max x y

/-- Value written at the larger index of a comparator. -/
def upper (up : Bool) (x y : α) : α := if up then max x y else min x y

/-- One merge phase. The two recursive calls are parallel disjoint blocks. -/
def merge : (b : ℕ) → Bool → Wires b α → Wires b α
  | 0, _, x => x
  | b + 1, up, x =>
    join (merge b up (fun i ↦ lower up (lo x i) (hi x i)))
      (merge b up (fun i ↦ upper up (lo x i) (hi x i)))

/-- Sort a block, with ascending order requested by `true`. -/
def sort : (b : ℕ) → Bool → Wires b α → Wires b α
  | 0, _, x => x
  | b + 1, up, x => merge (b + 1) up (join (sort b true (lo x)) (sort b false (hi x)))

section Map

variable {β : Type*} [LinearOrder β]

omit [LinearOrder α] [LinearOrder β] in
private theorem map_join {b : ℕ} (f : α → β) (x y : Wires b α) :
    f ∘ join x y = join (f ∘ x) (f ∘ y) := by
  funext i
  simp only [Function.comp_apply, join]
  split <;> rfl

/-- Thresholding commutes with every comparator, and hence with a full merge. -/
theorem merge_map (f : α → β) (hf : Monotone f) (b : ℕ) (up : Bool) (x : Wires b α) :
    f ∘ merge b up x = merge b up (f ∘ x) := by
  induction b generalizing up with
  | zero => rfl
  | succ b ih =>
    simp only [merge, map_join, ih]
    congr 1 <;> congr 1 <;> funext i <;>
      cases up <;> simp [lower, upper, lo, hi, hf.map_min, hf.map_max]

/-- A monotone map can be pushed from the output to the input of the network. -/
theorem sort_map (f : α → β) (hf : Monotone f) (b : ℕ) (up : Bool) (x : Wires b α) :
    f ∘ sort b up x = sort b up (f ∘ x) := by
  induction b generalizing up with
  | zero => rfl
  | succ b ih =>
    simp only [sort, merge_map f hf, map_join, ih]
    rfl

end Map

end RAMSort

end VPVNP
end Computability
end OAI
