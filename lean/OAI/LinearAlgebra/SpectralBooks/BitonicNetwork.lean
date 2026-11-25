import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Order.MinMax
import Mathlib.Tactic

namespace OAI
/-! # Batcher's comparator schedule

A network on `2^k` wires consists of fixed rewirings, disjoint parallel
subnetworks, and layers of pairwise minimum/maximum comparators. Both children
of a parallel constructor have their own wires and comparators.
-/

namespace LinearAlgebra.SpectralBooks.Batcher

/-- A block of `2^k` ordered wires. -/
abbrev Wires (k : ℕ) (α : Type*) := Fin (2^k) → α

/-- Identify two consecutive blocks with one block of twice their width. -/
def splitEquiv (k : ℕ) : Fin (2^k) ⊕ Fin (2^k) ≃ Fin (2^(k+1)) :=
  finSumFinEquiv.trans (finCongr (by rw [pow_succ, Nat.mul_two]))

/-- Index in the lower half of the block. -/
def low {k : ℕ} (i : Fin (2^k)) : Fin (2^(k+1)) := splitEquiv k (.inl i)

/-- Index in the upper half of the block. -/
def high {k : ℕ} (i : Fin (2^k)) : Fin (2^(k+1)) := splitEquiv k (.inr i)

@[simp] theorem low_val {k : ℕ} (i : Fin (2^k)) : (low i).val = i.val := rfl
@[simp] theorem high_val {k : ℕ} (i : Fin (2^k)) : (high i).val = 2^k+i.val := rfl

theorem low_or_high {k : ℕ} (j : Fin (2^(k+1))) :
    (∃ i, j = low i) ∨ (∃ i, j = high i) := by
  obtain ⟨i, rfl⟩ := (splitEquiv k).surjective j
  cases i with
  | inl i => exact Or.inl ⟨i, rfl⟩
  | inr i => exact Or.inr ⟨i, rfl⟩

/-- Concatenate consecutive blocks without any comparator. -/
def join {k : ℕ} {α : Type*} (a b : Wires k α) : Wires (k+1) α :=
  Sum.elim a b ∘ (splitEquiv k).symm

@[simp] theorem join_low {k : ℕ} {α : Type*} (a b : Wires k α) (i : Fin (2^k)) :
    join a b (low i) = a i := by simp [join, low]

@[simp] theorem join_high {k : ℕ} {α : Type*} (a b : Wires k α) (i : Fin (2^k)) :
    join a b (high i) = b i := by simp [join, high]

/-- Syntax for a fixed, data-independent comparator schedule. -/
inductive Network : ℕ → Type
  | nil {k} : Network k
  | reverse {k} : Network k
  | compareHalves {k} : Network (k+1)
  | parallel {k} (l r : Network k) : Network (k+1)
  | seq {k} (a b : Network k) : Network k

/-- Apply the comparator schedule to ordered records. -/
def Network.eval {k : ℕ} {α : Type*} [LinearOrder α] : Network k → Wires k α → Wires k α
  | .nil, x => x
  | .reverse, x => x ∘ Fin.rev
  | .compareHalves, x => join (fun i => min (x (low i)) (x (high i)))
      (fun i => max (x (low i)) (x (high i)))
  | .parallel l r, x => join (l.eval (x ∘ low)) (r.eval (x ∘ high))
  | .seq a b, x => b.eval (a.eval x)

/-- The fixed-depth recursive bitonic merging schedule. -/
def mergeNet : (k : ℕ) → Network k
  | 0 => .nil
  | k+1 => .seq .compareHalves (.parallel (mergeNet k) (mergeNet k))

@[simp] theorem mergeNet_succ_eval {k : ℕ} {α : Type*} [LinearOrder α] (x : Wires (k+1) α) :
    (mergeNet (k+1)).eval x =
      join ((mergeNet k).eval (fun i => min (x (low i)) (x (high i))))
        ((mergeNet k).eval (fun i => max (x (low i)) (x (high i)))) := by
  simp [mergeNet, Network.eval, Function.comp_def]

/-- Sort the two halves, reverse the second, then merge the resulting bitonic block. -/
def sortNet : (k : ℕ) → Network k
  | 0 => .nil
  | k+1 => .seq (.parallel (sortNet k) (.seq (sortNet k) .reverse)) (mergeNet (k+1))

@[simp] theorem sortNet_succ_eval {k : ℕ} {α : Type*} [LinearOrder α] (x : Wires (k+1) α) :
    (sortNet (k+1)).eval x = (mergeNet (k+1)).eval
      (join ((sortNet k).eval (x ∘ low)) (((sortNet k).eval (x ∘ high)) ∘ Fin.rev)) := rfl

/-- Applying an order-preserving map before or after the network gives the same wires. -/
theorem Network.eval_comp {k : ℕ} {α β : Type*} [LinearOrder α] [LinearOrder β]
    (N : Network k) (f : α → β) (hf : Monotone f) (a : Wires k α) :
    N.eval (f ∘ a) = f ∘ N.eval a := by
  induction N with
  | nil => rfl
  | reverse => rfl
  | compareHalves =>
    funext i
    rcases low_or_high i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp [Network.eval, hf.map_min]
    · simp [Network.eval, hf.map_max]
  | parallel l r hl hr =>
    funext i
    rcases low_or_high i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simpa [Network.eval, Function.comp_assoc] using congrFun (hl (a ∘ low)) j
    · simpa [Network.eval, Function.comp_assoc] using congrFun (hr (a ∘ high)) j
  | seq a b ha hb => simp only [Network.eval, ha, hb]

/-- Number of two-input compare-exchanges, counting each physical pair in each layer. -/
def Network.comparisons {k : ℕ} : Network k → ℕ
  | .nil | .reverse => 0
  | .compareHalves (k := d) => 2^d
  | .parallel l r => l.comparisons + r.comparisons
  | .seq a b => a.comparisons + b.comparisons

/-- Number of parallel comparator layers. Fixed permutations are wire reindexings. -/
def Network.depth {k : ℕ} : Network k → ℕ
  | .nil | .reverse => 0
  | .compareHalves => 1
  | .parallel l r => max l.depth r.depth
  | .seq a b => a.depth + b.depth

/-- The merging network on `2^k` inputs uses `k 2^k / 2` comparators. -/
theorem mergeNet_comparisons (k : ℕ) : 2*(mergeNet k).comparisons = 2^k*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [mergeNet, Network.comparisons, pow_succ]
    nlinarith

/-- The sorting network on `2^k` inputs uses `2^k k(k+1)/4` comparators. -/
theorem sortNet_comparisons (k : ℕ) : 4*(sortNet k).comparisons = 2^k*k*(k+1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hm := mergeNet_comparisons (k+1)
    rw [pow_succ] at hm
    simp only [sortNet, Network.comparisons, pow_succ]
    nlinarith

@[simp] theorem mergeNet_depth (k : ℕ) : (mergeNet k).depth = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [mergeNet, Network.depth, ih, Nat.add_comm]

/-- Batcher's sorting schedule has `k(k+1)/2` parallel comparator layers. -/
theorem sortNet_depth (k : ℕ) : 2*(sortNet k).depth = k*(k+1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [sortNet, Network.depth, Nat.add_zero, max_self, mergeNet_depth]
    nlinarith

end LinearAlgebra.SpectralBooks.Batcher

end OAI
