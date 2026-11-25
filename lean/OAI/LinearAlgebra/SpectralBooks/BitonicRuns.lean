import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Basic

namespace OAI
/-! # Circular lower cuts of a pair of sorted runs

Concatenate one increasing run with a second run in reverse. At a fixed threshold,
the second run contributes a suffix and the first contributes a prefix. Together
these form a single interval in circular order.
-/

namespace LinearAlgebra.SpectralBooks.Batcher

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- Membership of a position in the half-open interval starting at `s` of length
`m` in a circle of `N` positions, for `i, s < N` and `m ≤ N`. -/
def cyclicCut (N s m i : ℕ) : Prop :=
  (s ≤ i ∧ i < s + m) ∨ (s ≤ i + N ∧ i + N < s + m)

/-- The lower cut of an increasing run is a prefix. -/
private theorem sorted_prefix {a : Fin n → α} (ha : Monotone a) (c : α) :
    ∃ k ≤ n, ∀ i : Fin n, a i ≤ c ↔ i.val < k := by
  classical
  let P (k : ℕ) := ∀ i : Fin n, k ≤ i.val → c < a i
  have hbound : P n := fun i hi ↦ False.elim (i.isLt.not_ge hi)
  have hex : ∃ k, P k := ⟨n, hbound⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hbound, fun i ↦ ⟨?_, ?_⟩⟩
  · intro hi
    by_contra! h
    exact (Nat.find_spec hex i h).not_ge hi
  · intro hi
    by_contra! h
    apply (Nat.find_min hex hi)
    intro j hij
    exact h.trans_le (ha (show i ≤ j from hij))

/-- Two increasing runs form a bitonic sequence when the second is reversed:
every lower cut is a circular interval. -/
theorem sorted_pair_cyclicCut (hn : 0 < n) {a b : Fin n → α}
    (ha : Monotone a) (hb : Monotone b) (c : α) :
    ∃ s < n + n, ∃ m ≤ n + n,
      (∀ i : Fin n, a i ≤ c ↔ cyclicCut (n + n) s m i.val) ∧
      (∀ i : Fin n, b (Fin.rev i) ≤ c ↔ cyclicCut (n + n) s m (n + i.val)) := by
  obtain ⟨u, hu, hau⟩ := sorted_prefix ha c
  obtain ⟨v, hv, hbv⟩ := sorted_prefix hb c
  by_cases h : v = 0
  · subst v
    refine ⟨0, by omega, u, by omega, ?_, ?_⟩
    · intro i
      rw [hau]
      unfold cyclicCut
      omega
    · intro i
      rw [hbv]
      unfold cyclicCut
      omega
  · refine ⟨n + n - v, by omega, u + v, by omega, ?_, ?_⟩
    · intro i
      rw [hau]
      unfold cyclicCut
      omega
    · intro i
      rw [hbv, Fin.val_rev]
      unfold cyclicCut
      omega

end LinearAlgebra.SpectralBooks.Batcher

end OAI
