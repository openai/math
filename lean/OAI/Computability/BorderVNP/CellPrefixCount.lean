import OAI.Computability.BorderVNP.CellSparseChecks

/-!
# Unique prefix counts in the cell's Boolean witness bank

The row for prefix length `i` has one flag for each integer count from zero to the
cap. If a count exceeds the cap, all those flags are false. The transition checks
force every auxiliary bit, including flags on overflowed prefixes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Prefix

/-- Number of matches among the first `i` entries of a fixed assignment. -/
def count (m : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | i+1 => count m i + (m i).toNat

/-- There is at most one contribution per position. -/
theorem count_le (m : ℕ → Bool) (i : ℕ) : count m i ≤ i := by
  induction i with
  | zero => rfl
  | succ i ih => cases h : m i <;> simp [count,h] <;> omega

/-- Row-major address of a prefix flag. -/
def address (base cap i k : ℕ) : ℕ := base + i*(cap+1) + k

/-- The Boolean transition at count `k`; count zero has no predecessor on a match. -/
def next (m : Bool) (f : ℕ → Bool) (k : ℕ) : Bool :=
  ((!m) && f k) || (m && (if k = 0 then false else f (k-1)))

/-- Initial row: only zero matches occur in the empty prefix. -/
def Initial (cap : ℕ) (flags : ℕ → ℕ → Bool) : Prop :=
  ∀ k ≤ cap, flags 0 k = decide (k=0)

/-- A single row is obtained from its predecessor by a conditional unit shift. -/
def Step (cap i : ℕ) (m : Bool) (flags : ℕ → ℕ → Bool) : Prop :=
  ∀ k ≤ cap, flags (i+1) k = next m (flags i) k

/-- The auxiliary flags pass their initialization and all prefix transitions. -/
def Valid (copies cap : ℕ) (m : ℕ → Bool) (flags : ℕ → ℕ → Bool) : Prop :=
  Initial cap flags ∧ ∀ i < copies, Step cap i (m i) flags

private theorem next_canonical (m : ℕ → Bool) (i k : ℕ) :
    next (m i) (fun s => decide (count m i = s)) k = decide (count m (i+1) = k) := by
  cases hm : m i <;> cases k <;> simp [next,count,hm]

/-- Each auxiliary bit has the unique value prescribed by the true prefix count. -/
theorem valid_iff (copies cap : ℕ) (m : ℕ → Bool) (flags : ℕ → ℕ → Bool) :
    Valid copies cap m flags ↔ ∀ i ≤ copies, ∀ k ≤ cap, flags i k = decide (count m i = k) := by
  constructor
  · rintro ⟨h₀,hs⟩ i
    induction i with
    | zero =>
      intro _ k hk
      simpa [count, eq_comm] using h₀ k hk
    | succ i ih =>
      intro hi k hk
      rw [hs i (by omega) k hk, ← next_canonical, next, next, ih (by omega) k hk, ih (by omega) (k-1) (by omega)]
  · intro h
    refine ⟨fun k hk => ?_, fun i hi k hk => ?_⟩
    · simpa [count, eq_comm] using h 0 (Nat.zero_le _) k hk
    · rw [h (i+1) (by omega) k hk, ← next_canonical, next, next, h i hi.le k hk, h i hi.le (k-1) (by omega)]

/-- Zero-extend a finite flag table for the natural-index recurrence. -/
def getFlags {copies cap : ℕ} (f : Fin (copies+1) → Fin (cap+1) → Bool) (i k : ℕ) : Bool :=
  if hi : i ≤ copies then if hk : k ≤ cap then f ⟨i, by omega⟩ ⟨k,by omega⟩ else false else false

/-- The rectangular auxiliary bank has exactly one satisfying assignment for each
input match sequence. The finite indices cover every bit in the allocated block. -/
theorem existsUnique_flags (copies cap : ℕ) (m : ℕ → Bool) :
    ∃! f : Fin (copies+1) → Fin (cap+1) → Bool, Valid copies cap m (getFlags f) := by
  refine ⟨fun i k => decide (count m i.val = k.val), (valid_iff ..).mpr ?_, ?_⟩
  · intro i hi k hk
    simp [getFlags,hi,hk]
  · intro f h
    funext i k
    have hi : i.val ≤ copies := by omega
    have hk : k.val ≤ cap := by omega
    simpa [getFlags,hi,hk] using (valid_iff copies cap m (getFlags f)).mp h i.val hi k.val hk

end CellSparse.Prefix

end BorderVNP
end Computability
end OAI
