import OAI.Computability.BorderVNP.RoutingISATableBounds

/-! # The accumulating unordered width and ordinal arrays

One store saves the old pair width at the record's ordinal slot. A nonlocal record
then updates its single pair-width entry. This recurrence proves the exact prefix
image and preserves all addresses outside the two writable arrays.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open Finset

/-- Memory update for one complete interval in the record pass. -/
def TableLayout.storeRecord (l : TableLayout) (r : TableRow) (i : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  let k := l.widths+l.pairKey r.first r.second
  if r.first = r.second then Function.update mem (l.ordinals+i) 0
  else Function.update (Function.update mem (l.ordinals+i) (mem k)) k (mem k+r.width)

/-- The full width table, completed ordinal prefix, and preserved external contents
after processing exactly the first `i` descriptors. -/
structure TableLayout.IntervalImage (l : TableLayout) (row : ℕ → TableRow)
    (before : ℕ → ℕ) (i : ℕ) (mem : ℕ → ℕ) : Prop where
  /-- The square table records every unordered pair's cumulative width. -/
  widths : ∀ k < l.teams^2, mem (l.widths+k) = l.pairWidth row i k
  /-- Every processed interval has the starting ordinal of that interval. -/
  ordinals : ∀ j < i, mem (l.ordinals+j) = l.ordinal row j
  /-- Other arrays and unallocated addresses retain their initial contents. -/
  outside : ∀ x, ¬ l.contains .widths x → ¬ l.contains .ordinals x → mem x = before x

/-- A transmission's accessed fields lie in the actual allocated record array. -/
theorem TableLayout.contains_record {l : TableLayout} {i q : ℕ} (hi : i < l.count) (hq : q < 7) :
    l.contains .records (7*i+l.records+q) := by
  change l.records ≤ _ ∧ _ < l.records+7*l.count
  omega

/-- Neither of the two output stores can alter a source descriptor. -/
theorem TableLayout.IntervalImage.recordsMatch {l : TableLayout} {w i : ℕ} {row : ℕ → TableRow}
    {before mem : ℕ → ℕ} (h : l.IntervalImage row before i mem) (al : l.Allocated w)
    (initial : l.recordsMatch row before) : l.recordsMatch row mem := by
  intro j hj
  have hold (q : ℕ) (hq : q < 7) : mem (7*j+l.records+q) = before (7*j+l.records+q) :=
    h.outside _ (al.separate .records .widths _ (by decide) (l.contains_record hj hq))
      (al.separate .records .ordinals _ (by decide) (l.contains_record hj hq))
  have e := initial j hj
  dsimp only
  rw [← Nat.add_zero (7*j+l.records), hold 0 (by decide), Nat.add_zero, hold 1 (by decide),
    hold 2 (by decide), hold 3 (by decide)]
  exact e

/-- The prefix invariant is preserved by the exact ordinal and width stores. -/
theorem TableLayout.IntervalImage.store {l : TableLayout} {w i : ℕ} {row : ℕ → TableRow}
    {before mem : ℕ → ℕ} (h : l.IntervalImage row before i mem) (al : l.Allocated w)
    (fit : l.RowsFit w row) (hi : i < l.count) :
    l.IntervalImage row before (i+1) (l.storeRecord (row i) i mem) := by
  have hk : (l.pairKey (row i).first (row i).second) < l.teams^2 := l.pairKey_lt (fit.labels i hi).2.1 (fit.labels i hi).2.2
  have ha : l.contains .widths (l.widths+(l.pairKey (row i).first (row i).second)) := l.contains_offset (a := .widths) hk
  have ho : l.contains .ordinals (l.ordinals+i) := l.contains_offset (a := .ordinals) hi
  have disjoint (k j : ℕ) (kfit : k < l.teams^2) (jfit : j < l.count) : l.widths+k ≠ l.ordinals+j :=
    fun e => al.separate .widths .ordinals _ (by decide) (l.contains_offset (a := .widths) kfit)
      (e ▸ l.contains_offset (a := .ordinals) jfit)
  constructor
  · intro k kfit
    have hd := disjoint k i kfit hi
    rw [TableLayout.pairWidth, Finset.sum_range_succ]
    by_cases eq : (row i).first = (row i).second
    · simp only [TableLayout.storeRecord, eq, ite_true, Function.update_of_ne hd,
        ne_eq, not_true_eq_false, false_and, ite_false, Nat.add_zero]
      exact h.widths k kfit
    · by_cases he : (l.pairKey (row i).first (row i).second) = k
      · subst k
        simpa [TableLayout.storeRecord, eq, TableLayout.pairWidth] using congrArg (· + (row i).width) (h.widths (l.pairKey (row i).first (row i).second) hk)
      · have hn : l.widths+k ≠ l.widths+(l.pairKey (row i).first (row i).second) := by omega
        simp only [TableLayout.storeRecord, eq, ite_false, Function.update_of_ne hn, Function.update_of_ne hd,
          he, and_false, Nat.add_zero]
        exact h.widths k kfit
  · intro j hj
    have hji : j ≤ i := by omega
    have hd := (disjoint (l.pairKey (row i).first (row i).second) j hk (by omega)).symm
    by_cases e : j = i
    · subst j
      by_cases eq : (row i).first = (row i).second
      · simp only [TableLayout.storeRecord, TableLayout.ordinal, eq, ite_true, Function.update_self]
      · simpa only [TableLayout.storeRecord, TableLayout.ordinal, eq, ite_false, Function.update_of_ne hd,
          Function.update_self] using h.widths (l.pairKey (row i).first (row i).second) hk
    · have hn : l.ordinals+j ≠ l.ordinals+i := by omega
      by_cases eq : (row i).first = (row i).second <;>
        simpa [TableLayout.storeRecord, eq, Function.update_of_ne hd, Function.update_of_ne hn]
          using h.ordinals j (by omega)
  · intro x hn ho'
    have ha' : x ≠ l.widths+(l.pairKey (row i).first (row i).second) := fun e => hn (e ▸ ha)
    have ho'' : x ≠ l.ordinals+i := fun e => ho' (e ▸ ho)
    by_cases eq : (row i).first = (row i).second <;>
      simpa [TableLayout.storeRecord, eq, Function.update_of_ne ha', Function.update_of_ne ho'']
        using h.outside x hn ho'

end RoutingISA

end BorderVNP
end Computability
end OAI
