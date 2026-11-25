import OAI.Computability.BorderVNP.RoutingISATableAddressImage

/-! # The physical ordinal table partitions each unordered demand list

Every bit of every nonlocal descriptor has exactly one position in its pair. Conversely,
every position below the stored pair width comes from one descriptor and one local bit.
Empty and co-located intervals contribute no positions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open Finset

/-- A bit of a nonlocal descriptor for the specified unordered team pair. -/
abbrev TableLayout.RecordBit (l : TableLayout) (row : ℕ → TableRow) (key : ℕ) :=
  {x : Fin l.count × ℕ // (row x.1).first ≠ (row x.1).second ∧
    l.pairKey (row x.1).first (row x.1).second = key ∧ x.2 < (row x.1).width}

private theorem covers_prefix (l : TableLayout) (row : ℕ → TableRow) (key n q : ℕ)
    (hq : q < l.pairWidth row n key) :
    ∃ i < n, (row i).first ≠ (row i).second ∧ l.pairKey (row i).first (row i).second = key ∧
      l.ordinal row i ≤ q ∧ q < l.ordinal row i+(row i).width := by
  induction n with
  | zero => simp [TableLayout.pairWidth] at hq
  | succ n ih =>
    by_cases hprev : q < l.pairWidth row n key
    · obtain ⟨i,hi,hr⟩ := ih hprev
      exact ⟨i, hi.trans (Nat.lt_succ_self _), hr⟩
    · have he : l.pairWidth row (n+1) key = l.pairWidth row n key +
          if (row n).first ≠ (row n).second ∧ l.pairKey (row n).first (row n).second = key then (row n).width else 0 :=
        Finset.sum_range_succ ..
      rw [he] at hq
      split at hq
      next h =>
        have ho : l.ordinal row n = l.pairWidth row n key := by simp [TableLayout.ordinal, h.1, h.2]
        exact ⟨n,Nat.lt_succ_self n,h.1,h.2,ho ▸ Nat.le_of_not_gt hprev,ho ▸ hq⟩
      next => omega

/-- Add the prefix before a descriptor to its local bit number. -/
def TableLayout.recordBitOrdinal (l : TableLayout) (row : ℕ → TableRow) (key : ℕ)
    (b : l.RecordBit row key) : Fin (l.pairWidth row l.count key) :=
  ⟨l.ordinal row b.val.1+b.val.2, (Nat.add_lt_add_left b.property.2.2 _).trans_le
    ((l.ordinal_add_width_le row b.val.1.isLt b.property.1).trans_eq
      (congrArg (l.pairWidth row l.count) b.property.2.1))⟩

/-- The half-open intervals from distinct records of the same unordered pair are disjoint. -/
theorem TableLayout.recordBitOrdinal_injective (l : TableLayout) (row : ℕ → TableRow) (key : ℕ) :
    Function.Injective (l.recordBitOrdinal row key) := by
  rintro ⟨⟨i,a⟩,hi⟩ ⟨⟨j,b⟩,hj⟩ eq
  have val := congrArg Fin.val eq
  change l.ordinal row i+a = l.ordinal row j+b at val
  have same : i = j := by
    rcases lt_trichotomy i j with h | h | h
    · have hsep := l.ordinal_order row h hi.1 hj.1 (hi.2.1.trans hj.2.1.symm)
      have ha : a < (row i).width := hi.2.2
      omega
    · exact h
    · have hsep := l.ordinal_order row h hj.1 hi.1 (hj.2.1.trans hi.2.1.symm)
      have hb : b < (row j).width := hj.2.2
      omega
  subst j
  exact Subtype.ext (Prod.ext rfl (Nat.add_left_cancel val))

/-- Every bit of a physically transmitted demand list belongs to an actual descriptor. -/
theorem TableLayout.recordBitOrdinal_surjective (l : TableLayout) (row : ℕ → TableRow) (key : ℕ) :
    Function.Surjective (l.recordBitOrdinal row key) := by
  intro q
  obtain ⟨i,hi,hne,hk,hle,hlt⟩ := covers_prefix l row key l.count q.val q.isLt
  refine ⟨⟨(⟨i,hi⟩,q.val-l.ordinal row i),hne,hk,by change q.val-l.ordinal row i < (row i).width; omega⟩,
    Fin.ext ?_⟩
  change l.ordinal row i + (q.val-l.ordinal row i) = q.val
  omega

/-- The exact bijection from nonlocal interval bits to the finite ordinal used for
round-robin relay assignment. Its forward map is the native prefix-plus-local-bit address. -/
noncomputable def TableLayout.recordBitsEquiv (l : TableLayout) (row : ℕ → TableRow) (key : ℕ) :
    l.RecordBit row key ≃ Fin (l.pairWidth row l.count key) :=
  Equiv.ofBijective (l.recordBitOrdinal row key) ⟨l.recordBitOrdinal_injective row key, l.recordBitOrdinal_surjective row key⟩

/-- In the final native table, reading a record's starting ordinal and adding its bit
offset gives the forward value of the descriptor bijection. -/
theorem TableLayout.Image.ordinal_read {l : TableLayout} {row : ℕ → TableRow} {before after : ℕ → ℕ}
    (image : l.Image row before after) (key : ℕ) (b : l.RecordBit row key) :
    after (l.ordinals+b.val.1)+b.val.2 = (l.recordBitsEquiv row key b).val :=
  congrArg (· + b.val.2) (image.ordinals _ b.val.1.isLt)

end RoutingISA

end BorderVNP
end Computability
end OAI
