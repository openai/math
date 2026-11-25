import OAI.Hierarchy.DescentPackedMatchingCell
import OAI.Hierarchy.DescentPackedLocalMatch

namespace OAI
/-! # The fixed small-key table for complete local whole-item matching -/

namespace Hierarchy.DescentPacking.PackedMatch
open DescentSIMDLookup
open scoped BigOperators Classical
noncomputable section
variable {s : Shape}

def short (d n : ℕ) : Cell d := ⟨n%2^d,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
theorem short_val {d n : ℕ} (h : n<2^d) : (short d n).val=n := Nat.mod_eq_of_lt h

def need (x : Inputs s) (i : Fin s.packs) := (x.need i).val
def cap (x : Inputs s) (i : Fin s.bins) := (x.cap i).val

abbrev MatchedUnit (x : Inputs s) := PackedLocalMatch.Unit (need x) (cap x)

structure Bounded (x : Inputs s) : Prop where
  item : ∀i,need x i≤ s.limit
  thin : (∑i,need x i)≤ s.entries
  thick : (∑i,cap x i)≤ s.entries
  entries : s.entries<2^s.digit
  bins : s.bins≤2^s.digit

def amount (x : Inputs s) := Fintype.card (MatchedUnit x)

def describe (x : Inputs s) (u : Fin s.pairs) (r : PackedLocalMatch.Record)
    (t h : Fin s.entries) : Fin 12→Cell s.digit :=
  ![short s.digit 1,short s.digit r.accepted,short s.digit r.bin,short s.digit r.thin,short s.digit r.thick,
    x.thin t 0,x.thin t 1,x.thin t 2,x.thick h 0,x.thick h 1,x.thick h 2,x.profile u]

def transform (x : Inputs s) : Output s where
  count := short s.digit (amount x)
  row u :=
    match PackedLocalMatch.dense (need x) (cap x) s.limit u.val with
    | none=>fun _=>0
    | some r=>if h : r.thin<s.entries ∧ r.thick<s.entries then describe x u r ⟨_,h.1⟩ ⟨_,h.2⟩ else fun _=>0

/-- The same fixed function applies to every group, indexed only by its measured local digits. -/
def lookupCell (s : Shape) (z : Cell s.inputBits) : Cell s.outputBits := encodeOutput (transform (decodeInput s z))

theorem count_read (x : Inputs s) (h : Bounded x) :
    (decodeOutput s (lookupCell s (encodeInput x))).count.val=Fintype.card (MatchedUnit x) := by
  simp only [lookupCell,decode_encode,output_inverse,transform,amount]
  exact short_val ((PackedLocalMatch.count_le _ _).trans_lt (h.thin.trans_lt h.entries))

theorem unit_index (x : Inputs s) (h : Bounded x) (e : MatchedUnit x) :
    (PackedLocalMatch.fields (need x) (cap x) e).accepted<s.pairs := by
  have within : (∑i,need x i)≤ s.pairs := by
    simpa [Shape.pairs]
      using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>h.item i)
  exact (PackedLocalMatch.bounds (need x) (cap x) e).1.trans_le within

theorem unit_row (x : Inputs s) (h : Bounded x) (e : MatchedUnit x) :
    let v:=PackedLocalMatch.fields (need x) (cap x) e
    let i : Fin s.pairs:=⟨v.accepted,unit_index x h e⟩
    let bounds:=PackedLocalMatch.bounds (need x) (cap x) e
    (decodeOutput s (lookupCell s (encodeInput x))).row i =
      describe x i v ⟨v.thin,bounds.2.2.1.trans_le h.thin⟩ ⟨v.thick,bounds.2.2.2.trans_le h.thick⟩ := by
  have live := e.2.2.isLt.trans_le ((PackedLocalMatch.amount_at (need x) (cap x) e.2.1.val).le.trans (h.item _))
  have bd := PackedLocalMatch.bounds (need x) (cap x) e
  have inside : (PackedLocalMatch.fields (need x) (cap x) e).thin < s.entries ∧
      (PackedLocalMatch.fields (need x) (cap x) e).thick < s.entries :=
    ⟨bd.2.2.1.trans_le h.thin,bd.2.2.2.trans_le h.thick⟩
  simp only [lookupCell,decode_encode,output_inverse,transform,PackedLocalMatch.dense_at _ _ e live,dite_eq_left inside]

theorem empty_row (x : Inputs s) (h : Bounded x) (i : Fin s.pairs) (past : amount x ≤ i.val) :
    (decodeOutput s (lookupCell s (encodeInput x))).row i=fun _=>0 := by
  have empty := (PackedLocalMatch.dense_none (need x) (cap x) i.val h.item).2 past
  simp only [lookupCell,decode_encode,output_inverse,transform,empty]

end
end Hierarchy.DescentPacking.PackedMatch

end OAI
