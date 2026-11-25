import OAI.Computability.BorderVNP.CellPacketGeometryReferences

/-! # Static geometry ordinal formulas

The actual absolute indices used as the public descriptor operands depend only on
the lengths of the local public encodings in their original order. A change of cell
labels or of scalar payloads at fixed lengths leaves these indices fixed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.SiteWords

open CellSparse CellSparse.Packet
open CellSparse.Packet.Source (Box boxPart)

variable {C : ℕ} {S Orig : Type}

/-- Length of a source block in raw order ignores all current cell labels. -/
theorem siteRows_length (owner : S → Fin C) (emit : S → List ℕ) (sites : List S) :
    (siteRows owner emit sites).length = (sites.map fun s => (emit s).length).sum := by
  simp [siteRows,List.length_flatMap,tag]

private theorem constant_length (owner : S → Fin C) (emit : S → List ℕ) (sites : List S) (n : ℕ)
    (shape : ∀ s, (emit s).length = n) : (siteRows owner emit sites).length = sites.length*n := by
  rw [siteRows_length]
  simp only [shape]
  rw [show (fun _ : S => n) = Function.const S n from rfl,List.map_const,List.sum_replicate_nat]

private theorem pos_cast {raw : List (Fin C × ℕ)} {c : Fin C} {a b : ℕ} (ab : a=b)
    (x : Position raw c a) (t : Position raw c a = Position raw c b) :
    (t.mp x).ordinal = x.ordinal := by subst b; rfl

private theorem pos_rec {raw : List (Fin C × ℕ)} {c : Fin C} {a b : ℕ} (h : a=b)
    (x : Position raw c a) : (h ▸ x : Position raw c b).ordinal = x.ordinal := by subst b; rfl

private theorem span_rec {raw : List (Fin C × ℕ)} {c : Fin C} {a b n : ℕ} (h : a=b)
    (x : Span raw c a n) :
    (h ▸ x : Span raw c b n).first.ordinal = x.first.ordinal ∧
    (h ▸ x : Span raw c b n).last.ordinal = x.last.ordinal := by subst b; exact ⟨rfl,rfl⟩

private theorem position_val {raw : List (Fin C × ℕ)} (c : Fin C) (pre : List (Fin C × ℕ))
    (xs : List ℕ) (post : List (Fin C × ℕ)) (split : raw = pre++tag c xs++post) (i : Fin xs.length) :
    (position c pre xs post split i).ordinal.val = pre.length+i.val := by subst raw; rfl

private theorem span_first {raw : List (Fin C × ℕ)} (c : Fin C) (pre : List (Fin C × ℕ))
    (xs : List ℕ) (post : List (Fin C × ℕ)) (split : raw = pre++tag c xs++post) (ne : 0<xs.length) :
    (span c pre xs post split ne).first.ordinal.val = pre.length := by
  exact position_val c pre xs post split ⟨0,ne⟩

private theorem span_last {raw : List (Fin C × ℕ)} (c : Fin C) (pre : List (Fin C × ℕ))
    (xs : List ℕ) (post : List (Fin C × ℕ)) (split : raw = pre++tag c xs++post) (ne : 0<xs.length) :
    (span c pre xs post split ne).last.ordinal.val = pre.length+(xs.length-1) := by
  unfold span
  simp only
  rw [pos_cast (by dsimp only; omega)]
  exact position_val c pre xs post split ⟨xs.length-1,by omega⟩

/-- Each cell header occupies exactly two raw words at its hardwired cell offset. -/
theorem Directory.header_ordinals (D : Directory S Orig C) (c : Fin C) :
    (D.headerSpan c).first.ordinal.val = c.val*2 ∧ (D.headerSpan c).last.ordinal.val = c.val*2+1 := by
  unfold Directory.headerSpan
  simp only
  rw [(span_rec _ _).1,(span_rec _ _).2,span_first,span_last]
  rw [constant_length _ _ _ 2 (fun _ => rfl)]
  simp

/-- Sum of public word lengths of all preceding sites and the preceding boxes at
this site. It counts the global source columns after the two-word cell headers. -/
def Directory.boxOffset (D : Directory S Orig C) (i : Fin D.sites.length)
    (j : Fin (D.boxes D.sites[i.val]).length) :=
  C*2 + ((D.sites.take i.val).map fun s => (boxWords (D.boxes s)).length).sum +
    (boxWords ((D.boxes D.sites[i.val]).take j.val)).length

private theorem headers_length (D : Directory S Orig C) : D.headers.length = C*2 := by
  unfold Directory.headers cellRows
  rw [constant_length _ _ _ 2 (fun _ => rfl),List.length_finRange]

private theorem counts_length (D : Directory S Orig C) : D.counts.length = C := by
  unfold Directory.counts cellRows
  rw [constant_length _ _ _ 1 (fun _ => rfl),List.length_finRange,Nat.mul_one]

/-- A known box always occupies its static public range regardless of its cell. -/
theorem Directory.box_ordinals (D : Directory S Orig C) (i : Fin D.sites.length)
    (j : Fin (D.boxes D.sites[i.val]).length) (fs : List Factor)
    (known : (D.boxes D.sites[i.val])[j.val] = Sum.inl fs) :
    (D.boxSpan i j fs known).first.ordinal.val = D.boxOffset i j ∧
    (D.boxSpan i j fs known).last.ordinal.val = D.boxOffset i j + ((fieldList factor fs).length-1) := by
  unfold Directory.boxSpan
  simp only [span_first,span_last,List.length_append,siteRows_length,headers_length,tag,List.length_map,
    Directory.boxOffset,true_and]

/-- Index of the record-list count in the global unsorted public word stream. -/
def Directory.countOffset (D : Directory S Orig C) (c : Fin C) :=
  C*2 + (D.sites.map fun s => (boxWords (D.boxes s)).length).sum + c.val

/-- First raw word of the report for the specified cell. -/
def Directory.reportOffset (D : Directory S Orig C) (c : Fin C) :=
  C*2 + (D.sites.map fun s => (boxWords (D.boxes s)).length).sum + C +
    (D.sites.map fun s => ((D.rows s).flatMap record).length).sum +
    (((List.finRange C).take c.val).map fun a => (fieldList vector (D.reports a)).length).sum

/-- The final reference joins raw ordinals in the static count and report sections. -/
theorem Directory.tail_ordinals (D : Directory S Orig C) (c : Fin C) :
    (D.tailSpan c).first.ordinal.val = D.countOffset c ∧
    (D.tailSpan c).last.ordinal.val = D.reportOffset c + ((fieldList vector (D.reports c)).length-1) := by
  unfold Directory.tailSpan
  simp only
  rw [pos_rec,pos_rec,span_first,span_last]
  simp only [List.length_append]
  rw [constant_length id (fun a => [(D.cellRecords a).length]) _ 1 (fun _ => rfl)]
  simp [Directory.countOffset,Directory.reportOffset,headers_length,counts_length,Directory.boxRows,
    Directory.recordRows,siteRows_length]

end CellPacketGeometry.SiteWords

end BorderVNP
end Computability
end OAI
