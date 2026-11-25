import OAI.Computability.BorderVNP.CellPacketGeometryHistoryRead
import OAI.Computability.BorderVNP.CellPacketGeometryOrderedRun

/-! # Fixed geometry slots for the complete frozen history and final binding rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open CellSparse CellSparse.Packet Packing.Inherited Packing.BankPacket Packing.Word
open FrozenTape LiveWords

variable {a C cap d t : ℕ} {R B U V E Orig : Type}

/-- One anchor for every physical site ID, one spare anchor for all inactive
source slots, then the complete frozen history and the final incidence bindings. -/
abbrev Slot (a : ℕ) (R U : Type) := Fin a ⊕ Option (R ⊕ U)

/-- Public scalar field roles at a physical row piece: final bit and box
offsets followed by the immutable numerically encoded record columns. -/
abbrev Field (cap : ℕ) := Bool ⊕ Fin cap

/-- The global chronological order of public rows, with a separate anchor
slot for every physical private/public box table. -/
def roster (a : ℕ) (S : Schema R B) (L : Schema U V) : List (Slot a R U) :=
  (List.finRange a).map Sum.inl ++ [.inr none] ++ S.rows.map (fun r => .inr (some (.inl r))) ++
    L.rows.map (fun r => .inr (some (.inr r)))

/-- Global ordinal of the real site anchor. -/
def anchorSlot (S : Schema R B) (L : Schema U V) (j : Fin a) : Fin (roster a S L).length :=
  ⟨j.val,by simp [roster]; omega⟩

/-- Real records are grouped ahead of the inactive anchor, which is distinct
from every old or newly introduced network site. -/
def holeSlot (a : ℕ) (S : Schema R B) (L : Schema U V) : Fin (roster a S L).length :=
  ⟨a,by simp [roster]⟩

theorem anchorSlot_get (S : Schema R B) (L : Schema U V) (j : Fin a) :
    (roster a S L).get (anchorSlot S L j) = Sum.inl j := by
  simp [anchorSlot,roster,List.get_eq_getElem,List.append_assoc,List.getElem_append_left]

theorem holeSlot_get (a : ℕ) (S : Schema R B) (L : Schema U V) :
    (roster a S L).get (holeSlot a S L) = Sum.inr none := by
  simp [holeSlot,roster,List.get_eq_getElem,List.append_assoc,List.getElem_append_right]

/-- Active-owner interpretation of the native enable and sparse public owner words. -/
def name (a : ℕ) (x : Pins R B d → Bool) (r : R) : Option (Fin a) :=
  if h : x (.inl (r,.inl ())) ∧ owner x r < a then some ⟨owner x r,h.2⟩ else none

/-- A real index is selected exactly when both native source columns select it. -/
theorem name_eq (x : Pins R B d → Bool) (r : R) (j : Fin a) :
    name a x r = some j ↔ x (.inl (r,.inl ())) = true ∧ owner x r=j.val := by
  unfold name
  split <;> rename_i h
  · simp [h.1,Fin.ext_iff]
  · simp only [reduceCtorEq,false_iff]
    rintro ⟨yes,key⟩
    exact h ⟨yes,key ▸ j.isLt⟩

/-- Destination site of every real history piece; the spare slot carries padding. -/
def siteOf (x : Pins R B d → Bool) (y : Pins U V t → Bool) : Slot a R U → Option (Fin a)
  | .inl i => some i
  | .inr none => none
  | .inr (some (.inl r)) => name a x r
  | .inr (some (.inr u)) => name a y u

/-- Actual final site anchor of a complete public source piece. -/
def anchor (S : Schema R B) (L : Schema U V) (x : Pins R B d → Bool) (y : Pins U V t → Bool)
    (i : Fin (roster a S L).length) : Fin (roster a S L).length :=
  (siteOf x y ((roster a S L).get i)).elim (holeSlot a S L) (anchorSlot S L)

/-- Final cell of a public piece, with the one extra skipped cell for holes. -/
def cellOf (S : Schema R B) (L : Schema U V) (x : Pins R B d → Bool) (y : Pins U V t → Bool)
    (cells : Fin a → Fin C) (i : Fin (roster a S L).length) : Fin (C+1) :=
  (siteOf x y ((roster a S L).get i)).elim (Fin.last C) (fun j => (cells j).castSucc)

/-- The actual global cell key agrees with that of its regrouping anchor for
both live and inactive rows. -/
theorem anchored (S : Schema R B) (L : Schema U V) (x : Pins R B d → Bool) (y : Pins U V t → Bool)
    (cells : Fin a → Fin C) (i : Fin (roster a S L).length) :
    cellOf S L x y cells (anchor S L x y i) = cellOf S L x y cells i := by
  unfold anchor cellOf
  cases h : siteOf x y ((roster a S L).get i) with
  | none => simp only [Option.elim_none,holeSlot_get,siteOf]
  | some j => simp only [Option.elim_some,anchorSlot_get,siteOf]

/-- Positional scalar operands of an immutable physical row, inside the
fixed common scalar alphabet of the private initializer. -/
def pin (ts : List Kind) (room : ts.length≤cap) (i : Fin ts.length) : Field cap := .inr (i.castLE room)

/-- Frozen historical records receive both final prefixes. Absolute final wire
bindings read the same finite tagged ABI with their original absolute operands. -/
def format (S : Schema R B) (L : Schema U V) (sh : ∀ r, (S.tags r).length≤cap)
    (lh : ∀ r, (L.tags r).length≤cap) : Slot a R U → List (RecordCode (Field cap))
  | .inl _ | .inr none => []
  | .inr (some (.inl r)) => [(Stored.fromTags (S.tags r) (pin _ (sh r))).placed
      (.field (.inl false)) (.field (.inl true))]
  | .inr (some (.inr u)) => [Stored.fromTags (L.tags u) (pin _ (lh u))]

/-- Actual static template for the joined public geometry stage. Each original
opaque table is placed once, at its site anchor, independently of all row copies. -/
def template (S : Schema R B) (L : Schema U V) (boxes : Fin a → List (Source.Box Orig))
    (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, (L.tags r).length≤cap)
    (privateWires : Fin (C+1) → E) (reports : Fin (C+1) → List (List E)) :
    Template E (Field cap) Orig (roster a S L).length (C+1) where
  boxes i := ((roster a S L).get i).elim boxes (fun _ => [])
  format i := format S L sh lh ((roster a S L).get i)
  privateWires := privateWires
  reports := reports

end CellPacketGeometry.History

end BorderVNP
end Computability
end OAI
