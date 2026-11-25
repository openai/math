import OAI.ThreeFlat.BitNetwork
import OAI.ThreeFlat.Diagonal.LaneCursorRows

namespace OAI
/-! # Addressing the occurrences of a sparse row trace

Cells may share hidden variables and input pins. A message is identified by
the source row, its public offset, the receiving cell's ordinal in its row,
and the argument number within the receiving cell.
-/

namespace ThreeFlat.Diagonal.LaneCursor

open scoped BigOperators Classical

variable {F : Type*} {p k low offsets slots : ℕ}

/-- Constant cell arguments have no incident wire. -/
def wired {n p : ℕ} : BitSource n p → Prop
  | .constant _ => False
  | _ => True

abbrev Occurrence (N : BitNetwork F p) :=
  {u : Fin N.cells × Fin 3 // wired (N.source u.1 u.2)}

/-- Row of the variable at the source end of an occurrence. The final case
is never used for a member of `Occurrence`. -/
def sourceRow {n : ℕ} (hidden : Fin n → Row k low) (pins : Fin p → Row k low)
    (fallback : Row k low) : BitSource n p → Row k low
  | .hidden h => hidden h
  | .pin j => pins j
  | .constant _ => fallback

/-- A row-addressed trace circuit with a common list of XOR offsets. -/
structure RowLayout (N : BitNetwork F p) (k low offsets slots : ℕ) where
  cellAddress : Fin N.cells ↪ Row k low × Fin slots
  hiddenRow : Fin N.internal → Row k low
  pinRow : Fin p → Row k low
  offset : Fin offsets → Row k low
  code : Occurrence N → Fin offsets
  reaches : ∀ e : Occurrence N,
    (cellAddress e.val.1).1 = partner
      (sourceRow hiddenRow pinRow (cellAddress e.val.1).1 (N.source e.val.1 e.val.2))
      (offset (code e))

namespace RowLayout

variable {N : BitNetwork F p} (P : RowLayout N k low offsets slots)

abbrev PayloadAddress (low slots : ℕ) := Fin (2 ^ low) × Fin slots × Fin 3

def mask (o : Fin offsets) : Lane k := (splitRow k low (P.offset o)).1

def owner (e : Occurrence N) : Row k low :=
  sourceRow P.hiddenRow P.pinRow (P.cellAddress e.val.1).1 (N.source e.val.1 e.val.2)

def ownerLane (e : Occurrence N) : Lane k := (splitRow k low (P.owner e)).1
def cellLane (c : Fin N.cells) : Lane k := (splitRow k low (P.cellAddress c).1).1

def tag (e : Occurrence N) : Fin offsets × PayloadAddress low slots :=
  (P.code e, (splitRow k low (P.owner e)).2, (P.cellAddress e.val.1).2, e.val.2)

def key (e : Occurrence N) : Lane k × (Fin offsets × PayloadAddress low slots) :=
  (P.ownerLane e, P.tag e)

/-- At any lane each reserved address identifies at most one occurrence. -/
theorem key_injective : Function.Injective P.key := by
  intro a b h
  have offset_eq : P.code a = P.code b := congrArg (fun z => z.2.1) h
  have owner_eq : P.owner a = P.owner b := (splitRow k low).injective
    (Prod.ext (congrArg (fun z : Lane k × (Fin offsets × PayloadAddress low slots) => z.1) h)
      (congrArg (fun z => z.2.2.1) h))
  have rows_eq : (P.cellAddress a.val.1).1 = (P.cellAddress b.val.1).1 := by
    have ra : (P.cellAddress a.val.1).1 = partner (P.owner a) (P.offset (P.code a)) := P.reaches a
    have rb : (P.cellAddress b.val.1).1 = partner (P.owner b) (P.offset (P.code b)) := P.reaches b
    rw [ra, rb, owner_eq, offset_eq]
  apply Subtype.ext
  apply Prod.ext
  · exact P.cellAddress.injective (Prod.ext rows_eq (congrArg (fun z => z.2.2.2.1) h))
  · exact congrArg (fun z => z.2.2.2.2) h

theorem from_receiver (e : Occurrence N) :
    P.cellLane e.val.1 - P.mask (P.tag e).1 = P.ownerLane e := by
  have reach : (P.cellAddress e.val.1).1 = partner (P.owner e) (P.offset (P.code e)) := P.reaches e
  dsimp only [cellLane, mask, tag]
  rw [reach, (partner_coordinates _ _).1, add_sub_cancel_right]
  rfl

/-- Fill each real outgoing message from its owner. Every unoccupied
address is fixed to zero, including gaps in the public offset table. -/
noncomputable def emitted (pin : Fin p → Bool) (hidden : Fin N.internal → Bool)
    (lane : Lane k) (address : Fin offsets × PayloadAddress low slots) : Bool :=
  Function.extend P.key (fun e => (N.source e.val.1 e.val.2).read hidden pin)
    (fun _ => false) (lane, address)

theorem emitted_wire (pin : Fin p → Bool) (hidden : Fin N.internal → Bool) (e : Occurrence N) :
    P.emitted pin hidden (P.ownerLane e) (P.tag e) = (N.source e.val.1 e.val.2).read hidden pin :=
  P.key_injective.extend_apply _ _ e

theorem emitted_unused (pin : Fin p → Bool) (hidden : Fin N.internal → Bool)
    (lane : Lane k) (address : Fin offsets × PayloadAddress low slots)
    (unused : ¬ ∃ e : Occurrence N, P.key e = (lane, address)) :
    P.emitted pin hidden lane address = false := Function.extend_apply' _ _ _ unused

/-- Decode a receiving cell argument either from its reservation or from its
local literal. -/
noncomputable def argument (receive : Fin offsets × PayloadAddress low slots → Bool)
    (cell : Fin N.cells) (j : Fin 3) : Bool :=
  if hw : wired (N.source cell j) then receive (P.tag ⟨(cell,j), hw⟩)
  else (N.source cell j).read (fun _ => false) (fun _ => false)

theorem argument_delivered (pin : Fin p → Bool) (hidden : Fin N.internal → Bool)
    (cell : Fin N.cells) (j : Fin 3) :
    P.argument (fun tag => P.emitted pin hidden (P.cellLane cell - P.mask tag.1) tag) cell j =
      (N.source cell j).read hidden pin := by
  by_cases hw : wired (N.source cell j)
  · let e : Occurrence N := ⟨(cell,j), hw⟩
    rw [argument, dite_eq_left hw]
    change P.emitted pin hidden (P.cellLane e.val.1 - P.mask (P.tag e).1) (P.tag e) = _
    rw [P.from_receiver e, P.emitted_wire]
  · rw [argument, dite_eq_right hw]
    cases eq : N.source cell j <;> simp_all [wired, BitSource.read]

end RowLayout
end ThreeFlat.Diagonal.LaneCursor

end OAI
