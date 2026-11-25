import OAI.Hierarchy.DescentResetRetainedCableLaw
import OAI.Hierarchy.DescentResetOperandComponents

namespace OAI
/-! The actual retained-operand lookup laws evaluated on a signed slot of the original donor. -/
namespace Hierarchy.DescentResetRetainedCableLaw.Shape
open DescentSIMDLookup DescentPackedZip DescentOperandStateBanks DescentOperandSignedSearch
open DescentNextSignedWindow DescentResetOperandComponents DescentResetOperandSlices
open scoped Classical Fin.CommRing
noncomputable section
variable (C : DescentResetRetainedCableLaw.Shape) {b : ℕ}

def oldIndex (x : C.Input) (z : C.Donor) (s : Bool) (j : C.Slot) : ℕ :=
  (if s then C.ticket x z j*C.units else 0)+(C.header x 3).val%C.units

def priceField (f : Field) (x : C.Input) : Cell C.fieldBits:=
  if f=2 then C.correction 0 x else if f=3 then C.correction 1 x else 0

theorem found_from_slots (x : C.Input) (z : C.Donor) (s : Bool) (j : C.Slot)
    (tag : (C.header x 0).val=1) (donor : (C.donorCell x).val=z.val+1)
    (face : ∀i,hit C.degree C.cap (if s then 1 else 0) i
      (DescentOperandPriorTicket.key C.degree C.cap C.units (C.header x)) (C.row x z i) ↔ i=j)
    (first : s=true→∀i,¬hit C.degree C.cap 0 i (DescentOperandPriorTicket.key C.degree C.cap C.units
      (C.header x)) (C.row x z i)) : C.found x=some (z,s,j):=by
  cases s with
  | false=>exact C.outgoing x z j tag donor (result_one _ _ 0 _ _ j face)
  | true=>exact C.incoming x z j tag donor (result_empty _ _ 0 _ _ (first rfl)) (result_one _ _ 1 _ _ j face)

theorem original_query (x : C.Input) (z : C.Donor) (s : Bool) (j : C.Slot)
    (foundAt : C.found x=some (z,s,j)) :
    C.query x=((if s then 1+2*C.strip else 1+(finProdFinEquiv (z,j)).val : ℕ):Cell C.queryBits) :=by
  cases s <;> simp [query,foundAt]

/-- The serial/word correction uses the prefix counted at the opposite compact relay
of an incoming cable. Its outgoing counterpart uses the old within-grain position. -/
theorem recorded_correction (x : C.Input) (z : C.Donor) (s : Bool) (j : C.Slot)
    (foundAt : C.found x=some (z,s,j)) (tag : (C.header x 0).val=1)
    (small : C.oldIndex x z s j<2^C.fieldBits) (f : Field) :
    C.priceField f x=DescentResetOperandComponents.correction C.units (if s then .trunk else .stem) f
      (C.header x 0) (if (C.hubCell x).val=1 then 1 else 0) ⟨C.oldIndex x z s j,small⟩:=by
  cases s <;> fin_cases f <;> by_cases h:(C.hubCell x).val=1 <;>
    simp [priceField,correction,foundAt,DescentResetOperandComponents.correction,oldIndex,
      DescentResetOperandSlices.part,DescentResetOperandSlices.mode,DescentResetOperandSlices.marked,h,tag]
  all_goals
    apply Fin.ext
    simp only [← Nat.cast_mul, ← Nat.cast_add, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    simpa [oldIndex] using small

theorem recorded_fields {degree cap : ℕ} (x : C.Input) (z : C.Donor) (s : Bool) (j : C.Slot)
    (foundAt : C.found x=some (z,s,j)) (tag : (C.header x 0).val=1) (positive : 0<C.units)
    (small : C.oldIndex x z s j<2^C.fieldBits) (earlier : Field→Cell C.fieldBits) (label : Cell b)
    (span : Span) (prevPeer prevSerial prevChunk : ℕ)
    (archive : ∀f,(earlier f).val=(Pointer.cable prevPeer prevSerial prevChunk).fields span f)
    (r : Record degree cap) (child : DescentSharedCableNames.Stage.Live degree cap)
    (markedAt : DescentResetOperandSlices.marked (if s then .trunk else .stem)
      (decide ((C.hubCell x).val=1))=r.marked ∨ C.oldIndex x z s j<C.units)
    (rendered : render r (C.oldIndex x z s j/C.units)=some child) (f : Field) :
    (DescentResetRetainedPages.kept f (earlier 0) (earlier f) label).val+(C.priceField f x).val+
      fresh r.neighbor.val r.shared f=(Pointer.cable child.neighbor.val (child.wire.val-child.within.val)
        (if r.marked then C.oldIndex x z s j%C.units else C.oldIndex x z s j)).fields span f :=by
  let hub : Cell 1:=if (C.hubCell x).val=1 then 1 else 0
  have same : earlier 0=C.header x 0:=Fin.ext ((archive 0).trans tag.symm)
  rw [C.recorded_correction x z s j foundAt tag small f,←same]
  apply from_cable C.units positive (if s then .trunk else .stem) earlier hub label span
    prevPeer prevSerial prevChunk archive ⟨C.oldIndex x z s j,small⟩ r child _ rendered f
  by_cases present:(C.hubCell x).val=1 <;> simpa [hub,present] using markedAt

end
end Hierarchy.DescentResetRetainedCableLaw.Shape

end OAI
