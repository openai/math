import OAI.Hierarchy.DescentNamedFixedBook
import OAI.Hierarchy.DescentTerminalPreflightRun
import OAI.Hierarchy.DescentTerminalWingPitch

namespace OAI
/-! Original neighbor, wing and header-table words survive the weights, six-field book and controls. -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open DescentTerminalLocalPortBook ProtocolRAM DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (x:Spec) (base:ℕ) (peer:Bank) (old:Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (decode:(Fin x.strips→Cell x.printBits)→Directory 4 x.vertices x.arguments) (control:ℕ→ℕ)
    {w:ℕ} (primitive:Memory w)
local notation "books" => x.issuedBook base peer old
def bookAtPrimitive := (books).memory decode (x.vertices*x.arguments)
  (Book.WeightShelf.memory x.vertices x.arguments (x.weights base) primitive) 6 le_rfl
def cableInput := (x.controls base).after control (Book.expression (x.parts base))
  (x.bookAtPrimitive base peer old decode primitive)

theorem book_at_primitive_low (space:x.maskBase base<2^w) (nonempty:0<x.strips)
    (peerLow:peer.base+peer.size≤x.cohortEnd base)
    (oldLow:∀u j,(old u j).base+(old u j).size≤x.cohortEnd base)
    (i:ℕ) (early:i<x.weights base) :
    x.bookAtPrimitive base peer old decode primitive i=primitive i := by
  obtain ⟨_,_,wb,bf,fc,_,_,_,_⟩:=x.layers base
  have heights:=x.all_lower base space
  have stop_ : (books).stop<2^w := by rw [x.print_stop base peer old];exact heights.2.2.2.2.1
  have fit:=x.book_fits base space nonempty
  have book:=(books).native decode (x.vertices*x.arguments)
    (Book.WeightShelf.memory x.vertices x.arguments (x.weights base) primitive)
    (x.source_fit base peer old space peerLow oldLow) fit.2.1 stop_ 6 le_rfl
  exact (book.2.2.1 i (early.trans_le wb)).trans
    (DescentStaticWordColumn.frame (x.weights base) _ _ primitive i (.inl early))

theorem cable_input_low (space:x.maskBase base<2^w) (nonempty:0<x.strips)
    (peerLow:peer.base+peer.size≤x.cohortEnd base)
    (oldLow:∀u j,(old u j).base+(old u j).size≤x.cohortEnd base)
    (i:ℕ) (early:i<x.weights base) :
    x.cableInput base peer old decode control primitive i=primitive i := by
  obtain ⟨_,_,wb,bf,fc,_,_,_,_⟩:=x.layers base
  have heights:=x.all_lower base space
  have controls:=(x.controls base).any (x.bookAtPrimitive base peer old decode primitive) control
    (Book.expression (x.parts base)) (x.control_fits base space nonempty) heights.2.2.2.2.2.1
  exact (controls.2.2 i (.inl ((early.trans_le wb).trans_le bf))).trans
    (x.book_at_primitive_low base peer old decode primitive space nonempty peerLow oldLow i early)

open DescentTerminalCombinedRole DescentTerminalPointerDigits

/-- The intermediate date used by the endpoint receipts is the named snapshot
of the complete real primitive purchase, including its prior population/actor run. -/
theorem book_snapshot_eq (q p nd nodes hidden args:ℕ) (oldPaid actor:Fin x.scalar.blocks→Bank)
    (first second:Shelf) (chart:Fin x.scalar.columns→Fin x.scalar.blocks→Gather.Address)
    {out0 out7:ℕ} (f0:(Fin x.scalar.columns→Cell x.scalar.pointerBits)→Cell out0)
    (f7:(Fin x.scalar.columns→Cell x.scalar.pointerBits)→Cell out7) (m:Memory w) :
    x.bookAtPrimitive base peer old decode
      (x.primitiveSnapshot (base:=base) (w:=w) (q:=q) (p:=p) (nd:=nd) (nodes:=nodes)
        (hidden:=hidden) (args:=args) (oldPaid:=oldPaid) (actor:=actor) (first:=first) (second:=second)
        (chart:=chart) (f0:=f0) (f7:=f7) m) =
    x.bookSnapshot (base:=base) (peer:=peer) (wing:=old) (w:=w) (q:=q) (p:=p) (nd:=nd)
      (nodes:=nodes) (hidden:=hidden) (args:=args) (oldPaid:=oldPaid) (actor:=actor) (first:=first)
      (second:=second) (chart:=chart) (f0:=f0) (f7:=f7) (decode:=decode) m := rfl

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
