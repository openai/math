import OAI.Hierarchy.ProbeStripPrefixBatch
import OAI.Hierarchy.ProbeStripPortBoard

namespace OAI
/-! # Operand bounds after placement of a padded strip -/
noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe PurchaseStage ProbeStage Calendar
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical

variable {F E A D : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A] [Fintype D]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ} {N z d k q : ℕ}

def PlacedInputs {n : ℕ} (f : Format z d k q n) (cut : ℕ) : Prop :=
  (enabledBatch f.market.layout f.board).Before cut ∧
    (∀i j,(f.board.wire i j).inputEnd≤cut) ∧ f.stockSource.slot.inputEnd≤cut

theorem placed_inputs (c : Channels D E) (m : Probe.FixedMenu F edge req box ε tree N)
    (b : Boards z d k q (Fintype.card D) (Fintype.card E)) (market : Market z d k)
    (dim header cut : ℕ) (channels : c.Before cut) (report : b.report.inputEnd≤cut)
    (terms : b.terms.base+b.terms.size≤cut) (menu : b.menu.base+b.menu.size≤cut)
    (selectors : b.selectors.base+b.selectors.size≤cut) (stock : market.shelf.stockBase+b.old.size≤cut)
    (price : b.price.base+b.price.size≤cut)
    (offsets : (GlobalTests.offsets b.globalTests).base+(GlobalTests.offsets b.globalTests).size≤cut) :
    let B:=format c m market b.repair b.test b.globalTests b.baseline b.price b.terms b.menu
      b.enabled b.selectors b.old b.reserve b.half b.cash .row b.report b.priceOut b.copies
      b.maxWidth b.start b.indexBits b.limit
    let f:=PortPadding.format dim header c.slot B
    f.board.repairBits.base+f.board.repairBits.size≤cut →
    (f.occurrenceHeader header).stop≤cut → PlacedInputs f cut ∧ (∀j,(f.board.reportWidth j).inputEnd≤cut) := by
  intro B f mask headerRoom
  let bank : Bank := {b.old with base:=market.shelf.stockBase}
  let test:=tested {b.test with live:=c.live,rows:=market.rows,population:=2^z}
    b.price (GlobalTests.offsets b.globalTests) bank c.digit
  let ports:Fin (Fintype.card E)→E := (Fintype.equivFin E).symm
  let actual:=batch (q:=q) m test b.terms b.menu f.board.repairBits b.selectors bank
    .row b.copies b.maxWidth ports c.slot
  have small : actual.Before cut := batch_before m test b.terms b.menu f.board.repairBits
    b.selectors bank .row b.copies b.maxWidth ports c.slot terms menu mask selectors stock
    (Nat.zero_le _) (quoted_before _ _ _ _ price offsets stock channels.digit_before) channels.slot_before
  refine ⟨⟨PortPadding.before_batch dim small,?_,?_⟩,?_⟩
  · intro i j
    change ((PortPadding.extend (wires m actual ports) (fun _=>Expr.lit 0) i) j).inputEnd≤cut
    unfold PortPadding.extend
    split
    · exact wires_before m actual ports small _ j
    · exact Nat.zero_le _
  · let h:=f.occurrenceHeader header
    have bounds : h.ball.base+h.ball.size≤cut ∧ h.field.base+h.field.size≤cut := by
      change h.start+h.small≤cut ∧ h.start+h.small+h.small≤cut
      change h.start+2*h.small+h.large+h.large≤cut at headerRoom
      omega
    apply destination_before h _ (PortPadding.extend c.slot none) bounds.1 bounds.2
    intro i e eq
    unfold PortPadding.extend at eq
    split at eq
    · exact channels.slot_before _ _ eq
    · contradiction
  · intro j
    exact InputEnd.choose _ _ _ _ (fun i=>wires_before m actual ports small i j) report

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
