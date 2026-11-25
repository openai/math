import OAI.Hierarchy.DescentResetChargeAmounts
import OAI.Hierarchy.DescentResetCompactTrunkPrice
import OAI.Hierarchy.DescentPhysicalResetDateTariff
import OAI.Hierarchy.DescentPhysicalResetTailTariff
import OAI.Hierarchy.DescentScheduledEnteredProgram
import OAI.Hierarchy.DescentContactOutputWork

namespace OAI
/-! Bit charges for the public reset instruction, in its executed chronological order.
The compact trunk bound starts after its original received directory. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentStaticWordColumn DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage DescentResetCanvasIngress ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false

variable {a : PhysicalReset} (L : DescentResetCanvasIngress.Layout) (base : ℕ) {w : ℕ}
    (u : a.DateInputs (L.endAddress base) w) (z : u.FinalInputs) (io : Dated.Operands)
local notation "v" => a.successor
local notation "b" => a.rebased (L.endAddress base)
local notation "F" => (v).front
local notation "early" => (v).actorEnd b
local notation "scene" => (v).issuedScene b u.earlier
local notation "p" => (v).privateShape
local notation "beginning" => L.phase base w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)
local notation "root" => a.throughPublishedRoots u.shape (L.endAddress base) u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "rootTicks" => a.throughPublishedTicks u.shape (L.endAddress base) u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits

def enteredCharges : EnteredCharges :=
  let actorAt:=(v).middle.stop b
  let receipt:=(F).received early scene u.sceneFits
  let joint:=(v).jointPhase b u.earlier w
  let privateAt:=(v).jointEnd b
  let contact:=(F).contactLayout early
  let remap:=((v).remap b).endAddress
  let start:=(v).sheetsStart b
  let original:=(v).finalEnd b
  let rolesAt:=(v).fullEnd b
  let md:=(v).metadata
  let work:=FinalInputs.originBudget a
  { roots:=((beginning).ticks+rootTicks+7*names ((beginning).program.seq root))*w
    actor:=instructionWords ((v).actor.actorBody u.actor actorAt w) ((v).actor.actorTicks u.actor actorAt w)*w
    received:=instructionWords receipt.program receipt.ticks*w
    compact:=(F).compactTrunkWords*w
    contact:=(v).contactShape.cost ((F).donorStart early) ((v).trunkEnd b) (v).contactShape.operandWork*w
    masks:=(instructionWords joint.program joint.ticks+
      instructionWords ((p).code privateAt contact u.earlier.pages w) ((p).ticks privateAt contact u.earlier.pages)+
      instructionWords (u.masked.code w) u.masked.ticks)*w
    numbered:=instructionWords (u.numbered.code remap w) (u.numbered.time remap)*w
    sheets:=instructionWords ((v).sheetsReturn u.sectors start u.operand b u.degree u.bank u.laws w)
      ((v).sheetsTime u.sectors start u.operand b u.degree u.bank u.laws w)*w
    funding:=(FinalInputs.setupCharge (v).funded original w+
      FinalInputs.fundedCharge (v).venue.census (v).funded.capacity)*w
    venue:=(v).venue.fee*w
    mover:=(v).roleTransfer.invoice rolesAt w*w
    classes:=FinalInputs.classCharge (v).actorClass ((v).roleEnd b)*w
    birth:=((v).birth.invoice+((v).primitive.clockBound work+7*(v).primitive.nameBound work))*w
    metadata:=FinalInputs.metadataCharge md.chart md.paidBits md.spanBits u.operand.slots*w }

theorem entered_charge_bound
    (old : 0 < (v).contactShape.donor.batch) (blocks : 0 < (v).contactShape.blocks)
    (lanes : 0 < (v).contactShape.batch) (sizes : FinalInputs.TailSizes v)
    (space : (v).primitive.endAddress ((v).birthEnd b) < 2^w) :
    (enterCode L base u z io).tariff ≤ (enteredCharges L base u io).total := by
  have whole:=enterCode_price L base u z io
  have dateWords:=dated_words u z
  have decks:=Nat.mul_le_mul_right w (measured_words u (v).contactShape.operandWork
    ((v).contactShape.work_bound _ _ _) old blocks lanes)
  have last:=Nat.mul_le_mul_right w (z.tail_words sizes space)
  rw [whole,dateWords]
  simp only [EnteredCharges.total,enteredCharges,FinalInputs.tailCharge,CandidateFront.compactTrunkWords,
    instructionWords,names_seq,Nat.mul_add,Nat.add_mul] at decks last ⊢
  omega

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
