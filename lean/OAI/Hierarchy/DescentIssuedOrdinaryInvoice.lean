import OAI.Hierarchy.DescentOrdinarySuccessorInvoice
import OAI.Hierarchy.DescentOrdinaryResultSteps
import OAI.Hierarchy.DescentOrdinaryArgumentBill

namespace OAI
/-! # The selected ordinary successor, including the twelve physical operand-entry stages -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentPackedColony DescentDatedAddressBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) {w : ℕ}
    (input : Dated.Operands) (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources)
    (A : ArgumentEntry v) (matched : A.Match v floor)
    (paths : A.clip.venue.paths=StageVenueTail.OrdinaryRaster.paths v.area)
    (src : OriginSources v) (producer : NativePhase w)
    (chipFit : (A.chipBank v floor).Fits w (v.refsStart floor))
    (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (packed : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (radix : v.vector.radix=2^v.reference.k)
    (funded : v.FundedRoom floor (v.fundedFromEntry floor A paths) input w)
    (room : v.ResultRoom floor B w)
local notation "old" => (⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "peers" => DescentOrdinaryVenueReturn.phase old (v.materialEnd floor) v.k v.area.H v.area.D v.venue.hosts v.venue.degree w
local notation "meta" => v.nodeChart
local notation "ps" => (fun x : Fin (meta).blocks=>v.venue.metadataPaid B (x).val)
local notation "bits" => v.metadata.paidBits
local notation "digit" => (v.resolver.size+2)
local notation "spans" => v.spanVectors floor
local notation "venue" => v.venue.phase B (v.rasterEnd floor) w

def entryFee : ℕ :=
  let c:=phaseCharge (w:=w) w (7*w)
  c (A.clip.phase A.venue (v.signedEnd floor) w)+
  c (DescentOrdinaryPriorPad.phase A.previous A.clip.venue.hosts A.clip.working (A.priorStart v floor) A.previousBase w)+
  c ((A.roleLayout v).phase (A.roleStart v floor) A.role w)+
  c ((A.chip v).phase (A.chipStart v floor) (A.chipSource v floor) w)+
  c ((A.population v floor).phase (A.ports v floor) (A.labels v floor) w)+
  codeCharge w (7*w) (v.refTime floor) ((v.refChart floor).program w)+
  codeCharge w (7*w) (v.bornBook.ticks (A.chipBank v floor) (v.birthStart floor))
    (v.bornBook.program (A.chipBank v floor) (v.birthStart floor) w)+
  c ((A.directory v floor matched).refs.phase w (v.vectorStart floor))+
  c producer+c (v.grainPhase floor w)+c (v.rasterPhase floor src w)+c (v.resolvePhase floor w shape fit packed)

theorem entry_word_fee :
    (v.argumentPhaseAfterSigned floor A matched src producer chipFit shape fit packed).wordInvoice =
      v.entryFee floor A matched src producer shape fit packed := by
  have native:=v.argumentAfterSigned_bill floor A matched src producer chipFit shape fit packed w (7*w)
  calc
    _ = phaseCharge w (7*w) (v.argumentPhaseAfterSigned floor A matched src producer chipFit shape fit packed) := by
      unfold NativePhase.wordInvoice DateBill.bitTariff phaseCharge codeCharge
      ring
    _ = _ := native

theorem issued_finish_invoice :
    (v.finish floor input count wires B
      (v.ordinaryResultSteps floor input A matched paths src producer chipFit shape fit packed radix funded)
      room).wordInvoice =
      (v.beforeSignedMaterial floor A.venue.panel A.venue.adjacency w).wordInvoice+(peers).wordInvoice+
      (v.mark floor input w).wordInvoice+(v.signed.phase wires (v.markEnd floor) w).wordInvoice+v.entryFee floor A matched src producer shape fit packed+
      (v.fundedRaster floor (v.fundedFromEntry floor A paths) input w funded).wordInvoice+(venue).wordInvoice+
      DateBill.bitTariff ((meta).ordinaryProgram (v.metaStart floor) bits digit w ps spans)
        ((meta).ordinaryTime (v.metaStart floor) bits digit ps spans)+
      DateBill.bitTariff (v.finalChart.program (v.finalSources floor) (v.metaEnd floor) w)
        (v.finalChart.ticks (v.finalSources floor) (v.metaEnd floor))+
      (v.primitiveUpdate floor A matched radix w).wordInvoice+(v.counter floor w).wordInvoice := by
  rw [v.finish_invoice]
  simp only [ordinaryResultSteps,v.entry_word_fee]


end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
