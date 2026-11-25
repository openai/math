import OAI.Hierarchy.DescentNativePhaseInvoice
import OAI.Hierarchy.DescentDatedOrdinaryFinal
import OAI.Hierarchy.DescentOrdinaryWordTariff

namespace OAI
/-! # Exact instruction and execution charge of the public ordinary successor -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentPacking.PackedMatch.Local.Stage
namespace PhysicalOrdinary
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) {w : ℕ}
  (input : Dated.Operands) (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources)
  (s : ResultSteps w) (room : v.ResultRoom floor B w)
local notation "old" => (⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "peers" => DescentOrdinaryVenueReturn.phase old (v.materialEnd floor) v.k v.area.H v.area.D v.venue.hosts v.venue.degree w
local notation "meta" => v.nodeChart
local notation "ps" => (fun x : Fin (meta).blocks=>v.venue.metadataPaid B (x).val)
local notation "bits" => v.metadata.paidBits
local notation "digit" => (v.resolver.size+2)
local notation "spans" => v.spanVectors floor
local notation "venue" => v.venue.phase B (v.rasterEnd floor) w

theorem return_invoice : (v.returnPhase floor B w room).wordInvoice=
    (venue).wordInvoice+
    DateBill.bitTariff ((meta).ordinaryProgram (v.metaStart floor) bits digit w ps spans)
      ((meta).ordinaryTime (v.metaStart floor) bits digit ps spans)+
    DateBill.bitTariff (v.finalChart.program (v.finalSources floor) (v.metaEnd floor) w)
      (v.finalChart.ticks (v.finalSources floor) (v.metaEnd floor)) := by
  change DateBill.bitTariff (((venue).program.seq _).seq _) (((venue).ticks+_)+_)=_
  rw [DateBill.bitTariff_seq,DateBill.bitTariff_seq]
  rfl

/-- The instruction counts correspond to the original addresses at each boundary. -/
theorem finish_invoice :
    (v.finish floor input count wires B s room).wordInvoice =
      (v.beforeSignedMaterial floor s.parts s.adjacency w).wordInvoice+(peers).wordInvoice+
      (v.mark floor input w).wordInvoice+(v.signed.phase wires (v.markEnd floor) w).wordInvoice+s.arguments.wordInvoice+
      s.paid.wordInvoice+(venue).wordInvoice+
      DateBill.bitTariff ((meta).ordinaryProgram (v.metaStart floor) bits digit w ps spans)
        ((meta).ordinaryTime (v.metaStart floor) bits digit ps spans)+
      DateBill.bitTariff (v.finalChart.program (v.finalSources floor) (v.metaEnd floor) w)
        (v.finalChart.ticks (v.finalSources floor) (v.metaEnd floor))+
      s.primitive.wordInvoice+(v.counter floor w).wordInvoice := by
  simp only [finish,beforeCount,NativePhase.wordInvoice_seq,v.return_invoice floor B room,Nat.add_assoc]

end
end PhysicalOrdinary
end Hierarchy.DescentSixParty.Chronology

end OAI
