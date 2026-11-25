import OAI.Hierarchy.DescentDatedStageObserved

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch
open DescentSixParty DescentSIMDLookup DescentColonies DescentPackedColony DescentKernelHistory.BitDescription
open DescentTerminalEpochDecoder DescentPackedProfileWindow DescentTerminalEpochChart DescentPackedProfileArchive
open DescentPackedProfileWide DescentGroupPeerOrder DescentStageEdgeReceipt
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentPacking.PackedMatch.Local
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (input : Dated.Operands) (floor : ℕ)
local notation "r" => v.prior
local notation "A" => v.prior.placement
local notation "a" => v.area
local notation "H" => 2^v.level
local notation "J" => v.schedule.groupCount v.age
local notation "c" => (a).chooser input.roster floor
local notation "rom" => (a).prepareAt input.roster floor
local notation "plan" => (a).matcher input.roster floor
local notation "M" => (a).lanesAt
local notation "e" => (Equiv.refl (Fin J))
local notation "sh" => (a).shapeAt
local notation "native" => (r).order.trans Fin.valEmbedding
local notation "measure" => (⟨(A).wire,(A).z,(A).hist⟩ : Dated.Measures)

variable (hv : Fintype.card v.prior.V ≤ 2^v.level)
local notation "names" => GroupStage.plane v.hostNumbers hv
local notation "rank" => groupRank ((e).toEmbedding.trans Fin.valEmbedding) ((names).trans Fin.valEmbedding)
local notation "rs" => (fun (h : Fin H) (j : Fin (A).degree)=>(r).venueRoster hv h (Fin.cast (r).branch j))
local notation "old" => input.ports (A).degree
local notation "top" => (plan).layout.topology
local notation "sel" => (a).selected v.gadget (A).fieldBits input measure
local notation "time_" => (a).selectedTicks v.gadget (A).fieldBits input measure
local notation "home" => scanHomeAt v.nonnegative (A).stage
local notation "color" => scanColorAt v.nonnegative (A).stage
variable {w : ℕ} {Pin : Type} (m : Memory w) (choice : (v.prior.placement.stage.result v.nonnegative).Choice)
    (entry : Source Pin) (z : Pin→Bool) (ext : DescentTerminalEpochBits.width entry.C ≤ v.area.shapeAt.digit)

/-- Once the original archived profile agrees, the selected matcher report
provides its genuine paid pair values and can advance the native history. -/
theorem reachedReport.accept (seen : v.reachedReport input floor hv m choice entry z ext)
    (hit : ∀i,(wideCell entry.pin z (sh).digit ext i).val=
      profileAt (inputNumber v.nonnegative A (e).toEmbedding names)
        ((scannedRows v.nonnegative (A).stage).profile choice) i) :
    OrdinaryReport A native v.schedule (r).valid v.nonnegative e v.hostNumbers hv c v.bitsPerField
      v.payload v.unit v.profile v.seats rom old choice rs m (sel w floor)
      (time_ w floor) (fun i=>i< floor ∨ (plan).endAddr≤ i) :=by
  obtain ⟨out,i,j,size,run,elected,paint,read₀,read₁,win,rails,donors,topology,profiles,frame⟩:=seen
  exact ⟨out,i,j,size,run,elected,paint,read₀,read₁,win,rails,donors,topology,profiles hit,frame⟩
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
