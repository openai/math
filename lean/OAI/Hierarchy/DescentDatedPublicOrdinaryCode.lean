import OAI.Hierarchy.DescentDatedOrdinaryFinal
import OAI.Hierarchy.DescentOrdinaryDonorDateCode
import OAI.Hierarchy.DescentDatedOrdinaryProfileIssue

namespace OAI
/-! # An ordinary date in causal order on the physical stage address plan -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (root shelf header : ℕ)
  (input : Dated.Operands) (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources)
  {w : ℕ} (s : ResultSteps w) (ready : v.ResultRoom (v.stageStart root) B w)
local notation "floor" => v.stageStart root
local notation "load" => v.archivePhase root shelf w
local notation "tail" => v.finish floor input count wires B s ready
set_option quotPrecheck false in
local notation "measure" => (⟨v.prior.placement.wire,v.prior.placement.z,v.prior.placement.hist⟩:Dated.Measures)

/-- The matcher and donor take their positions from the public date, and the
pair count occupies the final word of the whole successor. -/
def date (d : DonorDate) (positive : 0< d.exponent) : DateCode w:=
  d.codeLoadedAfter v.gadget positive v.payload v.seats v.bitsPerField floor header w input measure
    (load).program (load).ticks (tail).program (tail).ticks

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
