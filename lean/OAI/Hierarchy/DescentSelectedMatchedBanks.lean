import OAI.Hierarchy.DescentDatedDonorOutputs
import OAI.Hierarchy.DescentPrivateMatchedDate
import OAI.Hierarchy.DescentIssuedPublicDonor

namespace OAI
/-! # Genuine matcher output words for the selected physical donor procedure -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentHostDegree
open DescentPacking DescentPacking.PackedMatch DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage
open DescentPackedZip DescentPackedColony DescentTerminalEpochChart DescentPackedProfileWide
open DescentSixParty.StarKeys DescentKernelHistory
open DescentHostDirectory DescentTerminalEpochDecoder DescentPackedProfileArchive
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist w : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
local notation "A" => prior.placement
local notation "J" => S.groupCount i
local notation "H" => DescentCompiler.TerminalScale.hostRows (S.hostSize i)
local notation "pad" => prior.valid.host.trans (DescentCompiler.TerminalScale.hostPad _)
local notation "grp" => Equiv.refl (Fin J)
local notation "e" => dense prior.vertex
local notation "vid" => GroupStage.plane e pad
local notation "orig" => prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)
local notation "r" => 2^k
local notation "cm" => 2*(A).cap
local notation "K" => 2^(k+1)
local notation "dim" => (A).degree
local notation "short" => max (k+3) (Nat.clog 2 (dim+1))
local notation "prof" => DescentTerminalEpochBits.width G.C
local notation "s" => shape r dim cm prof
variable {he : 0≤ε} {c : (prior.placement.stage.result he).Choice} {n : Normalize ((prior.placement.stage.result he).state c)}
variable {z' D' : ℕ} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he prior.placement.stage c n target)

theorem matchedBanks_eq (payload seats romBase : ℕ) (input : Dated.Operands) :
    ticket.matchedBanks payload seats romBase (input.ports dim)
      (fun x j=>input.wire x.val j.val) input.hubs =
      ticket.donorDate.matcherOutput payload seats input romBase := by rfl

theorem matched_phase_eq (payload seats romBase base : ℕ) (input : Dated.Operands) {header w factor p : ℕ}
    (past : header≤base) (live : 0<ticket.installedDonorWidth short prof)
    (wide : 2*(ticket.installedDonorWidth short prof)≤payload) (size : payload≤w)
    (ratio : w≤factor*payload) (room : ticket.wholeDonorEnd short prof H payload base≤2^w)
    (grain : (A).stage.z=S.grainAt G.b p i) :
    let old:=ticket.matchedBanks payload seats romBase (input.ports dim) (fun x j=>input.wire x.val j.val) input.hubs
    let visit:=ticket.issuedVisit payload base old past live wide size ratio room grain
    (visit.install.seq visit.venue).seq visit.gather=ticket.donorDate.matchedPhase payload seats input romBase base w := by
  intro old visit
  exact (ticket.issued_public_phase payload base old past live wide size ratio room grain).trans
    (congrArg (ticket.donorDate.phase payload base w) (ticket.matchedBanks_eq payload seats romBase input))

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
