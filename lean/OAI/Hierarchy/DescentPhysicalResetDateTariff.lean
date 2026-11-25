import OAI.Hierarchy.DescentPhysicalResetDate
import OAI.Hierarchy.DescentPhysicalTrunkCost
import OAI.Hierarchy.DescentContactOutputPrice
import OAI.Hierarchy.DescentPrivateMaskPeriodPrice
import OAI.Hierarchy.DescentResetReceivedTariff
import OAI.Hierarchy.DescentFundedCensusInvoice
import OAI.Hierarchy.DescentDatedNodeMetadataTariff

namespace OAI
/-! The word-width invoice of the dated processor, including each installed instruction. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentStaticWordColumn DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w) (z : u.FinalInputs)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "s" => (v).sheets
local notation "A" => (v).front
local notation "begin₀" => (v).actorEnd b
local notation "scene₀" => (v).issuedScene b u.earlier
local notation "rbase" => ((v).remap b).endAddress
local notation "prior" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "priorTicks" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation "actors" => (v).actor.actorBody u.actor ((v).middle.stop b) w
local notation "actorTicks" => (v).actor.actorTicks u.actor ((v).middle.stop b) w
local notation "loaded" => (A).trunkScene begin₀ scene₀ u.sceneFits
local notation "measured" => (v).contactShape.issuedProgram ((A).donorStart begin₀) ((v).trunkEnd b) (scene₀).donor w
local notation "mticks" => (v).contactShape.issuedTicks ((A).donorStart begin₀) ((v).trunkEnd b) (scene₀).donor
local notation "joint" => (v).jointPhase b u.earlier w
local notation "pr₀" => (v).privateShape
local notation "prgo" => (pr₀).code ((v).jointEnd b) ((A).contactLayout begin₀) u.earlier.pages w
local notation "prtime" => (pr₀).ticks ((v).jointEnd b) ((A).contactLayout begin₀) u.earlier.pages
local notation "exit" => (v).sheetsReturn u.sectors ((v).sheetsStart b) u.operand b u.degree u.bank u.laws w
local notation "exitTicks" => (v).sheetsTime u.sectors ((v).sheetsStart b) u.operand b u.degree u.bank u.laws w

def instructionWords (p : Procedure w) (ticks : ℕ) :=ticks+7*names p

/-- Equalities use the actual compiled code's label, register and slot counts. -/
theorem dated_words :
    (date z).tariff =
     (instructionWords prior priorTicks+instructionWords actors actorTicks+
      instructionWords (loaded).program (loaded).ticks+instructionWords measured mticks+
      instructionWords (joint).program (joint).ticks+instructionWords prgo prtime+instructionWords (u.masked.code w) u.masked.ticks+
      instructionWords (u.numbered.code rbase w) (u.numbered.time rbase)+instructionWords exit exitTicks+
      instructionWords z.tailCode z.tailTime)*w := by
  simp only [date,DateCode.tariff,DateCode.ticks,DateCode.names,DateInputs.throughOperands,
    DateInputs.throughOperandTicks,instructionWords,names_seq]
  ring

/-- The compact trunk, measured contact decks and joint host comparisons charge
their computed layouts. Earlier and later phases use their own separate invoices. -/
theorem measured_words (T : ℕ)
    (work : ∀q f,((v).contactShape.fieldsAt ((A).donorStart begin₀) ((v).trunkEnd b) (scene₀).donor q f).work≤T)
    (oldLanes : 0<(v).contactShape.donor.batch) (blocks : 0<(v).contactShape.blocks)
    (lanes : 0<(v).contactShape.batch) :
    let n:=(A).newHosts*chunks (A).peer.groups (A).peer.lanes
    let pages:=3*2^(DescentResetTrunkIssue.width (A).metaBits (A).peer.lanes)
    let early:=(A).received begin₀ scene₀ u.sceneFits
    instructionWords (loaded).program (loaded).ticks+instructionWords measured mticks≤
      instructionWords early.program early.ticks+
       ((46+108*(A).newHosts+124*n+10*pages)+7*(15*(2*(A).newHosts+4*n+4)+350+15*(pages+1)))+
       (v).contactShape.cost ((A).donorStart begin₀) ((v).trunkEnd b) T := by
  intro n pages early
  obtain ⟨time,rom,_⟩:=(A).trunkScene_price begin₀ scene₀ u.sceneFits
  have contact:=(v).contactShape.actual_cost (w:=w) ((A).donorStart begin₀) ((v).trunkEnd b) (scene₀).donor
    T work oldLanes blocks lanes
  unfold instructionWords
  dsimp only [n,pages,early] at *
  omega

/-- The compact peer table broadcasts once for all groups. The private charts use
only the local shape fields and the true packet width. -/
def peerPrice :=
  7*(18000*((s).hosts+1)*((A).peer.oldDegree+1)+150*((A).peer.hosts+1)+
    25*DescentResetPeerJointBroadcast.count (s).hosts (s).groups (s).lanes (s).metaBits+38)

theorem issued_mask_words (old : 0<(pr₀).oldBatch) (blocks : 0<(pr₀).blocks) (lanes : 0<(pr₀).batch) :
    instructionWords (joint).program (joint).ticks+instructionWords prgo prtime≤
      peerPrice (a:=a)+(pr₀).periodPrice := by
  have packets:=(v).peerJoint_price b u.earlier w
  have priv:=(pr₀).issued_price ((v).jointEnd b) ((A).contactLayout begin₀) u.earlier.pages w old blocks lanes
  change (joint).ticks+names (joint).program≤_ at packets
  unfold instructionWords peerPrice
  omega

/-- The bounded job index is the physical writer's own range, including blank jobs. -/
def peak (n : ℕ) (work : ℕ→ℕ) :=Finset.univ.sup (fun j : Fin n=>work j.val)
theorem peak_le (n : ℕ) (work : ℕ→ℕ) (i : ℕ) (hi:i<n) : work i≤peak n work :=
  Finset.le_sup (f:=fun j : Fin n=>work j.val) (Finset.mem_univ ⟨i,hi⟩)

def rankWork :=peak (3*u.masked.jobs) fun j=>(u.masked.mixed.ranks.op u.masked.mixed.rankOp u.masked.mixed.rankReads j).work
def maskWork :=peak u.masked.jobs fun j=>(u.masked.mixed.masks.op (DescentCandidateMaskRAM.render (field:=u.masked.field)) u.masked.mixed.fields j).work

theorem rank_mask_words :
    let m :=u.masked
    instructionWords (m.code w) m.ticks≤
     (4+10*m.relay.size)+(m.mixed.ranks.costBound 5 m.field (rankWork u)+m.mixed.masks.costBound 9 m.field (maskWork u))+
     7*(15*(m.relay.size+1)+(m.mixed.ranks.nameBound 5 m.field (rankWork u)+m.mixed.masks.nameBound 9 m.field (maskWork u))) :=by
  intro m
  have both:=m.priced (w:=w) (rankWork u) (maskWork u) (peak_le _ _) (peak_le _ _)
  unfold instructionWords
  omega

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
