import OAI.Hierarchy.DescentPhysicalVenuePredecessor
import OAI.Hierarchy.DescentRecordedOperandActors
import OAI.Hierarchy.DescentReachedSheetBounds

namespace OAI
/-! # Address ranges of the authentic reset census before funding begins -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentDenseHostOrder DescentSIMDLookup DescentColonies
open DescentSixParty.Chronology DescentPacking.PackedMatch.Local.Stage ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist:ℕ} {ctl:ResetRates G S k D n h C f g cut tail}
  {prev:Reached W G q ε S k i z D wire hist} (B:ClosedReset prev ctl)
  {H Ma w:ℕ} (oldRoom:Fintype.card prev.V≤H)
local notation "cc" => B.terminals.commonDepth
local notation "Q" => (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-cc) (GroupStage.depthBound D n f g)).card
local notation "R" => H*Q
local notation "N" => Fintype.card B.next.V
local notation "rank" => (B.frame.host.symm.toEmbedding.trans prev.vertex).trans (Fin.castLEEmb oldRoom)
local notation "raw" => B.reset.rawHostRank B.terminals rank
variable {a:PhysicalReset}{floor:ℕ}{u:a.DateInputs floor w}
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "src" => PhysicalReset.FinalInputs.predecessor u
local notation "jobs" => (v).venue.census
local notation "ac" => (v).actor
local notation "ds" => (ac).directory ((v).middle.stop b)
local notation "stop₀" => (v).finalEnd b
local notation "fund" => (v).fundedEnd b
local notation "wk" => (v).receiver

include oldRoom in
/-- A single layout of the actor, peer, funding and signed receiver programs gives
all the scalar and padded-array extents used by the recorded successor venue. -/
theorem operand_locations (ready:u.Ready) (jobsAt:(jobs).jobs=(ac).shapes)
    (sitesAt:(jobs).hosts=(ac).hosts) (groupsAt:(jobs).groups=(ac).groups)
    (hosts:(ac).hosts=H) (shapesAt:(ac).shapes=Q) (chunksAt:(ac).chunksPerHost=chunks (2^cc) Ma)
    (peerRaw:(v).front.peer.hosts=R) (blocks:(wk).blocks=2^k) (limit:(wk).capacity=B.next.placement.cap)
    (word:stop₀<2^w) :
    N≤(src).ranks.inverse.size ∧ N<2^w ∧
    (src).actor.base+Q*(H*chunks (2^cc) Ma)≤ stop₀ ∧ (src).ranks.count.base<stop₀ ∧
    (src).ranks.inverse.base+N≤ stop₀ ∧ (src).ranks.forward.base+R≤ stop₀ ∧
    (∀j,((src).ranks.neighbor j).base+R≤ stop₀) ∧
    R≤(src).ranks.forward.size ∧ (∀j,R≤((src).ranks.neighbor j).size) ∧
    ∀(x:Block k)(j:Fin (2*B.next.placement.cap)),((src).signed x.val j.val).base+
      ((src).signed x.val j.val).size≤ stop₀:=by
  obtain ⟨actorFits,_,ranks,rendered⟩:=u.prior_venue_pages_at stop₀ le_rfl ready jobsAt sitesAt groupsAt word
  have scene:Q*(H*chunks (2^cc) Ma)≤(src).actor.size:=by
    rw [←hosts,←shapesAt,←chunksAt]
    exact (ac).extent_scene ((v).middle.stop b)
  have sites:(ds).sites=R:=by change (ac).hosts*(ac).shapes=_;rw [hosts,shapesAt]
  have full:N≤R:=by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (fun node : B.next.V => raw node) (raw).injective
  have paid:R≤(ds).pitch:=sites.ge.trans (ds).ordered.1
  have inverse:N≤(src).ranks.inverse.size:=full.trans paid
  have peer(j:Fin 3):R≤((src).ranks.neighbor j).size:=by
    change R≤2^Nat.clog 2 (v).front.peer.hosts
    rw [peerRaw]
    exact Nat.le_pow_clog (by decide) _
  refine ⟨inverse,inverse.trans_lt ranks.inverse.2.1,(Nat.add_le_add_left scene _).trans actorFits.2.2,
    (Nat.lt_add_of_pos_right ranks.count.1).trans_le ranks.count.2.2,
    (Nat.add_le_add_left inverse _).trans ranks.inverse.2.2,
    (Nat.add_le_add_left paid _).trans ranks.forward.2.2,
    fun j=>(Nat.add_le_add_left (peer j) _).trans (ranks.neighbor j).2.2,paid,peer,?_⟩
  intro x j
  exact (u.receiver_page rendered word (x.cast blocks.symm) (j.cast (congrArg (2*·) limit.symm))).1.2.2

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
