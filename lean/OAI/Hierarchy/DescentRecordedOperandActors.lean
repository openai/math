import OAI.Hierarchy.DescentPhysicalResetActorOutput
import OAI.Hierarchy.DescentRecordedActorDirectoryAfterRoots
import OAI.Hierarchy.DescentRecordedVenueComplete
import OAI.Hierarchy.DescentPhysicalFundedRoom

namespace OAI
/-! # The actor classifier's signed masks and dense directory at the operand snapshot -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentDenseHostOrder DescentSIMDLookup DescentActorRaster DescentPackedZip
open DescentPaidResidentCount DescentPacking.PackedMatch.Local.Stage DescentPackedColony DescentColonies
open DescentDatedAddressBook DescentStageEdgeReceipt DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist:ℕ} {ctl:ResetRates G S k D n h C f g cut tail}
  {prev:Reached W G q ε S k i z D wire hist} (B:ClosedReset prev ctl)
  {H Ma w:ℕ} (oldRoom:Fintype.card prev.V≤H)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "height" => GroupStage.depthBound D n f g
local notation "Q" => (DescentDenseHostOrder.roster (Z).graph ((Z).k-cc) height).card
local notation "R" => H*Q
local notation "N" => Fintype.card B.next.V
local notation "vertex" => B.frame.host.symm.toEmbedding.trans prev.vertex
local notation "rank" => (vertex).trans (Fin.castLEEmb oldRoom)
local notation "raw" => (Z).rawHostRank T rank
variable {a:PhysicalReset}{floor:ℕ}{u:a.DateInputs floor w}
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "inputs" => PhysicalReset.FinalInputs.predecessor u
local notation "atActor" => (v).middle.stop b
local notation "ds" => (v).actor.directory atActor
local notation "scene" => (v).actor.scene atActor
local notation "stencil" => a.throughStencil u.shape floor u.count u.hub u.g u.Y u.src u.sourceRows u.oldDegree w
local notation "scanTime" => a.throughStencilTicks u.shape floor u.count u.hub u.g u.Y u.sourceRows u.oldDegree w
local notation "rt" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "pub_" => (((rt).preparedRoots u.book u.bookFits).seq ((v).actor.classifier u.actor atActor w)).seq ((ds).program w scene)
local notation "ticks_" => ((rt).preparedTicks u.book u.bookFits+(v).actor.classifierTime u.actor atActor w)+(ds).ticks scene
local notation "rows" => H*chunks (2^cc) Ma

/-- The inputs after the classifier come from the same execution of
`Recorded.directory_after_roots`. Its intermediate scene lies below the native
directory and therefore survives the latter's rank, inverse and flags writes. -/
theorem recorded_operand_actors (ready:u.Ready)
    (hosts:(v).actor.hosts=H) (shapesAt:(v).actor.shapes=Q)
    (parts:(v).actor.chunksPerHost=chunks (2^cc) Ma)
    {initial measured posted classified m:Memory w}
    (pre:u.throughOperandDate.Runs initial m) (scan:(stencil).Exec initial measured scanTime)
    (ran:(pub_).Exec measured posted ticks_)
    (count:posted (ds).count.base=(N:Word w))
    (inv:∀t:B.next.V,posted ((ds).inverse.base+((Z).denseHostRank T rank t).val)=((raw t).val:Word w))
    (fwd:∀t:B.next.V,posted ((ds).ranks.base+(raw t).val)=(((Z).denseHostRank T rank t).val:Word w))
    (image:posted=(ds).result scene classified)
    (planes:∀j (p:Row H (2^cc) Ma),classified ((scene).base+j.val*rows+(row H (2^cc) Ma p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j) p).val:Word w)) :
    (∀j (p:Row H (2^cc) Ma),m ((inputs).actor.base+j.val*rows+(row H (2^cc) Ma p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j) p).val:Word w)) ∧
      m (inputs).ranks.count.base=(N:Word w) ∧
      (∀t:B.next.V,m ((inputs).ranks.inverse.base+(B.next.vertex t).val)=((raw t).val:Word w)) ∧
      (∀t:B.next.V,m ((inputs).ranks.forward.base+(raw t).val)=((B.next.vertex t).val:Word w)):=by
  have stay:=PhysicalReset.DateInputs.operand_actor_below (u:=u) ready pre scan ran
  have bank:=PhysicalReset.DateInputs.prior_actor_bank (u:=u) ready
  have exactEnd:(scene).base+(scene).size=(ds).first:=rfl
  have now:(scene).Fits w (ds).first:=⟨bank.1,bank.2.1,exactEnd.le⟩
  have keep:=((ds).evaluate scene classified now ready.actor.parts ready.actor.room).2.2
  have dim:Q*rows≤(scene).size:=by
    rw [←hosts,←shapesAt,←parts]
    exact (v).actor.extent_scene atActor
  have published:= (ds).fits ready.actor.room
  have countLow: (ds).count.base<(v).actorEnd b :=
    (Nat.lt_add_of_pos_right published.2.2.2.1.1).trans_le published.2.2.2.1.2.2
  have site:(ds).sites=R:=by change (v).actor.hosts*(v).actor.shapes=_;rw [hosts,shapesAt]
  have dense: N≤R := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (fun node : B.next.V => raw node) (raw).injective
  have rankLow:=PhysicalReset.DateInputs.actor_rank_space u ready
  refine ⟨?_,(stay _ countLow).trans count,?_,?_⟩
  · intro j p
    have cell:j.val*rows+(row H (2^cc) Ma p).val<Q*rows:=calc
      _ < j.val*rows+rows:=Nat.add_lt_add_left (row H (2^cc) Ma p).isLt _
      _ = (j.val+1)*rows:=(Nat.succ_mul ..).symm
      _ ≤ Q*rows:=Nat.mul_le_mul_right rows j.isLt
    have low:(scene).base+j.val*rows+(row H (2^cc) Ma p).val<(ds).first:=by
      rw [←exactEnd,Nat.add_assoc];exact Nat.add_lt_add_left (cell.trans_le dim) _
    have before:(ds).first≤(v).actorEnd b:=Nat.le_add_right ..
    exact (stay _ (low.trans_le before)).trans ((congrFun image _).trans ((keep _ (Or.inl low)).trans (planes j p)))
  · intro t
    have live:(B.next.vertex t).val<(ds).inverse.size :=
      (B.next.vertex t).isLt.trans_le (dense.trans (site.ge.trans (ds).ordered.1))
    have stored:=inv t
    rw [dense_physical B oldRoom t] at stored
    exact (stay _ ((Nat.add_lt_add_left live _).trans_le published.2.2.2.2.2.2)).trans stored
  · intro t
    have live:(raw t).val<(ds).ranks.size := (raw t).isLt.trans_le (site.ge.trans (ds).ordered.1)
    have stored:=fwd t
    rw [dense_physical B oldRoom t] at stored
    exact (stay _ ((Nat.add_lt_add_left live _).trans_le rankLow.2.2)).trans stored

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
