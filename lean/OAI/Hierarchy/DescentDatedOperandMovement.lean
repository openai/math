import OAI.Hierarchy.DescentPhysicalIssuedOperandColumns
import OAI.Hierarchy.DescentDatedPacketSnapshot
import OAI.Hierarchy.DescentDatedControlFrame
import OAI.Hierarchy.DescentPhysicalOperandCuts
import OAI.Hierarchy.DescentNamedResetOutput

namespace OAI
/-! The earlier actor, allocated old archive and guarded root rows stay available to both native operand moves. -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentPackedZip DescentSIMDLookup
structure MovementShape (C : DescentResetOperandSetup.Chart) : Prop where
  host : C.placement.oldHosts=C.retained.hosts
  groups : C.placement.groups*C.placement.blocks=C.retained.grouped
  size : 2^(C.retained.high+C.retained.low)=C.retained.groups*C.retained.blocks
  batch : 2^C.retained.low=C.retained.gatherLanes*C.retained.blocks
  gathered : 0<C.retained.gatherLanes
  blocks : 0<C.retained.blocks
  previous : 0<C.retained.previousLanes
  cut : C.retained.cut≤C.retained.high+C.retained.low
  pitch : C.retained.matrixLanes*C.retained.donors=2^C.retained.low
  matrix : 0<C.retained.matrixLanes
  decoded : 0<C.retained.decodedLanes
  packet : 0<C.seven.packetLanes
  signed : 0<C.signedLanes
end Hierarchy.DescentResetOperandSetup.Chart

namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentResetOperandSetup
noncomputable section
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h e prev M nextM cycles packet : ℕ)
    (prior : Prior) (base : ℕ)
local notation "V" => fromBoard G S board k tail age p f g drift degree h e prev M nextM cycles packet prior base
theorem movement_shape (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (live : age<S.length) (previous : 0<prior.operandLanes) : (V).setup.MovementShape:=by
  obtain ⟨dim,_,size,batch,cut,_,matrix,pitch,groups⟩:=
    S.previousGeometry G k tail drift degree p age h prior.nodes prior.arguments prior.operandLanes baseGroups radix live
  have gather : 0<(V).setup.retained.gatherLanes:=Nat.two_pow_pos _
  exact ⟨rfl,groups.symm,size,batch,gather,Nat.two_pow_pos _,previous,cut,pitch,
    (show 0<(V).setup.retained.matrixLanes from matrix.symm ▸ gather),
    Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _⟩
end
end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty DescentSixParty.Chronology DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentGL DescentColonies DescentOrdinaryAtomFieldRAM DescentSixParty.PackedFlow.Channels ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w U : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "C" => (v).setup
local notation "r" => (C).retained
local notation "s" => u.bank
local notation "start" => (v).operandFloor b
local notation "earlier" => (v).actorEnd b
local notation "head_" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "time_" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation "op" => (v).actor.actorBody u.actor ((v).middle.stop b) w
local notation "clock_" => (v).actor.actorTicks u.actor ((v).middle.stop b) w
variable (ok : u.Ready) (initial atActors : Memory w)
    (ran : ((a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits).seq
      (a.successor.actor.actorBody u.actor (a.successor.middle.stop (a.rebased floor)) w)).Exec initial atActors
      ((a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits) +
       (a.successor.actor.actorTicks u.actor (a.successor.middle.stop (a.rebased floor)) w)))
    (cheap : CheapCode ((a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits).seq
      (a.successor.actor.actorBody u.actor (a.successor.middle.stop (a.rebased floor)) w)))
local notation "mem" => u.beforeSetupImage ok atActors

include ran cheap in
theorem before_setup_actor : ∀j,j<earlier→mem j=atActors j:=by
  have turns:=u.control_frames ok initial atActors ran cheap
  have runResult :=u.run_to_sheets_from_actors ok initial atActors ran cheap
  obtain ⟨_,joint,_,_,_⟩:=(v).operands_after_front b
  have cut:=(v).cuts b
  have room:=cut.trunk.trans (cut.mass.trans (cut.joint.trans joint))
  exact fun j hj=>(turns.1 j (hj.trans_le room)).symm.trans (runResult.2.2 j (.inl hj))

include ran cheap in
theorem before_setup_moved (geo : (C).MovementShape) (L : DescentGL.Layout ((r).high+(r).low))
    (source : (r).Values) (X : (C).seven.Packets) (name : Fin U→Fin (C).placement.sparse)
    (signed : Fin (C).strip→Fin (C).placement.oldHosts→Fin ((C).placement.groups*(C).placement.blocks)→Cell (C).signedBits)
    (old : ∀i,((s).old i).Fits w earlier ∧ (r).hosts*chunks (r).groups (r).previousLanes≤((s).old i).size ∧
      Reads ((s).old i) (source i) (r).previousLanes atActors)
    (key : (s).matrix.base<earlier ∧ atActors (s).matrix.base=((DescentExterior.matrixCode L).val:Word w))
    (window : (s).window.Fits w earlier ∧ Source (s).window X (C).seven.packetLanes atActors)
    (signals : ∀j,((s).signed j).Fits w earlier ∧ Source ((s).signed j) (signed j) (C).signedLanes atActors)
    (count : (s).count.base<earlier ∧ atActors (s).count.base=(U:Word w))
    (inverse : (s).inverse.Fits w earlier ∧ U≤(s).inverse.size ∧
      ∀i:Fin U,atActors ((s).inverse.base+i.val)=((name i).val:Word w))
    (cu : U<2^w) (hu : (C).placement.newHosts≤2^w) :
    let strips:=fun j=>blockValues geo.cut ((r).before geo.size source j) L
    (C).Moved start (s) name (((C).sources start w (s)).image mem) ((C).assignedDigits geo.host geo.groups (s).which X strips) signed:=by
  have frame:=u.before_setup_actor ok initial atActors ran cheap
  have copy {H G d M₀ : ℕ} (e : Expr) (data : Fin H→Fin G→Cell d) (fit : e.Fits w earlier)
      (seen : Source e data M₀ atActors) : Source e data M₀ mem:=
    fun rowId=>(eval_below e _ _ _ fit frame).trans (seen rowId)
  have oldRead j : Reads ((s).old j) (source j) (r).previousLanes mem:=by
    intro rowId
    have bound:=(row _ _ _ rowId).isLt.trans_le (old j).2.1
    exact (frame _ ((Nat.add_lt_add_left bound _).trans_le (old j).1.2.2)).trans ((old j).2.2 rowId)
  have first : (C).placed start≤(C).packetEnd start:=((C).packets.join _).1.trans ((C).packets.join _).2
  have second : (C).packetEnd start≤(C).publicEnd start:=Nat.le_add_right ..
  obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈⟩:=(C).order start
  have third : (C).publicEnd start≤(C).endAddress start:=by omega
  have roof:=(first.trans (second.trans third)).trans_lt (((v).keep_before b).trans_lt
    (((v).operands_after_front b).2.2.2.2.trans_lt ok.full))
  exact (C).movedSources start mem (s) ok.placed roof geo.host geo.groups geo.size geo.batch
    geo.gathered geo.blocks geo.previous geo.cut geo.pitch geo.matrix geo.decoded geo.packet geo.signed
    L ((frame _ key.1).trans key.2) source (fun j=>(old j).2.1) oldRead X (copy _ _ window.1 window.2)
    name ((frame _ count.1).trans count.2) (fun i=>(frame _ ((Nat.add_lt_add_left
      (i.isLt.trans_le inverse.2.1) _).trans_le inverse.1.2.2)).trans (inverse.2.2 i)) cu hu inverse.2.1 signed
    (fun j=>copy _ _ (signals j).1 (signals j).2)
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
