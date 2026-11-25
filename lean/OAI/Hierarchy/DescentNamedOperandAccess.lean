import OAI.Hierarchy.DescentPhysicalResetOperandRoom
import OAI.Hierarchy.DescentNamedSheetAccess
import OAI.Hierarchy.DescentPhysicalOperandCuts
import OAI.Hierarchy.DescentPreparedSavedRegister
import OAI.Hierarchy.DescentPhysicalOperandSetupRoom
import OAI.Hierarchy.DescentResetPublicCuts

namespace OAI
/-! The preceding root, actor and rank charts give all operands of the reset's final seven-field receiver. -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSIMDLookup DescentPackedZip DescentResetMixedWordRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

theorem ActorSetup.depth_words (v : ActorSetup) (start stop w : ℕ)
    (past : v.directoryEnd start≤ stop) (room : stop<2^w) :
    (v.depths start).Fits w stop ∧ (v.levels start).Fits w stop:=by
  have ⟨_,n,m,l,h⟩:=v.monotone start
  have d : (v.depths start).base+(v.depths start).size=(v.counts start).base:=rfl
  obtain ⟨b,c,e⟩:=v.gate_order start
  have go : (v.gate start).repeatBase≤(v.gate start).gateBase:=by
    rw [←c]
    unfold DescentSharedLeafLookup.Public.stop
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have body : (v.gate start).output≤v.endAddress start:=Nat.le_add_right ..
  have roof : v.endAddress start≤v.directoryEnd start:=Nat.le_add_right ..
  have hi : (v.levels start).base+(v.levels start).size≤ stop:=by omega
  have lo : (v.depths start).base+(v.depths start).size≤ stop:=by omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (lo.trans_lt room),lo⟩,
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (hi.trans_lt room),hi⟩⟩

namespace PhysicalReset.DateInputs
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "first" => (v).operandFloor b
local notation "C" => (v).setup
local notation "R" => (v).linkedRankInputs u.sectors ((v).sheets.originalEnd ((v).remap b).endAddress)
local notation "roots" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w

theorem raw_operand_access (roof : (v).finalEnd b<2^w)
    (placed : (C).Ready u.bank w first) (rootAt : (roots).preparedEnd u.book=(v).middle.stop b)
    (blocks : (C).placement.blocks=(v).controlRegisters.dims.blocks)
    (slots : (v).front.signedQueries/2+(C).strip≤(v).receiver.candidates) :
    (∀i,(u.rawOperands.query i).Fits w ((v).keepBase b)) ∧ (∀i,(u.rawOperands.kept i).Fits w ((v).keepBase b)):=by
  have cuts:=(v).cuts b
  obtain ⟨_,joint,coord,_,last⟩:=(v).operands_after_front b
  have upto:=(v).control_address_bounds b
  have dirFirst : (v).actorEnd b≤first:=
    (cuts.trunk.trans (cuts.mass.trans cuts.joint)).trans joint
  have origin:=(cuts.actors.trans (cuts.trunk.trans (cuts.mass.trans (cuts.joint.trans
    (cuts.privateEnd.trans cuts.meta)))))
  have saved:=(roots).saved_register_room u.book u.bookFits
  rw [rootAt] at saved
  have floorFit : first<2^w:=upto.2.2.2.trans_lt roof
  have depth:=(v).actor.depth_words ((v).middle.stop b) first w dirFirst floorFit
  have room:=last.trans_lt roof
  obtain ⟨_,p,q,r,s,t,i,j⟩:=(C).order first
  have early:=(p.trans (q.trans (r.trans (s.trans (t.trans (i.trans j)))))).trans_lt
    (((v).keep_before b).trans_lt room)
  exact u.raw_request_room room blocks placed.inverse depth.1 depth.2 joint coord
    ⟨saved.1,saved.2.1,saved.2.2.trans origin⟩ placed.packets.2.1
    (fun x=>(v).retained_hub_fits b ((v).issuedScene b u.earlier) x early)
    (fun x d=>(v).retained_ticket_fits b x d u.operandBlocks.symm
      ((Nat.add_lt_add_left d.isLt _).trans_le slots) early)

theorem operand_access (roof : (v).finalEnd b<2^w) (rank : ((v).rankBook R b).Previous w)
    (placed : (C).Ready u.bank w first) (rootAt : (roots).preparedEnd u.book=(v).middle.stop b)
    (blocks : (C).placement.blocks=(v).controlRegisters.dims.blocks)
    (slots : (v).front.signedQueries/2+(C).strip≤(v).receiver.candidates) :
    (v).OperandEarly u.operand ((v).renderFromRanks R b) w b:=by
  have packed:=u.raw_operand_access roof placed rootAt blocks slots
  have room:=((v).operands_after_front b).2.2.2.2.trans_lt roof
  exact u.operand_room room rank
    (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ ((v).keep_before b) (packed.1 i))
    (fun i=>(v).keptValue_fits b _ (packed.2 i) room)

end PhysicalReset.DateInputs
end
end Hierarchy.DescentDatedAddressBook

end OAI
