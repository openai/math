import OAI.Hierarchy.DescentDatedRetainedTicket
import OAI.Hierarchy.DescentPhysicalTrunkRoom
import OAI.Hierarchy.DescentRankPortPrefixRoom

namespace OAI
/-! # Live address bounds for both retained reset correction fields -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup DescentDyadicSpan DescentPackedZip DescentResetStemHeaders
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable (v : ResetOutput) (base : ℕ)
local notation "F" => v.front
local notation "A" => v.receiver
local notation "C" => v.setup
local notation "cut" => v.actorEnd base
local notation "stop" => (C).casts (v.operandFloor base)
local notation "pay" => (C).publicEnd (v.operandFloor base)
local notation "n₀" => ((F).newHosts*chunks (F).peer.groups (F).peer.lanes)
local notation "pointer" => DescentResetTrunkCompactGather.rows ((F).mixed cut) (F).newHosts (F).peer.groups (F).peer.lanes

theorem correction_cuts :
    v.trunkEnd base≤v.ticketEnd base ∧ v.ticketEnd base≤pay ∧ pay≤ stop:=by
  have middle:=v.ranked_space_earlier base
  have trunk : v.trunkEnd base≤v.massEnd base:=by unfold massEnd;rw [v.contactShape.translate];omega
  have c:=(v.rankPort_after base)
  have t : v.rankPortEnd base≤v.ticketEnd base:=by
    exact (Nat.le_add_right (v.rankPortEnd base) _).trans
      ((Nat.le_add_right (v.pairEnd base) _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have t₁:=(v.earlier base).2.1
  have t₂ : v.rankEnd base≤v.fieldsEnd base:=Nat.le_add_right ..
  have panel:=((A).occupied (v.fieldsEnd base)).1
  have heads : v.controlFloor base≤v.operandFloor base:=by rw [operandFloor,v.controlRegisters.translated];omega
  have placed : v.operandFloor base≤(C).placed (v.operandFloor base):=by rw [(C).placed_shift];omega
  have packets : (C).placed (v.operandFloor base)≤(C).packetEnd (v.operandFloor base):=by
    unfold DescentResetOperandSetup.Chart.packetEnd
    rw [(C).packets.extent]
    omega
  have stamps : (C).packetEnd (v.operandFloor base)≤pay:=Nat.le_add_right ..
  exact ⟨trunk.trans (middle.2.1.trans (c.trans t)),
    t₁.trans (t₂.trans (panel.trans (heads.trans (placed.trans (packets.trans stamps))))),(C).order _ |>.1⟩

theorem retained_hub_fits {w : ℕ} (s : (F).Scene) (x : Fin (C).placement.blocks) (roof : stop<2^w) :
    (v.retainedHub base x).Fits w stop:=by
  have ⟨a,b,c⟩:=v.correction_cuts base
  have ⟨raw,headEnd,_⟩:=(F).trunk_regions_of_format cut s.stems.queries s.stems.digits
  have go : (F).mixed cut≤pointer:=by
    change _≤(F).mixed cut+span (F).newHosts+DescentResetStemKeyReindex.size (F).newHosts (F).newHosts (F).peer.groups (F).peer.lanes
    omega
  have gather : pointer≤(F).gathered cut:=Nat.le_add_right ..
  have trunk : (F).gathered cut≤(F).trunkEnd cut:=Nat.le_add_right ..
  have bound:=headEnd.trans (go.trans (gather.trans (trunk.trans (a.trans (b.trans c)))))
  have head:=DescentResetStemHeaders.body_fits (K:=1) (H:=(F).newHosts) (G:=(F).peer.groups)
    (M:=(F).peer.lanes) (b:=(F).metaBits*7) (raw:=(F).peer.endAddress ((F).peers cut))
    (base:=(F).trunkHeader cut) (by simpa using raw) (by simpa using bound.trans_lt roof) (0:Fin 1)
  apply DescentRetainedHubFlag.ready
  apply ProtocolRAMGeneratedWrite.fits_mono _ _ head
  exact (Nat.le_add_right _ _).trans bound

theorem incoming_row_fits {w : ℕ} (x : Fin (C).placement.blocks) (d : Fin (C).strip)
    (blocks : (C).placement.blocks=(A).blocks)
    (slot : (F).signedQueries/2+d.val<(A).candidates) (roof : v.ticketEnd base<2^w) :
    (v.incomingTicketRow base x d).Fits w (v.ticketEnd base):=by
  have ⟨lower,pre,post⟩:=v.correction_cuts base
  have bank:=DescentResetSourceTicketBank.column_fits (b:=v.ticketBits) (M:=(A).lanes)
    (H:=(A).hosts) (G:=(A).groups) (root:=v.pairEnd base) (X:=(A).blocks) (K:=(A).candidates)
    roof (x.cast blocks) ⟨(F).signedQueries/2+d.val,slot⟩
  have tabCut : pointer+span n₀=(F).gathered cut:=rfl
  have order : (F).gathered cut≤v.ticketEnd base:=(Nat.le_add_right ..).trans lower
  have table : (DescentResetTrunkGather.table pointer n₀).Fits w (v.ticketEnd base):=by
    change 0<span n₀ ∧ span n₀<2^w ∧ pointer+span n₀≤v.ticketEnd base
    have high:=order.trans_lt roof
    exact ⟨span_pos _,by omega,tabCut.le.trans order⟩
  have source : (v.incomingTicketBank base x d).Fits w (v.ticketEnd base):=⟨bank.1,bank.2.1,bank.2.2⟩
  exact ⟨⟨table,trivial⟩,trivial,trivial,source,table,trivial⟩

theorem retained_ticket_fits {w : ℕ} (x : Fin (C).placement.blocks) (d : Fin (C).strip)
    (blocks : (C).placement.blocks=(A).blocks)
    (slot : (F).signedQueries/2+d.val<(A).candidates) (roof : stop<2^w) :
    (v.retainedTicket base x d).Fits w stop:=by
  have ⟨_,pre,post⟩:=v.correction_cuts base
  have ready:=ProtocolRAMGeneratedWrite.fits_mono _ pre
    (v.incoming_row_fits base x d blocks slot ((pre.trans post).trans_lt roof))
  exact DescentOperandInputCast.expr_fits _ _ _ _ _ _ _ ((C).width_le _) ready roof

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
