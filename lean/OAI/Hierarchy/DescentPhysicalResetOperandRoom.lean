import OAI.Hierarchy.DescentPhysicalOperandBounds
import OAI.Hierarchy.DescentPublishedOperandRoom
import OAI.Hierarchy.DescentDatedRetainedSpace
import OAI.Hierarchy.DescentPhysicalResetDateOperands
import OAI.Hierarchy.DescentResetControlPackedSources

namespace OAI
/-! Static addressing of the two complete families requested by the ranked reset operand receiver. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open ProtocolRAM DescentSIMDLookup DescentPackedZip DescentResetOperandSetup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "first" => (v).operandFloor b
local notation "C" => (v).setup
local notation "ctrl" => (v).controlRegisters
local notation "start" => (v).controlFloor b
local notation "origin" => (v).middle.stop b
local notation "dir" => (v).actor.directory origin
local notation "depth" => (v).actor.depths origin
local notation "levels" => (v).actor.levels origin
local notation "rankInput" => (v).linkedRankInputs u.sectors ((v).sheets.originalEnd ((v).remap b).endAddress)

theorem raw_request_room (space : (v).operandStart b<2^w) (blocks : (C).placement.blocks=(ctrl).dims.blocks)
    (inv : (dir).inverse.Fits w first) (dep : (depth).Fits w first) (lev : (levels).Fits w first)
    (aux : (v).jointEnd b≤first)
    (coord : ((v).sheets.stemSources.coord.endAddress ((v).sheets.metaEnd ((v).remap b).endAddress))≤first)
    (saved : (⟨(a.stencilPhase u.shape floor u.count u.hub u.g u.Y).saved,0⟩:Bank).Fits w
      ((v).sheets.metaEnd ((v).remap b).endAddress))
    (parent : (C).packets.parent+DescentDyadicSpan.span (C).packets.receivers≤(C).placed first)
    (hubs : ∀x,((v).retainedHub b x).Fits w ((C).casts first))
    (tickets : ∀x j,((v).retainedTicket b x j).Fits w ((C).casts first)) :
    (∀i,(u.rawOperands.query i).Fits w ((v).keepBase b)) ∧
    (∀i,(u.rawOperands.kept i).Fits w ((v).keepBase b)):=by
  obtain ⟨a₁,b₁,c₁,d,e,g,h,l⟩:=(C).order first
  have after_:=a₁.trans (b₁.trans (c₁.trans (d.trans (e.trans (g.trans (h.trans l))))))
  have packet: (C).placed first≤(C).packetEnd first:=((C).packets.join _).1.trans ((C).packets.join _).2
  have low:first≤(C).publicEnd first:=by
    obtain ⟨t,q,k⟩:=(C).before first
    exact t.trans (q.trans (k.trans (packet.trans (Nat.le_add_right ..))))
  have short:=((v).keep_before b).trans_lt space
  have body (x : Fin (C).placement.blocks) (arg : Fin (C).retained.args) (node : Fin (C).retained.nodes)
      (mode : Option (Fin 7)) :
      let live:=(ctrl).live start x.val
      let reg:=(ctrl).ports start (a.c/2) x.val (dir).inverse depth levels
      ((C).selected first u.laws mode x arg node
        ((C).carried first x arg node ((v).retainedHub b x) ((v).retainedTicket b x))
        reg (u.menu.publicInput u.shape floor u.count u.hub u.g u.Y live reg x.val)).Fits w ((v).keepBase b):=by
    intro live reg
    have safe:=(ctrl).port_fits start (x.cast blocks) (a.c/2) (dir).inverse depth levels
      ((low.trans after_).trans_lt short) inv dep lev
    have old:=(C).carried_fits first ((b₁.trans (c₁.trans (d.trans (e.trans (g.trans (h.trans l)))))).trans_lt short)
      x arg node ((v).retainedHub b x) ((v).retainedTicket b x) (hubs x) (tickets x)
    have public_:=u.menu.published_input_room u.shape floor u.count u.hub u.g u.Y
      live reg (after_.trans_lt short) aux coord saved parent
      (ProtocolRAMGeneratedWrite.fits_mono _ low safe.1)
      (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ low (safe.2 i)) x.val
    exact (C).selected_fits first u.laws mode x arg node _ _ _ old.1 old.2
      (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ (low.trans (a₁.trans (b₁.trans (c₁.trans d)))) (safe.2 i))
      (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ (a₁.trans (b₁.trans (c₁.trans (d.trans (e.trans g))))) (public_ i)) short
  exact ⟨fun _=>body _ _ _ none,fun _=>body _ _ _ (some _)⟩

theorem request_room (space : (v).operandStart b<2^w) (blocks : (C).placement.blocks=(ctrl).dims.blocks)
    (inv : (dir).inverse.Fits w first) (dep : (depth).Fits w first) (lev : (levels).Fits w first)
    (aux : (v).jointEnd b≤first)
    (coord : ((v).sheets.stemSources.coord.endAddress ((v).sheets.metaEnd ((v).remap b).endAddress))≤first)
    (saved : (⟨(a.stencilPhase u.shape floor u.count u.hub u.g u.Y).saved,0⟩:Bank).Fits w
      ((v).sheets.metaEnd ((v).remap b).endAddress))
    (parent : (C).packets.parent+DescentDyadicSpan.span (C).packets.receivers≤(C).placed first)
    (hubs : ∀x,((v).retainedHub b x).Fits w ((C).casts first))
    (tickets : ∀x j,((v).retainedTicket b x j).Fits w ((C).casts first)) :
    (∀i,(u.operand.query i).Fits w ((v).operandStart b)) ∧
    (∀i,(u.operand.kept i).Fits w ((v).operandStart b)):=by
  obtain ⟨query,kept⟩:=u.raw_request_room space blocks inv dep lev aux coord saved parent hubs tickets
  exact ⟨fun i=>ProtocolRAMGeneratedWrite.fits_mono _ ((v).keep_before b) (query i),
    fun i=>(v).keptValue_fits b _ (kept i) space⟩

theorem operand_room (space : (v).operandStart b<2^w) (rank : ((v).rankBook rankInput b).Previous w)
    (query : ∀i,(u.operand.query i).Fits w ((v).operandStart b)) (kept : ∀i,(u.operand.kept i).Fits w ((v).operandStart b)) :
    (v).OperandEarly u.operand ((v).renderFromRanks rankInput b) w b :=by
  let L:=(v).rankBook rankInput b
  have near : (v).fieldsEnd b≤(v).controlFloor b:=by
    change (v).fieldsEnd b≤DescentNextSignedWindow.Native.All.endAddress ((v).fieldsEnd b) _ _ _ _ _ _
    unfold DescentNextSignedWindow.Native.All.endAddress
    omega
  have control : (v).controlFloor b≤first:=by
    change _≤(ctrl).endAddress start
    rw [(ctrl).translated start]
    exact Nat.le_add_right ..
  have placed : first≤(v).operandStart b:=by
    apply le_trans _ ((v).keep_before b)
    change first≤(C).endAddress first
    rw [(C).affine first]
    exact Nat.le_add_right ..
  have chart:=(near.trans control).trans placed
  have roof : (v).rankEnd b<2^w:=(Nat.le_add_right _ _).trans_lt (chart.trans_lt space)
  obtain ⟨a₀,a₁,a₂,a₃⟩:=L.ordered
  have headers:=fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ (((a₀.trans a₁).trans a₂).trans a₃) (rank.header x j)
  have native:=DescentResetFieldAssembler.any («b»:=(v).assemblerBits) (M:=(v).receiver.lanes) ((v).rankEnd b)
    (rankInput).header L.finalRank (fun _=>(0:Word w)) headers (L.finalRank_fits rank roof) (chart.trans_lt space)
  refine ⟨query,kept,?_⟩
  intro i j
  unfold ResetOutput.previous
  dsimp only
  cases chosen : ResetOutput.pointerField _ with
  | none=>trivial
  | some port=>exact ProtocolRAMGeneratedWrite.fits_mono _ chart (native.2.1 _ j port)

/-- The compiled prior and both numerical candidate menus, including the physically
stored relay tickets and their trunk marks, for any array of input words. -/
theorem issued_operand_room (space : (v).operandStart b<2^w)
    (rank : ((v).rankBook rankInput b).Previous w) (blocks : (C).placement.blocks=(ctrl).dims.blocks)
    (inv : (dir).inverse.Fits w first) (dep : (depth).Fits w first) (lev : (levels).Fits w first)
    (aux : (v).jointEnd b≤first)
    (coord : (v).sheets.stemSources.coord.endAddress ((v).sheets.metaEnd ((v).remap b).endAddress)≤first)
    (saved : (⟨(a.stencilPhase u.shape floor u.count u.hub u.g u.Y).saved,0⟩:Bank).Fits w
      ((v).sheets.metaEnd ((v).remap b).endAddress))
    (parent : (C).packets.parent+DescentDyadicSpan.span (C).packets.receivers≤(C).placed first)
    (slots : (v).front.signedQueries/2+(C).strip≤(v).receiver.candidates) :
    (v).OperandEarly u.operand ((v).renderFromRanks rankInput b) w b :=by
  obtain ⟨_,p,q,r,s,t,i,j⟩:=(C).order first
  have early := (p.trans (q.trans (r.trans (s.trans (t.trans (i.trans j)))))).trans_lt (((v).keep_before b).trans_lt space)
  have ready:=u.request_room space blocks inv dep lev aux coord saved parent
    (fun x=>(v).retained_hub_fits b ((v).issuedScene b u.earlier) x early)
    (fun x d=>(v).retained_ticket_fits b x d u.operandBlocks.symm
      ((Nat.add_lt_add_left d.isLt _).trans_le slots) early)
  exact u.operand_room space rank ready.1 ready.2

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
