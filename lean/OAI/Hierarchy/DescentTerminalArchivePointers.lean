import OAI.Hierarchy.DescentTerminalArchiveCellPointer
import OAI.Hierarchy.DescentTerminalReachedPointerOrigin
import OAI.Hierarchy.DescentArchiveOriginalSlot

namespace OAI
/-! # Reading live terminal rectangles at the actual archived scalar node -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup DescentTerminalPointerDigits ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age grain degree wire hist w : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B)

variable {p R s Z : ℕ} (shape : WorldShape p R B) (op : RotorSpec)
    (label : NodeOrder.All B→Label G s Z op) (pointer : NodeOrder.All B→ℕ→Pointer)
    (flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)

open DescentTerminalPointerIssue DescentLocalPrivateNames DescentTerminalChronologicalBooks
variable {ports r B number room shape op label pointer flags}
variable {m : Memory w} (held : ArchiveRead ports r B number room shape op label pointer flags m)
    (hp : 0<p) (fmt : Widths) (capacity : fmt.nodeCapacity=some ports.nodes) (width : ∀f,fmt.pointer f=ports.operandBits)
    (packed : (ports.operandBits*ports.nodes)*ports.operandLanes≤w) (single : chunks ports.venue.groups ports.operandLanes=1)
    (v : W.graph.Site) {K d₀ : ℕ}
local notation "coord_" => Reached.NodeCells.coordinate r v
local notation "block_" => (coord_).2.2.cast (congrArg (2^·) room.radix)
local notation "host_" => (⟨(coord_).1.val,room.hosts v⟩ : Fin ports.operandHosts)
local notation "group_" => (coord_).2.1.cast room.groups
local notation "rawR" => (shape.sites v).recipe hp
local notation "birth_" => (number v).toEmbedding.trans Fin.valEmbedding
variable (args : ∀u,((shape.sites v).recipe hp).arity u≤K)
    (oldArgs : ∀u,((shape.sites v).recipe hp).arity u≤ports.argumentsPerNode)
local notation "loc_" => DescentTerminalPointerIssue.slot rawR birth_ (room.capacity v) args
variable (pages : Gather.Pages (2^ports.venue.k) r.placement.cap K) (current : Memory w)
    (t : CellInputs r.placement.degree r.placement.cap ports.nodes K)

private theorem ordinal_of_number {I : Type} [Fintype I] {n : ℕ} (e : I≃Fin n) (u : I) :
    (ordinal (e.toEmbedding.trans Fin.valEmbedding) u).val=(e u).val :=
  (ordinal_val (e.toEmbedding.trans Fin.valEmbedding) u).trans (Reached.earlier_count e u)

include held capacity width packed single in
/-- All existing slots select their actual original header at the chronological
host, group and block. The proof also covers zero operands and empty private lists. -/
theorem ArchiveRead.terminal_live_pointers
    (hold : ∀(s:Slot rawR) (f:Fin 4), current ((pages.pointers f (s.2.castLE (args s.1)) block_).base+(host_).val)=
      m ((previousBank ports.rangeLayout ports.archive.arguments block_ (DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) (s.2.castLE (oldArgs s.1)))).base+(host_).val))
    (fits : (ports.operandBits*ports.nodes)*((group_).val+1)≤d₀)
    (read : SourceRead fmt (pages.source (d:=d₀) current block_ host_) (group_).val t)
    (population : t.n=Fintype.card (rawR).Node)
    (arities : ∀u,t.arity (DescentTerminalPointerIssue.row rawR birth_ (room.capacity v) u)=(rawR).arity u) :
    ∀s:Slot rawR,t.pointer (loc_ s)=pointer ⟨v,s.1⟩ s.2.val :=by
  intro s
  let i:=loc_ s
  have pair : (finProdFinEquiv (m:=ports.nodes) (n:=K)).symm i=(DescentTerminalPointerIssue.row rawR birth_ (room.capacity v) s.1,s.2.castLE (args s.1)) :=by
    exact Equiv.symm_apply_apply _ _
  have operandIndex := congrArg Prod.snd pair
  have operandDigit : ((finProdFinEquiv (m:=ports.nodes) (n:=K)).symm i).2.val=s.2.val :=
    (congrArg Fin.val operandIndex).trans (Fin.val_castLE (args s.1) s.2)
  have inCap : ((finProdFinEquiv (m:=ports.nodes) (n:=K)).symm i).2.val<ports.argumentsPerNode:=by rw [pair];exact s.2.isLt.trans_le (oldArgs _)
  have idx : nodeOf i=(number v s.1).castLE (room.capacity v) :=by
    apply Fin.ext
    change ((finProdFinEquiv (m:=ports.nodes) (n:=K)).symm i).1.val=_
    rw [pair]
    change (ordinal birth_ s.1).val=(number v s.1).val
    exact ordinal_of_number (I := (rawR).Node) (number v) s.1
  have place : slotAt ports r B number room block_ (nodeOf i) host_ group_=some ⟨v,s.1⟩:=by
    rw [idx]
    exact slotAt_original ports r B number room v s.1
  have active : ((finProdFinEquiv (m:=ports.nodes) (n:=K)).symm i).2.val<(occurrences (shape.sites v) s.1).length:=by
    exact operandDigit.trans_lt (s.2.isLt.trans_eq (DescentRetainedRangeDigits.length (shape.sites v) s.1 hp).symm)
  have kept : ∀ f,current ((pages.pointers f ((finProdFinEquiv (m:=ports.nodes) (n:=K)).symm i).2 block_).base+(host_).val)=
      m ((previousBank ports.rangeLayout ports.archive.arguments block_ (DescentOperandStateBanks.page (f.castLE (by decide : 4≤7))
        ⟨((finProdFinEquiv (m:=ports.nodes) (n:=K)).symm i).2.val,inCap⟩)).base+(host_).val) :=by
    intro f
    have oldIndex : (⟨((finProdFinEquiv (m:=ports.nodes) (n:=K)).symm i).2.val,inCap⟩ : Fin ports.argumentsPerNode) =
        s.2.castLE (oldArgs s.1) := Fin.ext operandDigit
    exact (congrArg (fun arg : Fin K=>current ((pages.pointers f arg block_).base+(host_).val)) operandIndex).trans
      ((hold s f).trans (congrArg (fun arg : Fin ports.argumentsPerNode=>
        m ((previousBank ports.rangeLayout ports.archive.arguments block_
          (DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) arg)).base+(host_).val)) oldIndex.symm))
  have result:=held.cell_pointer_at fmt capacity width room.positive packed single current block_ host_ group_ i
    inCap ⟨v,s.1⟩ place active pages kept fits t read (live_slot rawR birth_ (room.capacity v) args t population arities s)
  exact result.trans (congrArg (pointer ⟨v,s.1⟩) operandDigit)


open DescentStageEdgeReceipt
variable [Fintype P] {oldNodes extSize : ℕ} (past : Fintype.card ((shape.sites v).recipe hp).Node≤oldNodes)
    (port : Attached W.graph v≃Fin extSize) (pin : P→ℕ) (freeze : ℕ→ℕ)
local notation "oldSlot" => DescentTerminalPointerIssue.slot rawR birth_ past oldArgs
local notation "ports_" => port.toEmbedding.trans Fin.valEmbedding
local notation "names_" => DescentPacking.PackedMatch.Local.Stage.cableNames k
    (groupRank (Fin.valEmbedding (n:=S.groupCount age)) (r.vertex.trans Fin.valEmbedding))
local notation "orig_" => Reached.argumentPointer r B number shape hp pin ports.argumentsPerNode

include capacity width packed single in
/-- At every actual scalar vertex the four held header columns are sufficient
to construct the complete terminal pointer interpretation. -/
theorem ArchiveRead.original_pointer_origin
    (saved : ArchiveRead ports r B number room shape op label orig_ flags m)
    (hold : ∀(s:Slot rawR) (f:Fin 4), current ((pages.pointers f (s.2.castLE (args s.1)) block_).base+(host_).val)=
      m ((previousBank ports.rangeLayout ports.archive.arguments block_ (DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) (s.2.castLE (oldArgs s.1)))).base+(host_).val))
    (fits : (ports.operandBits*ports.nodes)*((group_).val+1)≤d₀)
    (read : SourceRead fmt (pages.source (d:=d₀) current block_ host_) (group_).val t)
    (population : t.n=Fintype.card (rawR).Node)
    (arities : ∀u,t.arity (DescentTerminalPointerIssue.row rawR birth_ (room.capacity v) u)=(rawR).arity u)
    (publicAt : ∀z:Attached W.graph v,freeze (pin z.val)=(port z).val) :
    DescentTerminalPointerIssue.Origin W.graph v rawR birth_ (room.capacity v) args oldSlot
      (DescentTerminalPortChart.rank r.placement (r.order.trans Fin.valEmbedding) S r.valid names_ v ports_) ports_
      (reindexed t freeze) :=by
  apply Reached.argument_origin r B number shape hp pin v (room.capacity v) args past oldArgs port freeze
    t population arities ?_ publicAt
  exact saved.terminal_live_pointers hp fmt capacity width packed single v args oldArgs pages current t hold fits read population arities

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
