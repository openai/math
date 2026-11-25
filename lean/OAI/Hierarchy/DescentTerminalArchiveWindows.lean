import OAI.Hierarchy.DescentResetRegisteredOperandRows
import OAI.Hierarchy.DescentResetPublicationGeometry
import OAI.Hierarchy.DescentTerminalResetRoleArity

namespace OAI
/-! Every live operand, metadata and primitive word read by the final archive lies between
the reset origin and the end of its metadata checkpoint. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSixParty DescentSIMDLookup DescentDatedNodeMetadata ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable (v : ResetOutput) (base : ℕ)
local notation "top" => v.metadataEnd base
local notation "A" => v.receiver

/-- The allocation includes a full bank even for the last short operand row. -/
theorem field_window (f : Fin 7) (j : Fin v.argumentSlots) (x : Fin (A).blocks) :
    base≤(v.terminalField base f j x).base ∧
      (v.terminalField base f j x).base+(A).hosts*chunks (A).groups (A).lanes≤top :=by
  have data:=v.terminal_field_room base (w:=top) (by exact Nat.lt_two_pow_self) f j x
  have ord:=v.terminal_order base
  constructor
  · have lo : base≤v.scalarEnd base:=by rw [ResetOutput.scalarEnd,v.translated];omega
    change base≤v.scalarEnd base+_+_
    omega
  · exact ((Nat.add_le_add_left data.2 _).trans data.1.2.2).trans (ord.1.trans (ord.2.1.trans ord.2.2))

/-- The two actual node-metadata banks share the same allocation and extent. -/
theorem metadata_window (f : Fin 2) (x : Fin v.metadata.chart.blocks) :
    let b:=v.metadata.chart.bank (v.metadata.headerEnd (v.primitiveEnd base)) f x
    base≤b.base ∧ b.base+v.metadata.chart.rows≤top :=by
  let s:=v.metadata.headerEnd (v.primitiveEnd base)
  have data:=v.metadata.chart.valid (w:=top) s (show top<2^top from Nat.lt_two_pow_self) f x
  constructor
  · have born : base≤v.primitiveEnd base:=by rw [v.primitiveTranslated];omega
    change base≤v.primitiveEnd base+_+_+_+_
    omega
  · exact (Nat.add_le_add_left data.2 _).trans data.1.2.2

/-- The true printed primitive page precedes the metadata, including all its packed host rows. -/
theorem primitive_window (x : Fin v.primitive.chart.blocks) :
    base≤(v.terminalRole base x).base ∧ (v.terminalRole base x).base+v.primitive.chart.rows≤top :=by
  have data:=v.terminal_role_room base (w:=top) (show top<2^top from Nat.lt_two_pow_self) x
  constructor
  · have born : base≤v.birthEnd base:=by rw [v.birthTranslated];omega
    change base≤v.birthEnd base+_+_+_+_+_
    omega
  · exact ((Nat.add_le_add_left data.2 _).trans data.1.2.2).trans (v.terminal_order base).2.2

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "ports" => reset a floor u
local notation "v" => a.successor
local notation "base" => a.rebased floor
local notation "top" => (v).metadataEnd base
local notation "operandRows" => (ports).operandHosts*chunks (ports).venue.groups (ports).operandLanes
local notation "roleRows" => (ports).operandHosts*chunks (ports).venue.groups (ports).roleLanes

private theorem move_previous {l t : Layout} (e : l=t) (b : ℕ) (f : Fin 7) (x : Fin l.blocks) (j : Fin l.operands) :
    previousBank l b x (page f j)=previousBank t b (x.cast (congrArg Layout.blocks e))
      (page f (j.cast (congrArg Layout.operands e))) :=by cases e;rfl

private theorem move_meta {s t : DescentDatedNodeMetadata.Chart} (e : s=t) (b : ℕ) (f : Fin 2) (x : Fin s.blocks) :
    s.bank b f x=t.bank b f (x.cast (congrArg DescentDatedNodeMetadata.Chart.blocks e)):=by cases e;rfl

theorem reset_operand_window (layout:(ports).rangeLayout=(v).rangeLayout) (x:Fin (2^(ports).venue.k))
    (j:Fin (ports).argumentsPerNode) (f:Fin 7) :
    let bank:=previousBank (ports).rangeLayout (ports).archive.arguments x (page f j)
    base≤bank.base ∧ bank.base+operandRows≤top :=by
  have rows:operandRows=(v).receiver.hosts*chunks (v).receiver.groups (v).receiver.lanes:=
    congrArg Layout.rows layout
  dsimp only
  erw [move_previous layout (ports).archive.arguments f x j, rows, (v).operand_bank]
  exact (v).field_window base _ _ _

theorem reset_metadata_window (chart:(ports).metadataChart=(v).metadata.chart) (x:Fin (2^(ports).venue.k)) (f:Fin 2) :
    let bank:=metadataPage ports f x
    base≤bank.base ∧ bank.base+operandRows≤top :=by
  change base≤((ports).metadataChart.bank (ports).archive.nodeBase f x).base ∧
    ((ports).metadataChart.bank (ports).archive.nodeBase f x).base+operandRows≤top
  erw [move_meta chart (ports).archive.nodeBase f x, show operandRows=(v).metadata.chart.rows from congrArg DescentDatedNodeMetadata.Chart.rows chart]
  exact (v).metadata_window base f _

theorem reset_primitive_window (block : 2^(ports).venue.k=(v).primitive.chart.blocks)
    (rows : roleRows=(v).primitive.chart.rows) (x : Fin (2^(ports).venue.k)) :
    base≤((ports).archive.roles.bank x.val).base ∧ ((ports).archive.roles.bank x.val).base+roleRows≤top :=by
  rw [rows]
  exact (v).primitive_window base (x.cast block)


end
end Hierarchy.DescentSixParty.Chronology.DatePorts

namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler DescentDatedPriorOperand
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentOperandStateBanks ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ) (prev : DatePorts) (floor w : ℕ)
local notation "outer" => scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z prev floor
local notation "output_" => (outer).inner.successor
local notation "innerFloor" => prev.priorStart k floor
local notation "previous" => (prev.afterPad k floor).archive
variable (space : ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
  prev.operandLanes prev.roleLanes prev.venue prev.io (prev.priorStart k floor) w (prev.afterPad k floor).archive)
local notation "inputs" => resetInputs G S board k tail age p f gain drift degree h ordinary op s Z prev floor w space
local notation "next_" => resetPorts G S board k tail age p f gain drift degree h ordinary op s Z prev floor w space


local notation "base_" => (outer).inner.rebased ((outer).inner.stageStart innerFloor)
local notation "rows_" => (next_).operandHosts*chunks (next_).venue.groups (next_).operandLanes
local notation "roleRows_" => (next_).operandHosts*chunks (next_).venue.groups (next_).roleLanes

set_option maxHeartbeats 800000 in
/-- All original archive words at the scheduled last reset have a common protected interval. -/
theorem scheduled_archive_windows (oldK : prev.venue.k=k) :
    (∀x (j:Fin (next_).argumentsPerNode) f,
      let b:=previousBank (next_).rangeLayout (next_).archive.arguments x (page f j)
      base_≤b.base ∧ b.base+rows_≤(output_).metadataEnd base_) ∧
    (∀x f,let b:=metadataPage next_ f x
      base_≤b.base ∧ b.base+rows_≤(output_).metadataEnd base_) ∧
    (∀x:Fin (2^(next_).venue.k),let b:=(next_).archive.roles.bank x.val
      base_≤b.base ∧ b.base+roleRows_≤(output_).metadataEnd base_) :=by
  have geo:=reset_publication_geometry G S board k tail age p f gain drift degree h ordinary op s Z prev floor w space oldK
  refine ⟨fun x j f=>reset_operand_window inputs geo.axes x j f,
    fun x f=>reset_metadata_window inputs geo.chart x f,?_⟩
  apply reset_primitive_window inputs
  · change 2^prev.venue.k=2^k
    rw [oldK]
  · rfl

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
