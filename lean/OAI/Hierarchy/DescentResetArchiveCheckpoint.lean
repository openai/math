import OAI.Hierarchy.DescentDateTaggedOrdinals
import OAI.Hierarchy.DescentDatePortTaggedRead
import OAI.Hierarchy.DescentResetTaggedArchive
import OAI.Hierarchy.DescentCalendarRangeReturn
import OAI.Hierarchy.DescentPostedResetCheckpoints
import OAI.Hierarchy.DescentRegisteredSelectedReady

namespace OAI
/-! The original registered reset heap and successor port placement on the dated program. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d) {n degree : ℕ} (b : Menu n degree)
    (initial : Position) (i : ℕ) (e : RunTrace.Events traces i)
local notation "pos" => calendar (w:=w) traces b initial i
local notation "nextPos" => calendar (w:=w) traces b initial (i+1)
local notation "ports" => (pos).ports
local notation "s₀" => S.firstWidth G.b b.p
local notation "Z₀" => S.grainAt G.b b.p 0
local notation "floor₀" => (ports).priorStart k (pos).floor
local notation "prior₀" => ((ports).afterPad k (pos).floor).archive
local notation "outer" => scheduledAtPorts G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload b.ordinary b.op s₀ Z₀ (ports) (pos).floor
local notation "model" => (outer).inner
local notation "out" => (model).successor
local notation "ingress" => (model).ingress
local notation "publisher" => priorArchivePhase G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload b.ordinary b.op s₀ Z₀ (ports) (pos).floor w
local notation "raw" => previousArchiveLayout G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload b.ordinary b.op s₀ Z₀ (ports) (pos).floor
local notation "phase" => (ingress).phase floor₀ w (ports).io.hubs (fun x=>(ports).io.atoms x.val)
  (fun j=>(ports).io.wire j.1.val j.2.val)
local notation "codes" => instruction (w:=w) traces b initial
local notation "machine" => RunTrace.machine traces (fun t _=>(codes) t)
variable (geo : Geometry G S b k w i (pos))
local notation "cap" => ((capCalendar G.b S.rounds b.gain S.height).take i).prod*256
variable (space : ScheduledCodeRoom G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
    b.payload b.ordinary b.op s₀ Z₀ (ports).operandLanes (ports).roleLanes (ports).venue (ports).io floor₀ w prior₀)
local notation "u" => DatePorts.resetInputs G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
    b.payload b.ordinary b.op s₀ Z₀ (ports) (pos).floor w space
local notation "v" => (model).successor
local notation "receiver" => (v).receiver
local notation "atMem" boot:arg => (phase).image ((publisher).image (DateCode.history (codes) boot i))

local notation "newPorts" => DatePorts.reset (model) ((model).stageStart floor₀) (u)
local notation "finish" => DatePorts.resetFinalInputs G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
  b.payload b.ordinary b.op s₀ Z₀ (ports) (pos).floor w geo.capacity space

omit [Fintype P] in
/-- The destination heap is the next state of the very instruction that selected these ports. -/
theorem reset_archive_checkpoint (tags : ∀c,(traces c).path.kinds=kindCalendar S.rounds S.height)
    (kind : e.2.isReset=true) (roof : (outer).fullEnd<2^w)
    (ready : (u).Ready) (fitted : (finish).Room) (boot : Memory w) :
    (nextPos).ports=newPorts ∧ (newPorts).rangeLayout=(v).rangeLayout ∧
      ∃mid,(u).throughOperandDate.Runs (atMem boot) mid ∧
        (PhysicalReset.date finish).Runs (atMem boot) (DateCode.history (codes) boot (i+1)) :=by
  have kinds (r : RunTrace.Events traces i) : r.2.isReset=e.2.isReset :=
    r.2.compatible e.2 ((tags r.1).trans (tags e.1).symm)
  have chosen:=reset_return (w:=w) traces b initial i e kind geo.capacity space kinds
  have native : (ports).archive.Fits raw (pos).floor := geo.archive.data (out).setup.retained
  have low := (outer).stages.1.trans_lt ((outer).stages.2.trans_lt roof)
  have pages:=(raw).prior_registers (ports).archive.seed (ports).archive.nodeBase (ports).archive.arguments
    (pos).floor w native.1 native.2 low
  have roles (j : Fin (2^k)) := (ports).archive.roles.fits w (pos).floor j.val
    (j.isLt.trans_le geo.archive.blocks) geo.archive.roles low
  have address := (model).occupied ((model).stageStart floor₀)
  have stage := ((address.1.trans address.2.1).trans address.2.2).trans_lt roof
  have wireFits (j : (ingress).signed.Slot) : ((ports).io.wire j.1.val j.2.val).Fits w (pos).floor := by
    exact (geo.room.wires (j.1.cast (congrArg (2^·) geo.format.width.symm))
      (j.2.cast (congrArg (2*·) geo.capacity.symm))).1
  obtain ⟨_,_,mid,first,done,_⟩:=DatePorts.reset_checkpoints G S b.board k b.tail i b.p b.f b.gain b.drift
    b.degreeLimit b.payload b.ordinary b.op s₀ Z₀ (ports) (pos).floor w geo.capacity space (codes) boot
    chosen.1 ready fitted pages roles geo.room.header.hubs (fun x=>geo.room.paid.stock x.val) wireFits stage
  have issuedPorts : (nextPos).ports=newPorts:=congrArg Position.ports chosen.2.1
  have axes := (reset_range_fields traces b initial i e kind geo.capacity space kinds geo.format.width).2.1
  exact ⟨issuedPorts,issuedPorts ▸ axes,mid,first,done⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
