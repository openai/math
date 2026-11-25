import OAI.Hierarchy.DescentTerminalRegisteredRange
import OAI.Hierarchy.DescentRegisteredWindow
import OAI.Hierarchy.DescentRegisteredFinalEvent

namespace OAI
/-! # The signed packed register on the same native calendar and its last reset -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentPacking.PackedMatch.Local.Stage
open DescentRetainedRangeDigits DescentDatedPriorOperand DescentKernelHistory DescentLocalArchiveOrder
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d) {n degree : ℕ} (b : Menu n degree)
    (initial : Position) (i : ℕ) (e : RunTrace.Events traces i) (kind : e.2.isReset=true)
local notation "datePos" t => calendar (w:=w) traces b initial t
local notation "atDate" => datePos i
local notation "outerAt" => PhysicalReset.scheduledAtPorts G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
  b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) (atDate).ports (atDate).floor
local notation "innerFloor" => (atDate).ports.priorStart k (atDate).floor
local notation "modelAt" => (outerAt).inner
local notation "outputAt" => (modelAt).successor
local notation "previousBase" => (modelAt).rebased ((modelAt).stageStart innerFloor)
variable (cap : (calendar (w:=w) traces b initial i).ports.venue.cap=((capCalendar G.b S.rounds b.gain S.height).take i).prod*256)
    (space : PhysicalReset.ScheduledCodeRoom G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
      b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) (calendar (w:=w) traces b initial i).ports.operandLanes
      (calendar (w:=w) traces b initial i).ports.roleLanes (calendar (w:=w) traces b initial i).ports.venue (calendar (w:=w) traces b initial i).ports.io ((calendar (w:=w) traces b initial i).ports.priorStart k (calendar (w:=w) traces b initial i).floor) w ((calendar (w:=w) traces b initial i).ports.afterPad k (calendar (w:=w) traces b initial i).floor).archive)
    (kinds : ∀r : RunTrace.Events traces i,r.2.isReset=e.2.isReset)
    (radix : (calendar (w:=w) traces b initial i).ports.venue.k=k)

include kind cap space kinds radix in
omit [Fintype P] in
/-- One selected reset identifies all three physical components needed to read its scalar register. -/
theorem reset_range_fields :
    (datePos (i+1)).ports.archive=PriorResetArchive.reset outputAt previousBase ∧
    (datePos (i+1)).ports.rangeLayout=(outputAt).rangeLayout ∧
    (datePos (i+1)).ports.operandBits=(outputAt).nodeBits :=by
  obtain ⟨_,returned,archive⟩:=reset_return traces b initial i e kind cap space kinds
  refine ⟨archive,?_,?_⟩
  · rw [returned]
    apply PhysicalReset.scheduled_range_layout
    exact radix
  · rw [returned]
    rfl

variable {W₀ W : MarkedWorld F d P bits} {i₀ z₀ D₀ z D p : ℕ}
    {start : Reached W₀ G q ε S k i₀ z₀ D₀ wire hist} {now : Reached W G q ε S k (i+1) z D wire hist}
    (hp : 0<p) (a : Archive W₀) (number : Local a.bit) (path : Path start now) (whole : path.whole p)
    (boot : Memory w)
local notation "portsAt" => fun t=> (datePos t).ports
local notation "memoryAt" => DateCode.history (instruction (w:=w) traces b initial) boot
variable (room : ∀{U : MarkedWorld F d P bits} {t g N : ℕ} {r : Reached U G q ε S k t g N wire hist},
  ∀(prefix_ : Path start r) (wh : prefix_.whole p), (∃suffix_ : Path r now,prefix_.append suffix_=path) →
    DatePorts.RangeRoom (calendar (w:=w) traces b initial t).ports r (prefix_.archive p hp a wh).bit)
local notation "dims" => reset_range_fields traces b initial i e kind cap space kinds radix
local notation "okAt" => room path whole ⟨.here,rfl⟩
local notation "occupant" x => Reached.NodeCells.coordinate now (x).1
local notation "nodesAt" => trajectory p hp a number path whole
local notation "nodeTy" => NodeOrder.All (path.archive p hp a whole).bit
local notation "l" => (datePos (i+1)).ports.rangeLayout

omit [Fintype P] in
/-- At the returned reset date the full prefix register is exactly the actual seven-field
archive read on the very same native instruction's memory. -/
theorem final_range_return :
    DatePorts.registeredPages hp a number path portsAt memoryAt room path whole =
    fromRAM (PriorResetArchive.reset outputAt previousBase) (outputAt).rangeLayout (outputAt).nodeBits ((memoryAt) (i+1))
      (by rw [←congrArg Layout.lanes (dims).2.1]; exact (okAt).positive)
      (fun x : nodeTy=>((occupant x).2.2.cast (congrArg (2^·) (okAt).radix)).cast (congrArg Layout.blocks (dims).2.1))
      (fun x : nodeTy=>(⟨(occupant x).1.val,(okAt).hosts x.1⟩:Fin (l).hosts).cast (congrArg Layout.hosts (dims).2.1))
      (fun x : nodeTy=>((occupant x).2.1.cast (okAt).groups).cast (congrArg Layout.groups (dims).2.1))
      (fun x : nodeTy=>(((nodesAt x.1 x.2).castLE ((okAt).capacity x.1)):Fin (l).nodes).cast (congrArg Layout.nodes (dims).2.1)) :=
  DatePorts.registeredPages_final_reset hp a number path portsAt memoryAt room whole outputAt previousBase
    (dims).1 (dims).2.1 (dims).2.2

local notation "cutMemory" => DateCode.history (RunTrace.machine traces (fun t _=>instruction (w:=w) traces b initial t)) boot

omit [Fintype P] in
/-- The chosen path uses the physical memory from the actual finite-cut machine. -/
theorem final_cut_range_return (chosen : C) (inRange : i+1≤final) :
    DatePorts.registeredPages hp a number path portsAt cutMemory room path whole =
    fromRAM (PriorResetArchive.reset outputAt previousBase) (outputAt).rangeLayout (outputAt).nodeBits ((memoryAt) (i+1))
      (by rw [←congrArg Layout.lanes (dims).2.1]; exact (okAt).positive)
      (fun x : nodeTy=>((occupant x).2.2.cast (congrArg (2^·) (okAt).radix)).cast (congrArg Layout.blocks (dims).2.1))
      (fun x : nodeTy=>(⟨(occupant x).1.val,(okAt).hosts x.1⟩:Fin (l).hosts).cast (congrArg Layout.hosts (dims).2.1))
      (fun x : nodeTy=>((occupant x).2.1.cast (okAt).groups).cast (congrArg Layout.groups (dims).2.1))
      (fun x : nodeTy=>(((nodesAt x.1 x.2).castLE ((okAt).capacity x.1)):Fin (l).nodes).cast (congrArg Layout.nodes (dims).2.1)) :=by
  rw [←history_from_cuts traces b initial chosen boot (i+1) inRange]
  exact DatePorts.registeredPages_final_reset hp a number path portsAt cutMemory room whole outputAt previousBase
    (dims).1 (dims).2.1 (dims).2.2

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
