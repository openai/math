import OAI.Hierarchy.DescentNamedFinalPointerArchive
import OAI.Hierarchy.DescentTerminalArchiveWindows
import OAI.Hierarchy.DescentArchiveReadBetween

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P → ℕ} {d k wire hist w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C → RunTrace G q ε S k wire hist S.length bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)
local notation "cursor" => calendar (w:=w) traces b initial
local notation "priorCursor" => cursor (S.length-1)
local notation "lastSpace" => ScheduledCodeRoom G S b.board k b.tail (S.length-1) b.p b.f b.gain
  b.drift b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0)
  (priorCursor).ports.operandLanes (priorCursor).ports.roleLanes (priorCursor).ports.venue (priorCursor).ports.io
  ((priorCursor).ports.priorStart k (priorCursor).floor) w ((priorCursor).ports.afterPad k (priorCursor).floor).archive
local notation "outputPorts" sp:arg => DatePorts.resetPorts G S b.board k b.tail (S.length-1) b.p b.f b.gain
  b.drift b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0)
  (priorCursor).ports (priorCursor).floor w sp

local notation "lastJob_" => PhysicalReset.scheduledAtPorts G S b.board k b.tail (S.length-1) b.p b.f b.gain
  b.drift b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0)
  (priorCursor).ports (priorCursor).floor
local notation "floor_" => (priorCursor).ports.priorStart k (priorCursor).floor
local notation "origin_" => (lastJob_).inner.rebased ((lastJob_).inner.stageStart floor_)
local notation "end_" => (lastJob_).inner.successor.metadataEnd origin_

omit [Fintype P] in
private theorem finalResetFloorWidth
    (fixed : ∀ i (e f : RunTrace.Events traces i) x y,
      issued (w:=w) traces b i e (cursor i) x → issued (w:=w) traces b i f (cursor i) y → x=y)
    (caps : ∀ c,(traces c).path.capFactors=capCalendar G.b S.rounds b.gain S.height)
    (tags : ∀ c,(traces c).path.kinds=kindCalendar S.rounds S.height)
    (ready : Geometry G S b k w 0 initial)
    (placed : ∀ i (e : RunTrace.Events traces i), fitsAt traces b initial (w:=w) i e)
    (c : C) {p : ℕ} (ticket : Path.FinalReset p (traces c).path) :
    ∃ space : lastSpace,(cursor S.length).ports=outputPorts space ∧
      end_=(cursor S.length).floor ∧ (priorCursor).ports.venue.k=k ∧ initial.floor ≤ origin_ := by
  have geo:=geometry_on_event traces b initial fixed caps tags ready placed c (S.length-1) ticket.event
  obtain ⟨move,located,_,_⟩:=placed (S.length-1) ⟨c,ticket.event⟩ geo
  obtain ⟨_,space,_,_,next⟩:=final_move traces b initial c ticket fixed ⟨move,located⟩
  refine ⟨space,congrArg Position.ports next,(congrArg Position.floor next).symm,geo.format.width,?_⟩
  have low : initial.floor ≤ (priorCursor).floor := by
    rw [position_floor (RegisterTimeline.issued (w:=w) traces b) initial (S.length-1)]
    exact DescentDatedAddressBook.floor_mono initial.floor (span _ initial) (Nat.zero_le _)
  have cuts := ((priorCursor).ports.resetPad k).cuts (priorCursor).floor
  have padded : initial.floor ≤ floor_ := (low.trans (cuts.1.trans cuts.2)).trans (((priorCursor).ports.presence k).lower _)
  have booked := (lastJob_).inner.occupied ((lastJob_).inner.stageStart floor_)
  exact ((padded.trans ((lastJob_).inner.ingress.after floor_)).trans booked.1).trans booked.2.1

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

/-! The chosen archive's actual token, arity and all seven operand fields survive capture and role mounting. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline DescentLocalArchiveOrder DescentPrimitivePalette DescentKernelHistory
open DescentBundleHistory DescentOperandStateBanks Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
set_option quotPrecheck false
open private chosenClaim from OAI.Hierarchy.DescentNamedArchivePrefix
attribute [local irreducible] Origin.source Origin.archivePackage issued
variable {F : Type} [Field F]
variable {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)
variable {n₀ δ : ℕ} (b : RegisterTimeline.Menu n₀ δ) (initial : RegisterTimeline.Position)
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces b initial
local notation "issue" => RegisterTimeline.issued (w:=w) traces b
local notation "prog" => RegisterTimeline.instruction (w:=w) traces b initial


variable (gain : b.gain=g) (grain : b.p=p) (arity : b.f=f)
variable (ready : Geometry G S b k w 0 initial)
variable (placed : ∀i (e : RunTrace.Events (traceAt X G S ordinary reset branch positive room shorten) i),fitsAt (traceAt X G S ordinary reset branch positive room shorten) b initial (w:=w) i e)
open private register_cap_calendar from OAI.Hierarchy.DescentNamedPrefixState
open private traceAt_kinds from OAI.Hierarchy.DescentNamedBranchMachine
local notation "fixed" => all_registered_moves X G S ordinary reset branch positive room shorten w b gain grain arity
variable (z : (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).Pin → Bool) (walk : (Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice) (m : Memory w)
local notation "limit" => ((ch).rows z).length
local notation "valid" => (ch).read z=some walk
local notation "here" => (fun i l r x y=>fixed i (cursor i) l r x y)


local notation "branch_" => trace walk
local notation "t" => traces walk
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "rot" => RotorSpec.ofRates reset
local notation "caps" => register_cap_calendar X G S ordinary reset branch positive room shorten b gain
local notation "tags" => traceAt_kinds X G S ordinary reset branch positive room shorten
local notation "one_" => le_max_left 1 (max reset.bitsR (C*reset.bitsR))
local notation "real" => chosenClaim X G S ordinary reset branch positive room shorten w walk
local notation "atGeom" i:arg => Geometry G S b k w i (cursor i)
local notation "ram" i:arg => DateCode.history prog m i


open DescentDatedAddressBook DescentDatedPriorOperand
local notation "dates₀" => RunTrace.machine traces (fun i _=>prog i)
local notation "previous_" => cursor (S.length-1)
local notation "earlier" => DateCode.history dates₀ m S.length
local notation "archive_" => Branch.archive X G S (branch_) positive
local notation "local_" => Branch.localNodes X G S (branch_) positive
local notation "worldShape" => Branch.bundleShape X G S (branch_) positive one_
local notation "space_" => PhysicalReset.ScheduledCodeRoom G S b.board k b.tail (S.length-1) b.p b.f b.gain
  b.drift b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0)
  (previous_).ports.operandLanes (previous_).ports.roleLanes (previous_).ports.venue (previous_).ports.io
  ((previous_).ports.priorStart k (previous_).floor) w ((previous_).ports.afterPad k (previous_).floor).archive
local notation "resetOut" sp:arg => DatePorts.resetPorts G S b.board k b.tail (S.length-1) b.p b.f b.gain
  b.drift b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0)
  (previous_).ports (previous_).floor w sp

local notation "lastJob_" => PhysicalReset.scheduledAtPorts G S b.board k b.tail (S.length-1) b.p b.f b.gain
  b.drift b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0)
  (previous_).ports (previous_).floor
local notation "floor_" => (previous_).ports.priorStart k (previous_).floor
local notation "origin_" => (lastJob_).inner.rebased ((lastJob_).inner.stageStart floor_)
local notation "end_" => (lastJob_).inner.successor.metadataEnd origin_

open DescentSIMDLookup DescentPackedColony ProtocolRAM
open private DatePorts.bankInWindow from OAI.Hierarchy.DescentArchiveReadBetween
private theorem printedAfterMount (ports : DatePorts) (mem : Memory w)
    (printed : FinalPrintedArchive X G S ordinary reset branch positive room shorten w walk ports mem)
    {lo hi : ℕ}
    (fieldWindows : ∀ x j (f : Fin 7), DatePorts.bankInWindow lo hi
      (previousBank ports.rangeLayout ports.archive.arguments x (DescentOperandStateBanks.page f j))
      (ports.operandHosts * chunks ports.venue.groups ports.operandLanes))
    (metaWindows : ∀ x (f : Fin 2), DatePorts.bankInWindow lo hi (DatePorts.metadataPage ports f x)
      (ports.operandHosts * chunks ports.venue.groups ports.operandLanes))
    (roleWindows : ∀ x : Fin (2^ports.venue.k), DatePorts.bankInWindow lo hi (ports.archive.roles.bank x.val)
      (ports.operandHosts * chunks ports.venue.groups ports.roleLanes))
    (capture count : ℕ) (source : ℕ → ℕ) {roleBase replayBase : ℕ} (mount : RoleMount w roleBase replayBase)
    (before : capture + count ≤ lo) (later : hi ≤ roleBase) :
    FinalPrintedArchive X G S ordinary reset branch positive room shorten w walk ports
      (mount.phase.image (DescentLowCountBook.output capture source mem count)) := by
  obtain ⟨layout, flags, records⟩ := printed
  exact ⟨layout, flags, DatePorts.ArchiveRead.after_role_mount _ _ _ _ _ _ _ _ _ _ records fieldWindows metaWindows roleWindows capture count source mount before later⟩

attribute [local irreducible] FinalPrintedArchive terminalArchive
include gain grain arity ready placed in
private theorem mountedAtReset (height : 0 < S.height) (space : space_)
    (printed : FinalPrintedArchive X G S ordinary reset branch positive room shorten w walk (resetOut space) earlier)
    (capture count : ℕ) (source : ℕ → ℕ) {roleBase replayBase : ℕ} (mount : RoleMount w roleBase replayBase)
    (below : capture + count ≤ initial.floor) (beforeRole : (cursor S.length).floor ≤ roleBase) :
    FinalPrintedArchive X G S ordinary reset branch positive room shorten w walk (resetOut space)
      (mount.phase.image (DescentLowCountBook.output capture source earlier count)) := by
  let ticket:=issuedFinalReset X G S ordinary reset branch positive room shorten walk height
  obtain ⟨_, _, endAt, priorWidth, beforeOrigin⟩ := RegisterTimeline.finalResetFloorWidth traces b initial here caps tags ready placed walk ticket
  have banks:=DatePorts.scheduled_archive_windows G S b.board k b.tail (S.length-1) b.p b.f b.gain
    b.drift b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0)
    (previous_).ports (previous_).floor w space priorWidth
  exact printedAfterMount X G S ordinary reset branch positive room shorten w walk (resetOut space) earlier printed banks.1 banks.2.1 banks.2.2 capture count source mount (below.trans beforeOrigin) (endAt.le.trans beforeRole)

include gain grain arity ready placed in
/-- On every attained branch, the selected role encoding and all original address and span
words remain available after both true native writes in the calibrated terminal preflight. -/
theorem final_printed_archive_after_mount (height : 0<S.height)
    (state : terminalArchive X G S ordinary reset branch positive room shorten w walk (cursor S.length) earlier)
    (capture count : ℕ) (source : ℕ→ℕ) {roleBase replayBase : ℕ} (mount : RoleMount w roleBase replayBase)
    (below : capture+count≤ initial.floor) (beforeRole : (cursor S.length).floor≤roleBase) :
    ∃space:space_,(cursor S.length).ports=resetOut space ∧
      FinalPrintedArchive X G S ordinary reset branch positive room shorten w walk (resetOut space)
        (mount.phase.image (DescentLowCountBook.output capture source earlier count)) :=by
  obtain ⟨space, location, printed⟩:=final_printed_register X G S ordinary reset branch positive
    room shorten w b initial gain grain arity ready placed walk m height state
  exact ⟨space, location, mountedAtReset X G S ordinary reset branch positive room shorten w b initial
    gain grain arity ready placed walk m height space printed capture count source mount below beforeRole⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
