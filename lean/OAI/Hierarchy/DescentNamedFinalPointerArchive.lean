import OAI.Hierarchy.DescentOriginalTaggedArchiveFinal
import OAI.Hierarchy.DescentIssuedLastReset

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

omit [Fintype P] in
private theorem finalResetPortsOfEvent
    (fixed : ∀ i (e f : RunTrace.Events traces i) x y,
      issued (w:=w) traces b i e (cursor i) x → issued (w:=w) traces b i f (cursor i) y → x=y)
    (caps : ∀ c,(traces c).path.capFactors=capCalendar G.b S.rounds b.gain S.height)
    (tags : ∀ c,(traces c).path.kinds=kindCalendar S.rounds S.height)
    (ready : Geometry G S b k w 0 initial)
    (placed : ∀ i (e : RunTrace.Events traces i), fitsAt traces b initial (w:=w) i e)
    (c : C) {p : ℕ} (ticket : Path.FinalReset p (traces c).path) :
    ∃ space : lastSpace,(cursor S.length).ports=outputPorts space := by
  have geo:=geometry_on_event traces b initial fixed caps tags ready placed c (S.length-1) ticket.event
  obtain ⟨move,located,_,_⟩:=placed (S.length-1) ⟨c,ticket.event⟩ geo
  obtain ⟨_,space,_,_,next⟩:=final_move traces b initial c ticket fixed ⟨move,located⟩
  exact ⟨space,congrArg Position.ports next⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

/-! # Authentic field archive at the scheduled final reset -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline DescentLocalArchiveOrder DescentPrimitivePalette DescentKernelHistory
open DescentBundleHistory DescentOperandStateBanks Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
set_option quotPrecheck false
open private chosenClaim chosenWhole chosenAligned chosenOnly from OAI.Hierarchy.DescentNamedArchivePrefix
attribute [local irreducible] Origin.source Origin.archivePackage issued
open private branchClaim branchTrace claimOnPath from OAI.Hierarchy.DescentNamedArchivePrefix
open private Palette.encodedOrigin from OAI.Hierarchy.DescentNamedPrimitivePalette
attribute [local irreducible] Palette.encodedOrigin
variable {F : Type} [Field F]
section
variable {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
local notation "wire₀" => S.epochPower^S.priceExponent
local notation "s₀" => S.firstWidth G.b p
local notation "q₀" => (1/((s₀:ℝ)*(wire₀:ℝ)):ℝ)
local notation "ε₀" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)
variable (stride : 1 ≤ R) (op : RotorSpec) (menu : Runnable F op) (w : ℕ)
local notation "bArchive" => Branch.archive X G S b hp
local notation "bOrder" => Branch.localNodes X G S b hp
local notation "bShape" => Branch.bundleShape X G S b hp stride
private theorem branchPrintedOfClaim (pos : RegisterTimeline.Position) (mem : Memory w)
    (chosen : b.path.OnlyRotor op)
    (claimAt : branchClaim X G S b hp stride op menu w b.path pos mem) :
    ∃(layout : DatePorts.RangeRoom pos.ports b.target (bArchive).bit)
      (flags : Fin (2^pos.ports.venue.k) → Fin pos.ports.nodes → Fin pos.ports.operandHosts → Fin pos.ports.venue.groups → ℕ),
      DatePorts.ArchiveRead pos.ports b.target (bArchive).bit bOrder layout bShape op
        (encodePath op menu b.path hp (b.path.recorded_whole p b.recorded) chosen
          b.origin.archive (Palette.encodedOrigin (p:=p) b.origin op menu)).atNode
        (Reached.argumentPointer b.target (bArchive).bit bOrder bShape hp
          (fun y : Σ _ : Fin S.copies, Fin (Fintype.card (Port nP X.width)) => y.1.val) pos.ports.argumentsPerNode) flags mem := by
  dsimp only [branchClaim, branchTrace, claimOnPath, archiveClaim] at claimAt
  obtain ⟨layout, stored⟩ := claimAt (b.path.recorded_whole p b.recorded) b.aligned chosen
  dsimp only [Branch.archive, Branch.localNodes, Branch.bundleShape]
  exact ⟨layout, archiveFlag b.target (bArchive).bit bOrder pos.ports layout, stored⟩

end
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

/-- The physical archive, at its original width, with the actual branch's local numbering and shape. -/
def FinalPointerArchive (ports : DatePorts) (memory : Memory w) : Prop :=
  ∃(layout : DatePorts.RangeRoom ports (branch_).target (archive_).bit)
    (label : NodeOrder.All (archive_).bit→Label G s (S.grainAt G.b p 0) rot)
    (flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ),
    DatePorts.ArchiveRead ports (branch_).target (archive_).bit local_ layout worldShape rot label
      (Reached.argumentPointer (branch_).target (archive_).bit local_ worldShape positive
        (fun y : pins=>y.1.val) ports.argumentsPerNode) flags memory

/-- The role word is the attained palette encoding for this branch's actual node. -/
def FinalPrintedArchive (ports : DatePorts) (memory : Memory w) : Prop :=
  ∃(layout : DatePorts.RangeRoom ports (branch_).target (archive_).bit)
    (flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ),
    DatePorts.ArchiveRead ports (branch_).target (archive_).bit local_ layout worldShape rot
      (by delta SeedNamed.issued; exact (Palette.atLeaf X G S ordinary reset branch positive room shorten walk).atNode)
      (Reached.argumentPointer (branch_).target (archive_).bit local_ worldShape positive
        (fun y : pins=>y.1.val) ports.argumentsPerNode) flags memory

private theorem issuedLeafLabels (whole : (branch_).path.whole p)
    (rotors : (branch_).path.OnlyRotor rot) :
    (encodePath rot reset.menu (branch_).path positive whole rotors
      (branch_).origin.archive (Palette.encodedOrigin (p:=p) (branch_).origin rot reset.menu)).atNode
    = (by delta SeedNamed.issued
          exact (Palette.atLeaf X G S ordinary reset branch positive room shorten walk).atNode) := by
  delta SeedNamed.issued
  rfl

set_option maxHeartbeats 1400000 in
private theorem printedOfState (pos : RegisterTimeline.Position) (mem : Memory w)
    (state : terminalArchive X G S ordinary reset branch positive room shorten w walk pos mem) :
    FinalPrintedArchive X G S ordinary reset branch positive room shorten w walk pos.ports mem := by
  have saved := branchPrintedOfClaim X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p)
    (r:=(cert).choose) (c:=walk) (trace walk) positive one_ rot reset.menu w pos mem
    (chosenOnly X G S ordinary reset branch positive room shorten walk) state.1
  let holds (label : NodeOrder.All (archive_).bit → Label G s (S.grainAt G.b p 0) rot) : Prop :=
    ∃ (layout : DatePorts.RangeRoom pos.ports (branch_).target (archive_).bit)
      (flags : Fin (2^pos.ports.venue.k) → Fin pos.ports.nodes → Fin pos.ports.operandHosts → Fin pos.ports.venue.groups → ℕ),
      DatePorts.ArchiveRead pos.ports (branch_).target (archive_).bit local_ layout worldShape rot label
        (Reached.argumentPointer (branch_).target (archive_).bit local_ worldShape positive
          (fun y : pins => y.1.val) pos.ports.argumentsPerNode) flags mem
  have labelEq := issuedLeafLabels X G S ordinary reset branch positive room shorten walk
    ((branch_).path.recorded_whole p (branch_).recorded) (chosenOnly X G S ordinary reset branch positive room shorten walk)
  exact (congrArg holds labelEq).mp saved

private theorem pointerOfPrinted (ports : DatePorts) (mem : Memory w)
    (printed : FinalPrintedArchive X G S ordinary reset branch positive room shorten w walk ports mem) :
    FinalPointerArchive X G S ordinary reset branch positive room shorten w walk ports mem := by
  obtain ⟨layout, flags, stored⟩ := printed
  exact ⟨layout, _, flags, stored⟩

attribute [local irreducible] FinalPrintedArchive terminalArchive

include gain grain arity ready placed in
/-- Resolve the concrete last reset before eliminating the original chronological archive claim. -/
theorem final_printed_register (height : 0<S.height)
    (state : terminalArchive X G S ordinary reset branch positive room shorten w walk (cursor S.length) earlier) :
    ∃space : space_,(cursor S.length).ports=resetOut space ∧
      FinalPrintedArchive X G S ordinary reset branch positive room shorten w walk (resetOut space) earlier :=by
  let ticket:=issuedFinalReset X G S ordinary reset branch positive room shorten walk height
  obtain ⟨space, loc⟩ := RegisterTimeline.finalResetPortsOfEvent traces b initial here caps tags ready placed walk ticket
  have current := printedOfState X G S ordinary reset branch positive room shorten w walk (cursor S.length) earlier state
  exact ⟨space,loc,loc ▸ current⟩

include gain grain arity ready placed in
/-- Resolve the concrete last reset before eliminating the original chronological archive claim. -/
theorem final_pointer_register (height : 0<S.height)
    (state : terminalArchive X G S ordinary reset branch positive room shorten w walk (cursor S.length) earlier) :
    ∃space : space_,(cursor S.length).ports=resetOut space ∧
      FinalPointerArchive X G S ordinary reset branch positive room shorten w walk (resetOut space) earlier :=by
  obtain ⟨space, loc, printed⟩ := final_printed_register X G S ordinary reset branch positive room shorten
    w b initial gain grain arity ready placed walk m height state
  exact ⟨space, loc, pointerOfPrinted X G S ordinary reset branch positive room shorten w walk (resetOut space) earlier printed⟩

include gain grain arity ready placed in
/-- The original seed and the posted per-event field returns give the four real terminal
pointer pages, their spans, and the node metadata on the same registered final memory. -/
theorem final_pointer_archive (height : 0<S.height)
    (bootstrap : initial.ports.held (t).first initial.floor m ∧
      real Path.here initial m ∧ initial.ports.ArchiveTags m)
    (venue : ∀i (e : (t).path.Event i),atGeom i → advances traces b initial walk m limit valid i e)
    (acquire : ∀i (e : (t).path.Event i),atGeom i → e.incoming (cursor i) (ram i) →
      e.previousClaim real (cursor i) (ram i) → (cursor i).ports.ArchiveTags (ram i) → e.required limit valid →
      e.nextClaim real (cursor (i+1)) (ram (i+1)) ∧ TagInputs traces b initial walk m i e)
    (accepted : valid) :
    ∃space : space_,(cursor S.length).ports=resetOut space ∧
      FinalPointerArchive X G S ordinary reset branch positive room shorten w walk (resetOut space) earlier :=by
  have stored:=terminal_archive_from_dates X G S ordinary reset branch positive room shorten w fit b initial
    gain grain arity ready placed z walk m bootstrap venue acquire accepted
  exact final_pointer_register X G S ordinary reset branch positive room shorten w b initial
    gain grain arity ready placed walk m height stored

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
