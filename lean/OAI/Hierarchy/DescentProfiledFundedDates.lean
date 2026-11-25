import OAI.Hierarchy.DescentRegisterOriginalCourse
import OAI.Hierarchy.DescentProfiledOriginalReadbacks
import OAI.Hierarchy.DescentRegisteredReelBounds
import OAI.Hierarchy.DescentFundedDateInputs

namespace OAI
/-! # All word and date observations of the original funded selector capture -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open DescentTerminalEpochDecoder Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

private theorem FundedDateInputs.of_protected_ranges {w : ℕ} (S : AtomSchedule)
    (family program : ℕ → DateCode w) (m : Memory w)
    (header capture roof initialFloor : ℕ) (floors count saved : ℕ → ℕ)
    {observations : Prop} (observed : observations)
    (code : ∀ i < S.length, family i = program i)
    (same : ∀ i ≤ S.length, DateCode.history family m i = DateCode.history program m i)
    (protected_ : ∀ i, RegisterTimeline.Protected (program i) (floors i) header)
    (floorStart : ∀ i, initialFloor ≤ floors i) (below : header < initialFloor)
    (len : (kindCalendar S.rounds S.height).length = S.length)
    (countRange : ∀ i < S.length, initialFloor ≤ count i ∧ ∀ j, i < j → count i < floors j)
    (savedRange : ∀ i < S.length, initialFloor ≤ saved i ∧ ∀ j, i < j → saved i < floors j)
    (startAfter : capture + (countDates 0 (kindCalendar S.rounds S.height)).length ≤ initialFloor)
    (roofAfter : floors S.length ≤ roof) (roofFit : roof < 2^w) :
    FundedDateInputs S family m header capture roof floors count saved observations := by
  refine ⟨?_, ?_, fun i _ => below.trans_le (floorStart i), observed, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi state
    rw [code i hi]
    obtain ⟨out, ran, _⟩ := (protected_ i).run state
    exact ⟨out, ran⟩
  · intro i hi
    rw [code i hi]
    exact (protected_ i).cheap
  · exact fun i hi => (below.trans_le (countRange i hi).1).ne'
  · exact fun i hi => (below.trans_le (savedRange i hi).1).ne'
  · exact fun i hi j _ lt => (countRange i hi).2 j lt
  · exact fun i hi j _ lt => (savedRange i hi).2 j lt
  · intro i hi a apart earlier
    obtain ⟨dst, ran, kept⟩ := (protected_ i).run (DateCode.history program m i)
    rw [same (i+1) hi, same i hi.le]
    exact (congrFun (DateCode.nextMemory_eq (program i) ran) a).trans (kept a earlier apart)
  · intro i member
    have upto := countDates_age_lt member
    rw [len, Nat.zero_add] at upto
    have bound := ((countRange i upto).2 S.length upto).trans_le roofAfter
    exact ⟨startAfter.trans (countRange i upto).1, Nat.lt_of_le_of_lt (Nat.succ_le_of_lt bound) roofFit⟩
  · exact fun i hi => startAfter.trans (savedRange i hi).1
  · exact fun i hi => ((savedRange i hi).2 S.length hi).trans_le roofAfter

end Hierarchy.DescentSixParty.Chronology

namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentKernelHistory Computability.BorderVNP.Crossing Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {d k wire hist len w : ℕ} {bits : P→ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist len bits d)
    {bn bd : ℕ} (b : Menu bn bd) (initial : Position) (c : C) (m : Memory w)
local notation "branch" => traces c
local notation "cpu" => instruction (w:=w) traces b initial
local notation "cursor" => calendar (w:=w) traces b initial
local notation "ram" => DateCode.history cpu m
variable (limit : ℕ) (valid : Prop)

variable (header:ℕ)
variable (fixed:∀i (x y : RunTrace.Events traces i) (a z : Move w),
  issued (w:=w) traces b i x (calendar (w:=w) traces b initial i) a →
  issued (w:=w) traces b i y (calendar (w:=w) traces b initial i) z → a=z)
variable (seed:initial.ports.held (branch).first initial.floor m)
variable (earned:OriginalCourse traces b initial c m limit valid)
variable (meter:∀i (e:(branch).path.Event i),valid→e.incoming (cursor i) (ram i)→
  privateStep traces b initial c m header i e)

include fixed seed earned meter in
omit [Fintype P] in
private theorem original_held_on_machine (zero:m header=0) (live:valid) :
    (branch).path.Held header (DateCode.history (RunTrace.machine traces (fun i _=>instruction (w:=w) traces b initial i)) m len) := by
  have result := original_private_held traces b initial c m limit valid header fixed seed earned meter zero live
  exact (congrArg ((branch).path.Held header) (history_from_cuts traces b initial c m len le_rfl)).mpr result
end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline DescentExteriorReplay ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false
open scoped Fin.CommRing
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000
set_option cleanup.letToHave false
attribute [local irreducible] normalizedPackedChart
attribute [local irreducible] SeedNamed.issued RegisterTimeline.issued
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

open DescentDatedAddressBook
variable {n₀ δ : ℕ} (board : NonlinearExpanders.Graph n₀ δ) (op : RotorSpec)
    (frozen drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial
local notation "model" i:arg a:arg tick:arg =>
  DatePorts.ordinaryModel (a:RegisterTimeline.Position).ports tick op g frozen p f drift degree payload ((menu).seats i) a.floor (menu).ordinary
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    (S.firstWidth G.b p) (S.grainAt G.b p 0) a.ports a.floor

local notation "numbers" => profiledNumbers X G S ordinary reset branch positive room shorten w fit
  board op frozen drift degree payload lo header initial
local notation "data" => fun i=>Geometry G S menu k w i (cursor i)
local notation "issue" => RegisterTimeline.issued (w:=w) traces menu
local notation "program" => RegisterTimeline.instruction (w:=w) traces menu initial

local notation "windows" => profiledExecution X G S ordinary reset branch positive room shorten w fit
  board op frozen drift degree payload lo header initial
variable (bus : payload≤w) (site : 0<k) (seedDegree : initial.ports.venue.degree=3)
    (degreeRoom : maximumDegree (S.rounds+1)+1<2^w) (seed : data 0)
    (paid : ∀i,∀e:RunTrace.Events traces i,data i→numbers i e)
    (accessible : ∀i,∀e:RunTrace.Events traces i,data i→windows i e)



open DescentPackedEpochShelves DescentPackedProfileInstall DescentPackedProfileTape
local notation "family" => RunTrace.machine traces (fun i _=>program i)
local notation "flags" => RegisterTimeline.Menu.resetFlag S
local notation "saved" => fun i=>(menu).rotationAt G S k i (cursor i)
local notation "col" => fun i=>(menu).selectorAt G S k i (cursor i)
local notation "pitch" => DescentPackedEpochShelves.grain (payload/2) G.C
local notation "dates" => countDates 0 (kindCalendar S.rounds S.height)

attribute [local irreducible] Path.dateReadbacks RegisterTimeline.date
  RegisterTimeline.advances RegisterTimeline.capturedWords DateCode.history

include bus site seedDegree degreeRoom seed paid accessible in
/-- The terminal bootstrap consumes the same saved counts and matrices the registered
ordinary and reset instructions wrote. This includes malformed selectors whose first bad
proposal was still reached. -/
theorem profiled_funded_dates (capture roof:ℕ) (beforeHeader:lo+extent pitch (ch).layout≤header)
    (below:header< initial.floor) (startAfter:capture+(dates).length≤ initial.floor)
    (roofAfter:(cursor S.length).floor≤roof) (roofFit:roof<2^w) (votes:(ch).Pin→Bool) (m:Memory w)
    (original:∀a∈shelves pitch lo 0 (ch).layout,∀j:Fin (slots a.src.seats pitch),
      m (a.base+j.val)=((packed a.src.pin votes pitch j.val).val:Word w))
    (c:(last).Choice) (limit:ℕ) (valid:Prop) (scalar:ObservationRoom G S payload w)
    (bootstrap:initial.ports.held (traces c).first initial.floor m)
    (advance:∀i (e:(traces c).path.Event i),RegisterTimeline.advances traces menu initial c m limit valid i e)
    (resetWord:∀i (e:(traces c).path.Event i),e.isReset=true→valid→e.incoming (cursor i) (DateCode.history program m i)→
      RegisterTimeline.capturedWords traces menu initial c m i e) :
    FundedDateInputs S family m header capture roof (fun i=>(cursor i).floor) col saved
      ((traces c).path.dateReadbacks (DateCode.history family m) flags saved col limit valid) := by
  have protected_:=profiled_instruction X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial bus site seedDegree degreeRoom seed paid accessible
  have placed (i:ℕ) (e:RunTrace.Events traces i):fitsAt traces menu initial (w:=w) i e :=
    profiled_placement X G S ordinary reset branch positive room shorten w fit board op frozen drift degree
      payload lo header initial bus site seedDegree degreeRoom i e (paid i e)
  have reported:=profiled_original_readbacks X G S ordinary reset branch positive room shorten w fit board
    op frozen drift degree payload lo header initial protected_ beforeHeader below votes m original c limit valid
    scalar seed (by dsimp only [SeedNamed.traceAt] at bootstrap; exact bootstrap) placed accessible advance resetWord
  have same (i:ℕ) (hi:i≤S.length):DateCode.history family m i=DateCode.history program m i :=
    history_from_cuts traces menu initial c m i hi
  have code (i:ℕ) (hi:i<S.length):family i=program i:=by
    obtain ⟨e⟩:=(traces c).cut_in_prefix (traces c).path .here rfl i hi
    exact RunTrace.on_branch traces (fun j _=>program j) (fun _ _ _=>rfl) c i e
  have cells:=profiled_reel_range X G S ordinary reset branch positive room shorten w menu initial
    rfl rfl rfl seed placed c
  have countRange (i:ℕ) (hi:i<S.length):=cells i hi ((col) i) (Or.inl rfl)
  have savedRange (i:ℕ) (hi:i<S.length):=cells i hi ((saved) i) (Or.inr rfl)
  have floorStart (i:ℕ) : initial.floor ≤ (cursor i).floor :=
    by
      let steps := RegisterTimeline.issued (w:=w) traces menu
      change initial.floor ≤ (RegisterTimeline.position steps initial i).floor
      rw [RegisterTimeline.position_floor steps initial i]
      exact DescentDatedAddressBook.floor_mono initial.floor (RegisterTimeline.span steps initial) (Nat.zero_le i)
  have len : (kindCalendar S.rounds S.height).length=S.length:=by
    calc
      _ = (trace c).path.kinds.length := congrArg List.length (trace c).kinds.symm
      _ = S.length := (Nat.zero_add _).symm.trans (trace c).path.kinds_length
  exact FundedDateInputs.of_protected_ranges S family program m header capture roof initial.floor
    (fun i=>(cursor i).floor) col saved
    ((traces c).path.dateReadbacks_congr flags saved col limit valid same reported)
    code same protected_ floorStart below len countRange savedRange startAfter roofAfter roofFit

include bus site seedDegree degreeRoom seed paid accessible in
theorem profiled_funded_course (capture roof:ℕ) (beforeHeader:lo+extent pitch (ch).layout≤header)
    (below:header< initial.floor) (startAfter:capture+(dates).length≤ initial.floor)
    (roofAfter:(cursor S.length).floor≤roof) (roofFit:roof<2^w) (votes:(ch).Pin→Bool) (m:Memory w)
    (original:∀a∈shelves pitch lo 0 (ch).layout,∀j:Fin (slots a.src.seats pitch),
      m (a.base+j.val)=((packed a.src.pin votes pitch j.val).val:Word w))
    (c:(last).Choice) (limit:ℕ) (valid:Prop) (scalar:ObservationRoom G S payload w)
    (bootstrap:initial.ports.held (traces c).first initial.floor m)
    (course : OriginalCourse traces menu initial c m limit valid)
    (meter : ∀i (e:(traces c).path.Event i),valid→e.incoming (cursor i) (DateCode.history program m i)→
      privateStep traces menu initial c m header i e) (zero:m header=0) :
    FundedDateInputs S family m header capture roof (fun i=>(cursor i).floor) col saved
      ((traces c).path.dateReadbacks (DateCode.history family m) flags saved col limit valid) ∧
    (valid→(traces c).path.Held header (DateCode.history family m S.length)) := by
  refine ⟨profiled_funded_dates X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial bus site seedDegree degreeRoom seed paid accessible
    capture roof beforeHeader below startAfter roofAfter roofFit votes m original c limit valid scalar
    bootstrap course.advance course.resetWords,?_⟩
  intro alive
  exact RegisterTimeline.original_held_on_machine traces menu initial c m limit valid header
    (fun i x y a b=>all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl
      i (cursor i) x y a b) bootstrap course meter zero alive

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
