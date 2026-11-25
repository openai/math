import OAI.Hierarchy.DescentNamedIssuedSnapshotRanks
import OAI.Hierarchy.DescentRegisterOriginalCourse
import OAI.Hierarchy.DescentNamedPrefixState
import OAI.Hierarchy.DescentProfiledResetRankOperand

namespace OAI
/-! # Final reset ranks on the true accepted profiled instruction history -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
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
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
set_option cleanup.letToHave false
attribute [local irreducible] normalizedPackedChart SeedNamed.issued Origin.source Origin.archivePackage
local notation "cert" => SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : s < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook
local notation "board" => reset.board
local notation "op" => RotorSpec.ofRates reset
local notation "frozen" => tail
variable (drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial
local notation "model" i:arg a:arg tick:arg =>
  DatePorts.ordinaryModel (a:RegisterTimeline.Position).ports tick op g frozen p f drift degree payload ((menu).seats i) a.floor (menu).ordinary
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    (S.firstWidth G.b p) (S.grainAt G.b p 0) (a).ports (a).floor

local notation "numbers" => profiledNumbers X G S ordinary reset branch positive room shorten w fit
  board op frozen drift degree payload lo header initial
local notation:max "data" j:arg => Geometry G S menu k w j (cursor j)
local notation "issue" => RegisterTimeline.issued (w:=w) traces menu
local notation "program" => RegisterTimeline.instruction (w:=w) traces menu initial

local notation "windows" => profiledExecution X G S ordinary reset branch positive room shorten w fit
  board op frozen drift degree payload lo header initial
variable (bus : payload≤w) (site : 0<k) (seedDegree : initial.ports.venue.degree=3)
    (degreeRoom : maximumDegree (S.rounds+1)+1<2^w) (seed : data 0)
    (paid : ∀i,∀e:RunTrace.Events traces i,data i→numbers i e)
    (accessible : ∀i,∀e:RunTrace.Events traces i,data i→windows i e)


local notation "dir" => RegisterTimeline.snapshotDirectory (w:=w) traces menu initial
local notation "snaps" => SnapshotCalendar reset (kindCalendar S.rounds S.height)
    (capCalendar G.b S.rounds g S.height) dir
local notation "family" => RunTrace.machine traces (fun i _=>program i)

variable (bits₀ : (ch).Pin→Bool) (walk : (last).Choice) (m : Memory w)
local notation "limit" => ((ch).rows bits₀).length
local notation "valid" => (ch).read bits₀=some walk
variable (selected : valid)
  (boot : initial.ports.held (trace walk).origin.source initial.floor m)
  (advances_ : ∀i (e : (traces walk).path.Event i),data i →
    RegisterTimeline.advances traces menu initial walk m limit valid i e)

include bus site seedDegree degreeRoom paid seed accessible selected boot advances_ in
/-- Each reset's word is the new dense rank of this actor in the chosen original
path. The induction visits precisely the dated instructions of the accepted ballot. -/
theorem profiled_earned_snapshot_ranks (head : header< initial.floor)
    (capacity : SnapshotWordRoom S n h k tail p f g payload w) :
    (trace walk).path.snapshotRanks snaps (cursor S.length).floor (DateCode.history family m S.length) := by
  have placed₀:=profiled_placement X G S ordinary reset branch positive room shorten w fit board op frozen drift
    degree payload lo header initial bus site seedDegree degreeRoom
  have placed : ∀i(e:RunTrace.Events traces i), RegisterTimeline.fitsAt traces menu initial (w:=w) i e :=
    fun i e=>placed₀ i e (paid i e)
  have protected_:=profiled_instruction X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial bus site seedDegree degreeRoom seed paid accessible
  have sameKinds : (traces walk).path.kinds=kindCalendar S.rounds S.height := (trace walk).kinds
  have earned : (traces walk).path.snapshotRanks snaps (cursor S.length).floor (DateCode.history family m S.length) := by
    apply registered_snapshot_ranks reset traces menu initial walk m sameKinds protected_ head
    intro i e tag
    cases e with
    | ordinary => cases tag
    | reset before B after_ joined =>
      let rest:=(Path.here.reset B).append after_
      have cut₀ : before.append rest=(traces walk).path :=
        (Path.append_cut_assoc before (Path.here.reset B) after_).symm.trans joined
      obtain ⟨_,previous,_⟩:=original_prefix_state X G S ordinary reset branch positive room shorten w fit menu
        initial rfl rfl rfl seed placed bits₀ walk m boot advances_ before rest cut₀ (Or.inr selected)
      rw [←RegisterTimeline.position_floor issue initial i] at previous
      let event : (traces walk).path.Event i:=.reset before B after_ joined
      have arrived : Path.Event.incoming (t:=traces walk) event (cursor i) (DateCode.history program m i):=previous
      have native := profiled_reset_rank_operand X G S ordinary reset branch positive room shorten w fit
        drift degree payload lo header initial bus seedDegree degreeRoom walk m before B after_ joined
        seed placed arrived capacity
      obtain ⟨issuedOperands⟩:=native
      exact issuedOperands.publication (event.resetRecorded_of_whole p (trace walk).recorded)
  exact earned

include bus site seedDegree degreeRoom paid seed accessible selected boot in
/-- The same course that produces the dated rotation and population readbacks
also supplies every preceding registered input for the rank directory. -/
theorem profiled_course_snapshot_ranks
    (course : RegisterTimeline.OriginalCourse traces menu initial walk m limit valid)
    (head : header< initial.floor) (capacity : SnapshotWordRoom S n h k tail p f g payload w) :
    (trace walk).path.snapshotRanks snaps (cursor S.length).floor (DateCode.history family m S.length) :=
  profiled_earned_snapshot_ranks X G S ordinary reset branch positive room shorten w fit drift degree
    payload lo header initial bus site seedDegree degreeRoom seed paid accessible bits₀ walk m selected boot
    (fun i e _=>course.advance i e) head capacity

include bus site seedDegree degreeRoom paid seed accessible selected boot in
/-- Capturing the original ordinary-date counts preserves precisely the compact
reset banks. The replay base may be strictly above the final calendar floor. -/
theorem profiled_captured_course_ranks
    (course : RegisterTimeline.OriginalCourse traces menu initial walk m limit valid)
    (head : header< initial.floor) (words : SnapshotWordRoom S n h k tail p f g payload w)
    (countBase countRows replayBase : ℕ) (source : ℕ→ℕ)
    (before : countBase+countRows≤ initial.floor) (after_ : (cursor S.length).floor≤replayBase) :
    (trace walk).path.snapshotRanks snaps replayBase
      (DescentLowCountBook.output countBase source (DateCode.history family m S.length) countRows) :=by
  apply (trace walk).path.snapshotRanks_count_capture snaps source
    (profiled_course_snapshot_ranks X G S ordinary reset branch positive room shorten w fit drift degree
      payload lo header initial bus site seedDegree degreeRoom seed paid accessible bits₀ walk m selected boot
      course head words) after_
  intro i _ bank found
  exact Or.inr (before.trans (snapshotCalendar_above reset traces menu initial i bank found))

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
