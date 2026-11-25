import OAI.Hierarchy.DescentNamedProfiledExecution
import OAI.Hierarchy.DescentNamedProfiledNumbers
import OAI.Hierarchy.DescentRegisteredSnapshotInput
import OAI.Hierarchy.DescentPostedResetRankOperands

namespace OAI
/-! # The issued chronological rank directory for a named branch on its original memory -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline DescentExteriorReplay ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
set_option cleanup.letToHave false
set_option maxRecDepth 12000
attribute [local irreducible] SeedNamed.issued normalizedPackedChart Origin.source Origin.archivePackage
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false in
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
set_option hygiene false in
local notation "run" => (cert).choose
set_option hygiene false in
local notation "last" => Epochs.finish G _ _ run
set_option hygiene false in
local notation "s" => S.firstWidth G.b p
set_option hygiene false in
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
set_option hygiene false in
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
set_option hygiene false in
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

set_option hygiene false in
local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
set_option hygiene false in
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
set_option hygiene false in
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
set_option hygiene false in
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
set_option hygiene false in
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook
variable {n₀ δ : ℕ} (board : NonlinearExpanders.Graph n₀ δ) (op : RotorSpec)
    (frozen drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
set_option hygiene false in
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
set_option hygiene false in
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial
set_option hygiene false in
local notation "model" i:arg a:arg tick:arg =>
  DatePorts.ordinaryModel (a:RegisterTimeline.Position).ports tick op g frozen p f drift degree payload ((menu).seats i) a.floor (menu).ordinary
set_option hygiene false in
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    (S.firstWidth G.b p) (S.grainAt G.b p 0) a.ports a.floor

set_option hygiene false in
local notation "numbers" => profiledNumbers X G S ordinary reset branch positive room shorten w fit
  board op frozen drift degree payload lo header initial
set_option hygiene false in
local notation "data" => fun i=>Geometry G S menu k w i (cursor i)
set_option hygiene false in
local notation "issue" => RegisterTimeline.issued (w:=w) traces menu
set_option hygiene false in
local notation "program" => RegisterTimeline.instruction (w:=w) traces menu initial

set_option hygiene false in
local notation "windows" => profiledExecution X G S ordinary reset branch positive room shorten w fit
  board op frozen drift degree payload lo header initial
variable (bus : payload≤w) (site : 0<k) (seedDegree : initial.ports.venue.degree=3)
    (degreeRoom : maximumDegree (S.rounds+1)+1<2^w) (seed : data 0)
    (paid : ∀i,∀e:RunTrace.Events traces i,data i→numbers i e)
    (accessible : ∀i,∀e:RunTrace.Events traces i,data i→windows i e)


set_option hygiene false in
local notation "dir" => RegisterTimeline.snapshotDirectory (w:=w) traces menu initial
set_option hygiene false in
local notation "snaps" => SnapshotCalendar reset (kindCalendar S.rounds S.height)
    (capCalendar G.b S.rounds g S.height) dir
set_option hygiene false in
local notation "family" => RunTrace.machine traces (fun i _=>program i)

/-- Every numbered snapshot bank in the original branch is above the low count
capture, including snapshots from previous scheduled epochs. -/
theorem profiled_snapshot_away (countBase countRows : ℕ) (countEnd : countBase+countRows≤ initial.floor) :
    ∀i<S.length,∀B,(snaps).compact i=some B→B.base+B.size≤countBase ∨ countBase+countRows≤B.base := by
  intro i _ bank slot
  exact Or.inr (countEnd.trans (snapshotCalendar_above reset traces menu initial i bank slot))

attribute [local irreducible] RegisterTimeline.snapshotDirectory

include bus site seedDegree degreeRoom paid seed accessible in
set_option maxHeartbeats 1000000 in
theorem profiled_snapshot_ranks (head : header< initial.floor) (c : (last).Choice) (m : Memory w)
    (opened : ∀i(e : (traces c).path.Event i), e.isReset=true → ∀mv : Move w,
      issue i ⟨c,e⟩ (cursor i) mv → data i → mv.next.floor<2^w →
      Nonempty (e.ResetRankOperands p mv.code (dir i) mv.next.floor (DateCode.history program m i))) :
    (trace c).path.snapshotRanks snaps (cursor S.length).floor (DateCode.history family m S.length) := by
  have placed:=profiled_placement (F:=F) (cp:=cp) (nP:=nP) (k:=k) (cut:=cut) (tail:=tail) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (n₀:=n₀) (δ:=δ) X G S ordinary reset branch positive room shorten w fit board op frozen drift
    degree payload lo header initial bus site seedDegree degreeRoom
  have common:=all_registered_moves (F:=F) (cp:=cp) (nP:=nP) (k:=k) (cut:=cut) (tail:=tail) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (n₀:=n₀) (δ:=δ) X G S ordinary reset branch positive room shorten w menu rfl rfl rfl
  have protected_:=profiled_instruction (F:=F) (cp:=cp) (nP:=nP) (k:=k) (cut:=cut) (tail:=tail) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (n₀:=n₀) (δ:=δ) X G S ordinary reset branch positive room shorten w fit board op frozen drift
    degree payload lo header initial bus site seedDegree degreeRoom seed paid accessible
  have sameKinds : (traces c).path.kinds = kindCalendar S.rounds S.height := by
    exact (trace c).kinds
  have rows : (traces c).path.snapshotRanks snaps (cursor S.length).floor (DateCode.history family m S.length) := by
    apply registered_snapshot_rows_of_moves reset traces menu initial c m sameKinds protected_ head
      (fun i l r x y=>common i (cursor i) l r x y)
    intro i e tag
    obtain ⟨geom,mv,at_,room_,_⟩:=profiled_installed (F:=F) (cp:=cp) (nP:=nP) (k:=k) (cut:=cut) (tail:=tail) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (n₀:=n₀) (δ:=δ) X G S ordinary reset branch positive room shorten w fit
      board op frozen drift degree payload lo header initial seed (fun a v=>placed a v (paid a v)) i ⟨c,e⟩
    obtain ⟨inputs⟩:=opened i e tag mv at_ geom room_
    exact ⟨mv,at_,inputs.publication (e.resetRecorded_of_whole p ((trace c).recorded))⟩
  exact rows

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
