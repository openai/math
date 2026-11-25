import OAI.Hierarchy.DescentNamedProfiledAdmission
import OAI.Hierarchy.DescentRegisteredOrdinaryProtection

namespace OAI
/-! # Native all-input execution of the fixed date program on the original ballot chart -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentPacking.PackedMatch.Local.Stage
open DescentCompiler Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P → ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C → RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)
set_option quotPrecheck false
local notation "current" i:arg => calendar (w:=w) traces b initial i
local notation "outer" i:arg => PhysicalReset.scheduledAtPorts G S b.board k b.tail i b.p b.f b.gain b.drift
  b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0)
  (current i).ports (current i).floor

private def eventExecution (i : ℕ) (evt : RunTrace.Events traces i) : Prop :=
  let a := current i
  match evt with
  | ⟨_,.ordinary _ ticket _ _⟩ =>
    ∀ r : DatePorts.OrdinaryCodeRoom a.ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit b.payload
          (b.seats i) a.floor b.ordinary w,
      DatePorts.OrdinaryExecutionRoom a.ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit b.payload
          (b.seats i) a.floor b.ordinary w (b.profile i) b.header r
  | ⟨_,.reset _ _ _ _⟩ => True

omit [Fintype P] in
private theorem protected_event (i : ℕ) (evt : RunTrace.Events traces i) (move : Move w)
    (posted : issued traces b i evt (current i) move)
    (agree : ∀ m, issued traces b i evt (current i) m → m = move)
    (kinds : ∀ c, (traces c).path.kinds=kindCalendar S.rounds S.height)
    (geom : Geometry G S b k w i (current i)) (bus : b.payload ≤ w)
    (degreeBound : (current i).ports.venue.degree+1<2^w)
    (ordinaryRoom : eventExecution (w:=w) traces b initial i evt)
    (resetRoom : evt.2.isReset = true →
      8*b.receiverWidth G S k i (current i).ports ≤ b.payload ∧ (outer i).fullEnd < 2^w) :
    Protected move.code (current i).floor b.header := by
  rcases evt with ⟨c,e⟩
  cases e with
  | ordinary before ticket after joined =>
    obtain ⟨pos, code, rfl⟩ := posted
    exact DatePorts.ordinary_protected (current i).ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit
      b.payload (b.seats i) (current i).floor b.ordinary w (b.profile i) b.header pos code (ordinaryRoom code)
  | reset before ctl after joined =>
    let event : RunTrace.Events traces i := ⟨c,.reset before ctl after joined⟩
    obtain ⟨small, limit⟩ := resetRoom rfl
    obtain ⟨m,step,_,runs⟩ := reset_issued_any traces b initial kinds i event rfl geom small bus degreeBound limit
    obtain rfl := agree m step
    constructor
    · intro src
      obtain ⟨dst,run,_,keep⟩ := runs src
      exact ⟨dst,run,fun z lt _ => keep z (.inl lt)⟩
    · exact (runs (fun _ => 0)).choose_spec.2.1

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
set_option cleanup.letToHave false
set_option maxRecDepth 12000
attribute [local irreducible] normalizedPackedChart Origin.source Origin.archivePackage
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
  DatePorts.ordinaryModel (a:RegisterTimeline.Position).ports tick op g frozen p f drift degree payload ((menu).seats i) (a:RegisterTimeline.Position).floor (menu).ordinary
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

/-- All inputs of these structural conditions are public register addresses and bit counts. -/
def profiledExecution (i : ℕ) (evt : RunTrace.Events traces i) : Prop :=
  RegisterTimeline.eventExecution (w:=w) traces menu initial i evt

set_option hygiene false in
local notation "windows" => profiledExecution X G S ordinary reset branch positive room shorten w fit
  board op frozen drift degree payload lo header initial
variable (bus : payload≤w) (site : 0<k) (seedDegree : initial.ports.venue.degree=3)
    (degreeRoom : maximumDegree (S.rounds+1)+1<2^w) (seed : data 0)
    (paid : ∀i,∀e:RunTrace.Events traces i,data i→numbers i e)
    (accessible : ∀i,∀e:RunTrace.Events traces i,data i→windows i e)

private theorem chosenCaps (c : (last).Choice) :
    (traces c).path.capFactors = capCalendar G.b S.rounds g S.height := by
  dsimp only [traceAt]
  exact (SeedNamed.issued X G S ordinary reset branch positive room shorten c).calendar

attribute [local irreducible] SeedNamed.issued traceAt

include bus site seedDegree degreeRoom paid in
private theorem admitted (i : ℕ) (e : RunTrace.Events traces i) :
    fitsAt traces menu initial (w:=w) i e :=
  profiled_placement (F:=F) (cp:=cp) (nP:=nP) (k:=k) (cut:=cut) (tail:=tail)
    (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (n₀:=n₀) (δ:=δ)
    X G S ordinary reset branch positive room shorten w fit board op frozen drift degree
    payload lo header initial bus site seedDegree degreeRoom i e (paid i e)

open private chosenKind from OAI.Hierarchy.DescentNamedProfiledAdmission

private theorem resetSizes (i : ℕ) (evt : RunTrace.Events traces i) (paidHere : numbers i evt)
    (isReset : evt.2.isReset=true) :
    8*(menu).receiverWidth G S k i (cursor i).ports ≤ payload ∧ (resetAt i (cursor i)).fullEnd<2^w := by
  rcases evt with ⟨c,e⟩
  cases e with
  | ordinary before ticket after joined => cases isReset
  | reset before ctl after joined => exact paidHere

include bus site seedDegree degreeRoom paid seed accessible in
theorem profiled_issue_run (i : ℕ) (evt : RunTrace.Events traces i) (move : RegisterTimeline.Move w)
    (issued_ : issue i evt (cursor i) move) : RegisterTimeline.Protected move.code (cursor i).floor header := by
  let common:=all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl
  let placed:=admitted X G S ordinary reset branch positive room shorten w fit board op frozen drift degree
    payload lo header initial bus site seedDegree degreeRoom paid
  have kinds:=chosenKind X G S ordinary reset branch positive room shorten
  have caps:=chosenCaps X G S ordinary reset branch positive room shorten
  have geom:=RegisterTimeline.geometry_on_event traces menu initial (fun j a b x y=>common j (cursor j) a b x y)
    caps kinds seed placed evt.1 i evt.2
  exact RegisterTimeline.protected_event traces menu initial i evt move issued_
    (fun m h => common i (cursor i) evt evt m move h issued_) kinds geom bus
    (RegisterTimeline.calendar_degree_room traces menu kinds initial seedDegree degreeRoom i)
    (accessible i evt geom)
    (resetSizes X G S ordinary reset branch positive room shorten w fit board op frozen drift degree payload
      lo header initial i evt (paid i evt geom))

include bus site seedDegree degreeRoom paid seed accessible in
theorem profiled_instruction (i : ℕ) : RegisterTimeline.Protected (program i) (cursor i).floor header :=
  RegisterTimeline.instruction_run issue initial header
    (profiled_issue_run X G S ordinary reset branch positive room shorten w fit board op frozen drift degree
      payload lo header initial bus site seedDegree degreeRoom seed paid accessible) i

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
