import OAI.Hierarchy.DescentNamedProfiledNumbers
import OAI.Hierarchy.DescentNamedProfiledExecution
import OAI.Hierarchy.DescentRegisterOriginalCourse

namespace OAI
/-! # Preservation of the private charge word at each registered reset -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
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
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
set_option cleanup.letToHave false
attribute [local irreducible] normalizedPackedChart SeedNamed.issued Origin.source Origin.archivePackage
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
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

variable (bus : payload≤ w) (site : 0< k) (seedDegree : initial.ports.venue.degree=3)
    (degreeRoom : maximumDegree (S.rounds+1)+1<2^w) (seed : (fun i => RegisterTimeline.Geometry G S (RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).layout) k w i (RegisterTimeline.calendar (w:=w) (traceAt X G S ordinary reset branch positive room shorten) (RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).layout) initial i)) 0)
    (paid : ∀i,∀e:RunTrace.Events (traceAt X G S ordinary reset branch positive room shorten) i,(fun i => RegisterTimeline.Geometry G S (RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).layout) k w i (RegisterTimeline.calendar (w:=w) (traceAt X G S ordinary reset branch positive room shorten) (RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).layout) initial i)) i→(profiledNumbers X G S ordinary reset branch positive room shorten w fit board op frozen drift degree payload lo header initial) i e)

include bus seedDegree degreeRoom seed paid in
theorem profiled_reset_private_step (c:(last).Choice) (m:Memory w) (i:ℕ) (e:(traces c).path.Event i)
    (resetTag:e.isReset=true) (lower:header< initial.floor)
    (placed:∀j (e:RunTrace.Events traces j),fitsAt traces menu initial (w:=w) j e) :
    privateStep traces menu initial c m header i e := by
  dsimp only [SeedNamed.traceAt] at e
  cases e with
  | ordinary before ticket after joined=>cases resetTag
  | reset before B after joined=>
    let x:RunTrace.Events traces i:=⟨c,.reset before B after joined⟩
    have past:=(profiled_installed X G S ordinary reset branch positive room shorten w fit board op frozen drift
      degree payload lo header initial seed placed i x).1
    have ready:=paid i x past
    dsimp only [x, profiledNumbers] at ready
    have execute:=(reset_instruction traces menu initial (fun choice=>(trace choice).kinds) i x rfl past
      ready.1 bus seedDegree degreeRoom ready.2).2
    let execution := execute (DateCode.history program m i)
    let out := Classical.choose execution
    have verified := Classical.choose_spec execution
    have ran := verified.1
    have keep := verified.2.2
    have above:initial.floor≤(cursor i).floor:=by
      change initial.floor ≤ (RegisterTimeline.position (RegisterTimeline.issued (w:=w) traces menu) initial i).floor
      rw [RegisterTimeline.position_floor (RegisterTimeline.issued (w:=w) traces menu) initial i]
      exact DescentDatedAddressBook.floor_mono _ _ (Nat.zero_le i)
    change DateCode.history program m (i+1) header=DateCode.history program m i header
    exact (congrFun (DateCode.nextMemory_eq (program i) ran) header).trans (keep header (.inl (lower.trans_le above)))

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
