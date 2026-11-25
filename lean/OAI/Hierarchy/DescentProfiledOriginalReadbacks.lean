import OAI.Hierarchy.DescentProfiledOrdinaryObservations
import OAI.Hierarchy.DescentProfiledObservationScalars
import OAI.Hierarchy.DescentRegisterObservedPath
import OAI.Hierarchy.DescentNamedProfiledNumbers
import OAI.Hierarchy.DescentNamedProfiledExecution

namespace OAI
/-! # Reading back the actual recorded selector counts and rotations on the common processor -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
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
set_option maxHeartbeats 1500000
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

open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall
local notation "pitch" => DescentPackedEpochShelves.grain (payload/2) G.C
local notation "issue" => RegisterTimeline.issued (w:=w) traces menu
local notation "cpu" => RegisterTimeline.instruction (w:=w) traces menu initial


open DescentCompiler.TerminalScale DescentGroupPeerOrder DescentStageEdgeReceipt
open DescentColonies DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup
local notation "pos₀" => cursor
local notation "v₂" i:arg tick:arg => DatePorts.ordinaryModel (cursor i).ports tick op g frozen p f drift degree
  payload ((menu).seats i) (cursor i).floor (menu).ordinary
local notation "liveCPU" => DateCode.history cpu
local notation "load₂" i:arg tick:arg => (v₂ i tick).archivePhase (cursor i).floor ((menu).profile i) w


local notation "windows" => profiledExecution X G S ordinary reset branch positive room shorten w fit
  board op frozen drift degree payload lo header initial
local notation "data" => fun i=>RegisterTimeline.Geometry G S menu k w i (cursor i)
local notation "tag" => RegisterTimeline.Menu.resetFlag S
local notation "rot" => fun i=>(menu).rotationAt G S k i (cursor i)
local notation "sel" => fun i=>(menu).selectorAt G S k i (cursor i)

attribute [local irreducible] Path.dateReadbacks RegisterTimeline.position RegisterTimeline.date
  RegisterTimeline.advances RegisterTimeline.capturedWords DateCode.history RegisterTimeline.issued

theorem profiled_original_readbacks (protected_ : ∀j,RegisterTimeline.Protected (cpu j) (cursor j).floor header)
    (beforeHeader : lo+extent pitch (ch).layout≤ header) (lower : header< initial.floor)
    (votes : (ch).Pin→Bool) (m : Memory w)
    (original : ∀a∈shelves pitch lo 0 (ch).layout,∀j:Fin (slots a.src.seats pitch),
      m (a.base+j.val)=((packed a.src.pin votes pitch j.val).val:Word w))
    (c:(last).Choice) (limit:ℕ) (valid:Prop) (scalar:ObservationRoom G S payload w)
    (seed:data 0) (bootstrap:initial.ports.held (trace c).origin.source initial.floor m)
    (placed:∀i (e:RunTrace.Events traces i),RegisterTimeline.fitsAt traces menu initial (w:=w) i e)
    (hardware:∀i (e:RunTrace.Events traces i),data i→windows i e)
    (advance:∀i (e:(traces c).path.Event i),RegisterTimeline.advances traces menu initial c m limit valid i e)
    (resetWord:∀i (e:(traces c).path.Event i),e.isReset=true → valid → e.incoming (cursor i) (DateCode.history cpu m i) →
        RegisterTimeline.capturedWords traces menu initial c m i e) :
    (traces c).path.dateReadbacks (DateCode.history cpu m) tag rot sel limit valid:=by
  refine RegisterTimeline.observed_path traces menu initial c m limit valid
    (fun i x y a b=>all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl
      i (cursor i) x y a b) bootstrap advance ?_
  intro i e accepted incoming
  dsimp only [SeedNamed.traceAt] at e
  cases e with
  | ordinary before ticket after cut =>
    let originalEvent : RunTrace.Events traces i := ⟨c, .ordinary before ticket after cut⟩
    let installed := profiled_installed X G S ordinary reset branch positive room shorten w fit
      board op frozen drift degree payload lo header initial seed placed i originalEvent
    let mv := Classical.choose installed.2
    have provision := Classical.choose_spec installed.2
    have issuedHere := provision.1
    have before_ : (cursor i).floor < 2^w :=
      (RegisterTimeline.forward traces menu i originalEvent (cursor i) mv issuedHere).trans_lt provision.2.1
    dsimp only [originalEvent] at issuedHere
    unfold RegisterTimeline.issued at issuedHere
    let hk := Classical.choose issuedHere
    let code := Classical.choose issuedHere.choose_spec
    have ok := hardware i originalEvent installed.1
    have live : i < S.length := by
      have date := after.kinds_length
      omega
    unfold RegisterTimeline.capturedWords
    exact profiled_ordinary_observations X G S ordinary reset branch positive room shorten w fit board op
      frozen drift degree payload lo header initial protected_ beforeHeader lower votes m original c ticket
      before after cut code (ok code) installed.1 incoming scalar.height live before_
      (scalar.key i live.le) (scalar.count i live.le) scalar.grain hk
  | reset before B after joined=>exact resetWord i (.reset before B after joined) rfl (accepted rfl) incoming

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
