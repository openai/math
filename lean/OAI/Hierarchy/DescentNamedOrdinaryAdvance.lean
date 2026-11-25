import OAI.Hierarchy.DescentNamedOrdinaryOutput
import OAI.Hierarchy.DescentRegisteredOrdinaryAdvance
import OAI.Hierarchy.DescentRegisteredGeometry
import OAI.Hierarchy.DescentNamedAllRegisterMoves

namespace OAI
/-! # Every actual named prefix has its counted state, public memory and next-date geometry -/
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
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000
set_option Elab.async false
set_option cleanup.letToHave false
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
variable {n₀ δ : ℕ} (b : RegisterTimeline.Menu n₀ δ) (initial : RegisterTimeline.Position)
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces b initial
local notation "issue" => RegisterTimeline.issued (w:=w) traces b
local notation "prog" => RegisterTimeline.instruction (w:=w) traces b initial


variable (gain : b.gain=g) (grain : b.p=p) (arity : b.f=f)

variable (z : (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).Pin → Bool)
    (walk : (Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice) (m : Memory w)
local notation "limit" => ((ch).rows z).length
local notation "valid" => (ch).read z=some walk
variable {U : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width))) (fun _ => S.firstWidth G.b p*1)} {i z₀ D z' D' : ℕ} {rate:ℝ}
    {r : Reached U G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower) S k i z₀ D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    {nonneg:0≤(((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)} {T:StageInput U G rate (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)} {c:(T.result nonneg).Choice}
    {n:Normalize ((T.result nonneg).state c)}
    {dst:Reached n.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (before:Path (traceAt X G S ordinary reset branch positive room shorten walk).first r) (ticket:OrdinaryLink r nonneg T c n dst)
    (after:Path dst (traceAt X G S ordinary reset branch positive room shorten walk).last) (join:(before.ordinary ticket).append after=(traceAt X G S ordinary reset branch positive room shorten walk).path)
local notation "here" => cursor i
local notation "prior₁" => (here).ports
local notation "root₁" => (here).floor
local notation "ram₁" => DateCode.history prog m i
local notation:max "make" f₁:arg => f₁ prior₁ ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit b.payload
  (b.seats i) root₁ b.ordinary

attribute [local irreducible] SeedNamed.issued Origin.source normalizedPackedChart

include gain grain arity in
/-- A successful ordinary transition, or the observed ordinary prefix before
a later rejected ballot, advances the actual public register calendar. -/
theorem ordinary_positive_advance (geo:Geometry G S b k w i here)
    (hk:0<k) (room₁:(make DatePorts.OrdinaryCodeRoom) w)
    (exec:(make DatePorts.OrdinaryExecutionRoom) w (b.profile i) b.header room₁)
    (selected:(prior₁).held r root₁ ram₁ → (before.selections.length+1<limit ∨ valid) →
      (make DatePorts.returnedVenue) w (b.profile i) b.header hk room₁ exec ram₁) :
    RegisterTimeline.advances traces b initial walk m limit valid i (Path.Event.ordinary before ticket after join):=by
  refine RegisterTimeline.ordinary_advances
    (traceAt X G S ordinary reset branch positive room shorten) b initial walk m _ _
    before ticket after join hk room₁ exec ?_
  intro old accepted
  have returned := selected old accepted
  subst g
  subst f
  subst p
  exact Branch.held_from_venue X G S (SeedNamed.issued X G S ordinary reset branch positive room shorten walk)
    ticket before after join b.op b.tail b.drift b.degreeLimit b.payload (b.seats i) _ _ b.ordinary
    w (b.profile i) b.header hk room₁ exec _ old geo.room.population geo.room.initialSites
    geo.format.width geo.capacity geo.room.wires geo.room.header returned

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
