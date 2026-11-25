import OAI.Hierarchy.DescentOriginalTaggedArchivePrefix
import OAI.Hierarchy.DescentRegisteredFinalEvent
import OAI.Hierarchy.DescentRegisterOriginalCourse

namespace OAI
/-! # The complete tagged archive on the true last instruction image -/
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
local notation "fixed" => all_registered_moves X G S ordinary reset branch positive room shorten w b gain grain arity
variable (z : (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).Pin → Bool) (walk : (Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice) (m : Memory w)
local notation "limit" => ((ch).rows z).length
local notation "valid" => (ch).read z=some walk
local notation "here" => (fun i l r x y=>fixed i (cursor i) l r x y)


local notation "branch_" => trace walk
local notation "t" => traces walk
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "rot" => RotorSpec.ofRates reset
local notation "real" => chosenClaim X G S ordinary reset branch positive room shorten w walk

local notation "atGeom" i:arg => Geometry G S b k w i (cursor i)
local notation "ram" i:arg => DateCode.history prog m i


/-- All fields of the chosen endpoint and the exact tags in the padded physical register. -/
def terminalArchive (pos:RegisterTimeline.Position) (out:Memory w) : Prop :=
  real (t).path pos out ∧ pos.ports.ArchiveTags out

local notation "dates₀" => RunTrace.machine traces (fun i _=>prog i)

abbrev initialTagged : Prop :=
  initial.ports.held (t).first initial.floor m ∧ real Path.here initial m ∧ initial.ports.ArchiveTags m

abbrev datedArchiveSteps : Prop :=
  ∀i (e : (t).path.Event i),atGeom i → e.incoming (cursor i) (ram i) →
    e.previousClaim real (cursor i) (ram i) → (cursor i).ports.ArchiveTags (ram i) → e.required limit valid →
    e.nextClaim real (cursor (i+1)) (ram (i+1)) ∧ TagInputs traces b initial walk m i e

include gain grain arity ready placed in
theorem terminal_archive_from_dates
    (bootstrap:initialTagged X G S ordinary reset branch positive room shorten w initial walk m)
    (venue : ∀i (e : (t).path.Event i),atGeom i → advances traces b initial walk m limit valid i e)
    (acquire:datedArchiveSteps X G S ordinary reset branch positive room shorten w fit b initial z walk m)
    (accepted:valid) :
    terminalArchive X G S ordinary reset branch positive room shorten w walk (cursor S.length)
      (DateCode.history dates₀ m S.length) :=by
  have finished:=original_tagged_archive_prefix X G S ordinary reset branch positive room shorten w fit
    b initial gain grain arity ready placed z walk m bootstrap venue acquire (t).path .here rfl (Or.inr accepted)
  rw [history_from_cuts traces b initial walk m S.length le_rfl]
  exact ⟨finished.2.2.1,finished.2.2.2⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
