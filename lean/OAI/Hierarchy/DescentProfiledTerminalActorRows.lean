import OAI.Hierarchy.DescentProfiledResetAdvance
import OAI.Hierarchy.DescentRegisterOriginalCourse

namespace OAI
/-! # The terminal actor-occupancy pages read on the final reset of the purchased branch -/
namespace Hierarchy.DescentSixParty.Chronology.Path
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
  {bits : P → ℕ} {d k wire hist : ℕ} {q ε : ℝ}
  {I A B : MarkedWorld F d P bits} {j₀ z₀ D₀ j₁ z₁ D₁ j₂ z₂ D₂ : ℕ}
  {first : Reached I G q ε S k j₀ z₀ D₀ wire hist} {middle : Reached A G q ε S k j₁ z₁ D₁ wire hist}
  {last : Reached B G q ε S k j₂ z₂ D₂ wire hist}

private theorem earlier_selected_length (left : Path first middle) (right : Path middle last)
    {whole : Path first last} (cut : left.append right = whole) : left.selections.length ≤ whole.selections.length := by
  subst whole
  rw [Path.selections_append, List.length_append]
  exact Nat.le_add_right _ _

end Hierarchy.DescentSixParty.Chronology.Path

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
set_option cleanup.letToHave false
set_option maxHeartbeats 1600000
attribute [local irreducible] normalizedPackedChart SeedNamed.issued Origin.source Origin.archivePackage
  RegisterTimeline.position RegisterTimeline.date DateCode.history
set_option maxRecDepth 12000
set_option pp.maxSteps 650
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "profiled_terminal_actor_rows"
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

open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentPacking.PackedMatch.Local.Stage
variable (drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "board" => reset.board
local notation "op" => RotorSpec.ofRates reset
local notation "frozen" => tail
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

variable (bus : payload≤w) (seedDegree : initial.ports.venue.degree=3)
    (degreeRoom : maximumDegree (S.rounds+1)+1<2^w)

variable (walk : (last).Choice) (m : Memory w)
local notation "capSeq" => capCalendar G.b S.rounds g S.height

local notation "ix" => S.length-1
local notation "finalCur" => cursor ix
local notation "last₁" => (resetAt ix finalCur).inner
local notation "prevFloor" => (finalCur).ports.priorStart k (finalCur).floor
local notation "placedAt" => (last₁).rebased ((last₁).stageStart prevFloor)
local notation "terminal" => (fun x:DescentColonies.Block k=>(last₁).successor.terminalActor placedAt x.val)

attribute [local irreducible] traceAt

include bus seedDegree degreeRoom in
/-- The complete path receipt supplies the original incoming venue even when the final reset
is the first event whose actor-occupancy planes are requested by the terminal procedure. -/
theorem profiled_terminal_actor_rows (seed₁ : data 0)
    (placed₁ : ∀j (e : RunTrace.Events traces j),RegisterTimeline.fitsAt traces menu initial (w:=w) j e)
    (words : SnapshotWordRoom S n h k tail p f g payload w) (limit : ℕ) (valid : Prop)
    (origin : initial.ports.held (traces walk).first initial.floor m)
    (earlier : OriginalCourse traces menu initial walk m limit valid)
    (receipt : Path.FinalReset p (traces walk).path)
    (alive : (traces walk).path.selections.length<limit ∨ valid) :
    receipt.event.actorPlanes terminal (DateCode.history program m S.length) :=by
  have fixed : ∀j (x y : RunTrace.Events traces j) a b,
      issue j x (cursor j) a→issue j y (cursor j) b→a=b :=
    fun j x y a b=>all_registered_moves X G S ordinary reset branch positive room shorten w menu
      rfl rfl rfl j (cursor j) x y a b
  have lastRow (e : (traces walk).path.Event ix) (lastReset : e.isReset=true) :
      e.actorPlanes terminal (DateCode.history program m S.length):=by
    cases e with
    | ordinary before step after_ defn=>cases lastReset
    | @reset world₁ z₁ D₁ n₂ h₂ C₂ f₂ g₂ cut₂ tail₂ src₁ ctl₁ before B after_ joined=>
      let suffix:=(Path.here.reset B).append after_
      have cut : before.append suffix=(traces walk).path:=
        (Path.append_cut_assoc before (Path.here.reset B) after_).symm.trans joined
      have live : before.selections.length<limit ∨ valid :=
        alive.imp_left (Nat.lt_of_le_of_lt (Path.earlier_selected_length before suffix cut))
      have incoming:=held_prefix traces menu initial walk m limit valid fixed origin earlier.advance before suffix cut live
      have printed:=profiled_last_actor_planes X G S ordinary reset branch positive room shorten w fit
        drift degree payload lo header initial bus seedDegree degreeRoom walk m (U:=world₁) (i:=ix) (z:=z₁) (D:=D₁) (r:=src₁)
        (n₁:=n₂) (h₁:=h₂) (C₁:=C₂) (f₁:=f₂) (g₁:=g₂) (cut₁:=cut₂) (tail₁:=tail₂) (ctl:=ctl₁)
        before B after_ joined seed₁
        placed₁ words incoming receipt.succ_age
      let resetEvent : (traces walk).path.Event ix := .reset before B after_ joined
      let sameHistory := congrArg (DateCode.history program m) receipt.succ_age
      exact (congrArg (fun actual => resetEvent.actorPlanes terminal actual) sameHistory).mp printed
  exact lastRow receipt.event receipt.is_reset

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
