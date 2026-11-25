import OAI.Hierarchy.DescentPaidPitchCalendar

namespace OAI
/-! # The two previous physical source pitches from a single paid calendar and its actual initializer -/
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
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : (S.firstWidth G.b p) < 2^w)
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

open DescentCompiler.TerminalScale DescentDatedAddressBook
variable {t resetCost τ β copies driftR degreeMax ratio : ℕ}
local notation "height₀" => b.payload
local notation "J₀" => Nat.log 2 height₀/(2*β)
local notation "startRate" => (NativePitch.FundedBase.public_rate G t f g resetCost).choose
local notation "funds₀" => 44*argumentDigitRate G t f g resetCost driftR startRate
local notation "laneR" => returnLaneRate G t f g resetCost funds₀
local notation "roleR" => registeredRoleRate G t f g resetCost
local notation "maxD" => maximumDegree (t+1)
local notation "resetR" => PhysicalReset.allDensityRate G b.board b.op t f g resetCost maxD
local notation "A₁" => scale J₀ (max laneR resetR)
local notation "A₂" => scale J₀ (max roleR resetR)

variable (slots : ℕ)
variable (buy : PitchCalendar.Purchased G b.board b.op t f g resetCost b.drift driftR degreeMax slots ratio τ β b.payload)
    (schedule : S=stageNumbers G t (Nat.log 2 b.payload/(2*β)) f g resetCost copies b.tail)
    (depth : k=groupBits t (Nat.log 2 b.payload/(2*β)) (hostRate t resetCost) (capRate G t g) (cutRate t f g))
    (tailBits : b.tail=TerminalScale.tail τ (Nat.log 2 b.payload/(2*β))) (dr : b.drift+1 ≤ scale (Nat.log 2 b.payload/(2*β)) driftR)
    (degreeRoom : b.degreeLimit≤degreeMax)
local notation "socket₀" => 2^Nat.clog 2 (NativeBranch.localLimit G S)
local notation "bin₀" => NativeBranch.binLimit (k:=k) S
variable (chosen : p=(NativeBranch.binLimit (k:=k) S)*(b.payload/(16*(((2^Nat.clog 2 (NativeBranch.localLimit G S))*(G.b^(S.rounds*S.height)*G.b))*(NativeBranch.binLimit (k:=k) S)))))



local notation "steps" => RegisterTimeline.issued (w:=w) traces b
local notation "output" => RegisterTimeline.calendar (w:=w) traces b initial
variable (start : Geometry G S b k w 0 initial)
    (placed : ∀i e,RegisterTimeline.fitsAt (traceAt X G S ordinary reset branch positive room shorten) b initial (w:=w) i e)



local notation "argRead" => PitchCalendar.argumentRate G b.board b.op t f g resetCost b.drift driftR degreeMax slots
local notation "roleRead" => PitchCalendar.roleRate G b.board b.op t f g resetCost b.drift degreeMax slots

attribute [local irreducible] SeedNamed.issued Origin.source

include gain grain arity buy schedule depth tailBits dr degreeRoom chosen start placed in
theorem calibrated_prefix_pitch (R H base field wire hist : ℕ)
    (born : initial.ports=DatePorts.initial G b.op X R
      (DescentDatedSeedStartup.selectedLayout G S height₀ k b.tail g p b.drift b.degreeLimit f slots base field wire hist)
      k H (S.groupCount 0) height₀ (S.grainAt G.b p 0))
    (walk : (last).Choice)
    {U : MarkedWorld F 0 pins widths} {i z D : ℕ}
    {r : Reached U G price fee S k i z D (S.epochPower^S.priceExponent) s}
    (before : Path (trace walk).origin.source r) (after : Path r (trace walk).target)
    (joined : before.append after=(trace walk).path) :
    (output i).ports.ArchivePitchRoom (S.groupCount i) height₀ (scale J₀ argRead) (scale J₀ roleRead) :=by
  let C₀:=(DescentDatedSeedStartup.selected_seed_pitch_room G b.op t f g resetCost b.drift degreeMax slots).choose
  have seedDegree : initial.ports.venue.degree=3:=by rw [born];rfl
  have initialFit:=buy.initial copies b.degreeLimit base field wire hist
  dsimp only at initialFit
  have dated : S=stageNumbers G t J₀ f g resetCost copies (TerminalScale.tail τ J₀):=schedule.trans (by rw [tailBits])
  have kEq : k=groupBits t J₀ S.hostGain S.capGain (cutRate t f g):=by rw [schedule];exact depth
  rw [←dated,←kEq,←tailBits] at initialFit
  have period : S.rounds*S.height=t*J₀:=by rw [schedule];rfl
  have sourceSize : p=bin₀*(height₀/(16*((socket₀*(G.b^(t*J₀)*G.b))*bin₀))):=by
    simpa only [←period] using chosen
  rw [←sourceSize] at initialFit
  have init : initial.ports.ArchiveDensity (S.groupCount 0) height₀ (scale J₀ C₀) (scale J₀ C₀):=by
    rw [born]
    exact (initialFit cp nP X R H degreeRoom).toArchiveDensity
  exact named_prefix_pitch X G S ordinary reset branch positive room shorten w b initial gain grain arity
    buy.old buy.returned buy.resetPitch schedule depth tailBits dr degreeRoom buy.roleWidth chosen
    start placed seedDegree C₀ init walk before after joined

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
