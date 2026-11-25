import OAI.Hierarchy.DescentNamedPitchModes
import OAI.Hierarchy.DescentSelectedSeedPitchRoom
import OAI.Hierarchy.DescentRegisteredVenueDegree

namespace OAI
/-! # A single funded pair of live source pitches on every prefix, including the first invalid branch -/
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
variable (actual : ArgumentCalendar G b.op t f g resetCost τ β b.drift driftR degreeMax (b.payload))
    (resources : ReturnCalendar G t f g resetCost driftR (44*argumentDigitRate G t f g resetCost driftR ((NativePitch.FundedBase.public_rate G t f g resetCost).choose)) τ β ratio (b.payload))
    (resetBus : PhysicalReset.DensityCalendar G b.board b.op t f g resetCost τ (maximumDegree (t+1)) b.drift β degreeMax (b.payload))
    (schedule : S=stageNumbers G t (Nat.log 2 (b.payload)/(2*β)) f g resetCost copies b.tail)
    (depth : k=groupBits t (Nat.log 2 (b.payload)/(2*β)) (hostRate t resetCost) (capRate G t g) (cutRate t f g))
    (tailBits : b.tail=TerminalScale.tail τ (Nat.log 2 (b.payload)/(2*β))) (dr : b.drift+1 ≤ scale (Nat.log 2 (b.payload)/(2*β)) driftR)
    (degreeRoom : b.degreeLimit≤degreeMax) (roleWidth : scale (Nat.log 2 (b.payload)/(2*β)) (registeredRoleRate G t f g resetCost)≤(b.payload))
local notation "socket₀" => 2^Nat.clog 2 (NativeBranch.localLimit G S)
local notation "bin₀" => NativeBranch.binLimit (k:=k) S
variable (chosen : p=(NativeBranch.binLimit (k:=k) S)*((b.payload)/(16*(((2^Nat.clog 2 (NativeBranch.localLimit G S))*(G.b^(S.rounds*S.height)*G.b))*(NativeBranch.binLimit (k:=k) S)))))



local notation "steps" => RegisterTimeline.issued (w:=w) traces b
local notation "output" => RegisterTimeline.calendar (w:=w) traces b initial
variable (start : Geometry G S b k w 0 initial)
    (placed : ∀i e,RegisterTimeline.fitsAt (traceAt X G S ordinary reset branch positive room shorten) b initial (w:=w) i e)
    (seedDegree : initial.ports.venue.degree=3)

attribute [local irreducible] SeedNamed.issued Origin.source

include gain grain arity actual resources resetBus schedule depth tailBits dr degreeRoom roleWidth chosen start placed seedDegree in
theorem named_prefix_pitch (seedRate : ℕ)
    (seed : initial.ports.ArchiveDensity (S.groupCount 0) height₀ (scale J₀ seedRate) (scale J₀ seedRate))
    (walk : (last).Choice)
    {U : MarkedWorld F 0 pins widths} {i z D : ℕ}
    {r : Reached U G price fee S k i z D (S.epochPower^S.priceExponent) s}
    (before : Path (trace walk).origin.source r) (after : Path r (trace walk).target)
    (joined : before.append after=(trace walk).path) :
    (output i).ports.ArchivePitchRoom (S.groupCount i) height₀
      (scale J₀ (max seedRate (max laneR resetR))) (scale J₀ (max seedRate (max roleR resetR))) :=by
  have mono {a c : ℕ} (z : a≤c) : scale J₀ a ≤ scale J₀ c:=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ z)
  have fixed:=fun i (x z : RunTrace.Events traces i) (u v : Move w)=>
    all_registered_moves X G S ordinary reset branch positive room shorten w b gain grain arity i (output i) x z u v
  have caps (c : (last).Choice): (traces c).path.capFactors=capCalendar G.b S.rounds b.gain S.height:=by
    dsimp only [traceAt]
    exact (trace c).calendar.trans (congrArg (fun j => capCalendar G.b S.rounds j S.height) gain.symm)
  have tags (c : (last).Choice) : (traces c).path.kinds=kindCalendar S.rounds S.height:=by
    dsimp only [traceAt]
    exact (trace c).kinds
  have degree₀ : initial.ports.venue.degree≤ maximumDegree (S.rounds+1):=by
    rw [seedDegree]
    simpa only [Nat.zero_mod,atRound] using round_degree_le S.rounds 0
  have degrees (i : ℕ) : (output i).ports.venue.degree≤ maxD:=by
    have found:=calendar_degree_le (w:=w) traces b tags initial degree₀ i
    have rounds : S.rounds=t:=by rw [schedule];rfl
    exact found.trans_eq (congrArg (fun j => maximumDegree (j+1)) rounds)
  have real (i : ℕ) (e : RunTrace.Events traces i) : Geometry G S b k w i (output i):=
    geometry_on_event traces b initial fixed caps tags start placed e.1 i e.2
  have group (j : ℕ) : 0<S.groupCount j:=by rw [schedule];exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (Nat.two_pow_pos _))
  have hPos:0<height₀:=by
    have a:=roleWidth
    exact (Nat.two_pow_pos _).trans_le a
  apply RegisterTimeline.issued_prefix_pitch traces b initial fixed start.room
    (fun i e _=>placed i e (real i e)) _ _ (seed.weaken (mono (le_max_left ..)) (mono (le_max_left ..)))
    _ walk before after joined hPos group
  intro j e _
  have paid:=selected_output_pitches X G S ordinary reset branch positive room shorten w b gain grain arity
    actual resources resetBus schedule depth tailBits dr degreeRoom roleWidth chosen j e (output j) (real j e) (fun _=>degrees j)
  exact RegisterTimeline.OutputPitches.weaken traces b paid (mono (le_max_right ..)) (mono (le_max_right ..))

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
