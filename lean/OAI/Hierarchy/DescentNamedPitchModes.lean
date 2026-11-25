import OAI.Hierarchy.DescentChosenOutputPitches
import OAI.Hierarchy.DescentScheduledPitchModes
import OAI.Hierarchy.DescentIssuedPrefixPitch
import OAI.Hierarchy.DescentNamedAllRegisterMoves
import OAI.Hierarchy.DescentRegisteredGeometry

namespace OAI
/-! # Physical public rates for every output word along the named calendar -/
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


attribute [local irreducible] SeedNamed.issued Origin.source

include gain grain arity actual resources resetBus schedule depth tailBits dr degreeRoom roleWidth chosen in
theorem selected_output_pitches (i : ℕ) (event : RunTrace.Events traces i) (a : Position)
    (old : Geometry G S b k w i a)
    (degreeAt : event.2.isReset=true→a.ports.venue.degree≤ maxD) :
    OutputPitches traces b i event a A₁ A₂ :=by
  subst g
  subst p
  subst f
  have mono {x y : ℕ} (z : x≤y) : scale J₀ x ≤ scale J₀ y:=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ z)
  rcases event with ⟨walk,node⟩
  cases node with
  | ordinary prev ticket rest equal =>
    let br := SeedNamed.issued X G S ordinary reset branch positive room shorten walk
    dsimp only [traceAt] at prev rest equal
    let book:=OrdinaryBooks.atDate G S b.op b.gain k i b.p b.tail b.drift b.degreeLimit b.payload (b.seats i) a.ports
    let v:=book.onTicket ticket b.gain b.tail b.p b.f b.payload (b.seats i) a.ports.venue.lanes a.ports.io.roster b.ordinary
    have billed:=Branch.chosen_output_pitches X G S br ticket prev rest equal b.op b.tail b.drift b.degreeLimit
      b.payload (b.seats i) a.ports.venue.lanes a.ports a.ports.io.roster b.ordinary (v.stageStart a.floor)
      actual resources schedule depth tailBits dr degreeRoom bin₀ socket₀ (Nat.two_pow_pos _) chosen
      old.room.archive old.room.args positive roleWidth
    exact ⟨billed.1.trans (Nat.mul_le_mul_left _ (mono (le_max_left ..))),
      billed.2.trans (Nat.mul_le_mul_left _ (mono (le_max_left ..)))⟩
  | reset prev close rest equal =>
    have first : S.firstWidth G.b b.p≤height₀:=by rw [chosen];exact S.split_first_width G.b height₀ bin₀ socket₀ (Nat.two_pow_pos _)
    have pRoom:=S.grain_le_payload G.b b.p height₀ G.base_pos first
    have time : i≤S.length:=by
      have h:=rest.kinds_length
      change (i+1)+rest.kinds.length=S.length at h
      omega
    have receipt:=resetBus.written copies i b.p b.degreeLimit
    dsimp only at receipt
    have «public» : S=stageNumbers G t J₀ b.f b.gain resetCost copies (TerminalScale.tail τ J₀):=
      schedule.trans (by rw [tailBits])
    have dims : k=groupBits t J₀ S.hostGain S.capGain (cutRate t b.f b.gain):=by rw [schedule];exact depth
    rw [←«public»,←dims,←tailBits] at receipt
    have cap : a.ports.venue.cap=((capCalendar G.b t b.gain J₀).take i).prod*256:=by
      have h:=old.capacity
      simpa [schedule,stageNumbers] using h
    have measured:=receipt b.ordinary a.ports.venue a.ports.operandLanes a.ports.roleLanes
      (a.ports.priorStart k a.floor) a.ports.io.wire a.ports.io.roster time pRoom degreeRoom
      (degreeAt rfl) cap old.format.paid
    apply measured.imp_right
    intro cost
    exact cost.trans (Nat.mul_le_mul_left _ (le_min (mono (le_max_right ..)) (mono (le_max_right ..))))

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
