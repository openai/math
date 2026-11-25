import OAI.Hierarchy.DescentProfiledCalibratedLedger
import OAI.Hierarchy.DescentChosenOrdinaryCharge

namespace OAI
/-! The signed ordinary branch and the padded reset both pay their authentic
native instructions on the original normalized calendar. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open DescentCompiler.TerminalScale DescentDatedAddressBook PhysicalReset RegisteredReset DescentHostDegree
set_option quotPrecheck false
set_option hygiene false
open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F)
    {n d : ℕ} (board : NonlinearExpanders.Graph n d) (op : RotorSpec)
    (t f g resetCost cut ratio drift driftR bound slots τ B h copies p w lo header limit : ℕ)
local notation "J" => Nat.log 2 h/(2*B)
local notation "tb" => tail τ J
local notation "S" => stageNumbers G t J f g resetCost copies tb
local notation "cell" => groupBits t J (hostRate t resetCost) (capRate G t g) (cutRate t f g)
local notation "ar" => PitchCalendar.argumentRate G board op t f g resetCost drift driftR bound slots
local notation "rr" => PitchCalendar.roleRate G board op t f g resetCost drift bound slots
local notation "receiver" => degreeRate G board op t f g resetCost (maximumDegree (t+1))
local notation "K" => (⟨t,f,g,resetCost,atRound t,cut,ratio,receiver,drift,bound,max ar rr⟩ : RegisteredReset.Parameters)
variable (ordinary : OrdinaryRates G S cell cut) (reset : ResetRates G S cell (atRound t) n d op.C f g cut tb)
    (boardAt : reset.board=board)
    (branch : G.b ≤ 2^(capRate G t g)) (positive : 0 < p) (room : 10*(X.size+1) ≤ copies)
    (shorten : reentryRate d op.C*(1-(2-G.rate)/4)^t ≤ 1/2) (fit : (S).firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
local notation "b₀" => fromProfiles G S board op cell tb p f g drift limit h lo header (ch).layout
variable (initial : Position)
local notation "cursor" i => calendar (w:=w) traces b₀ initial i
local notation "socket" => 2^Nat.clog 2 (NativeBranch.localLimit G S)
local notation "bin" => NativeBranch.binLimit (k:=cell) S

local notation "Offers" => ProfiledOrdinaryOffer G f g board op t resetCost τ drift bound B h
local notation "grain" => DescentPackedEpochShelves.grain (h/2) G.C


/-- Actual instruction price at every original date, including the meter and the
register fallback used when its cut has no events. -/
def StageLedger : Prop :=
  ∀(initial : Position), let menu:=b₀
    drift+1 ≤ scale J driftR → limit ≤ bound →
    p=bin*(h/(16*((socket*(G.b^(t*J)*G.b))*bin))) →
    Geometry G S menu cell w 0 initial →
    ∀addrRate headRate : ℕ,ProfiledRate.Covers G board op t f g resetCost τ drift bound B h addrRate →
    initial.floor ≤ 2^(headRate*h) → (t+1+max addrRate headRate+2)*h ≤ w →
    ∀R H base field wire hist : ℕ,initial.ports=DatePorts.initial G op X R
      (DescentDatedSeedStartup.selectedLayout G S h cell tb g p drift limit f slots base field wire hist)
      cell H ((S).groupCount 0) h ((S).grainAt G.b p 0) →
    w ≤ ratio*h → 2^h ≤ copies → copies ≤ (2^h)^2 →
    lo+extent grain (ch).layout ≤ header → header < initial.floor →
    (∑i∈Finset.range (S).length,(instruction (w:=w) traces menu initial i).tariff)*2^J ≤
      2*(copies*((S).copies*p))

local notation "lead_" => 9*ProfiledOrdinaryOffer.ordinaryUnitLead G t resetCost ratio
local notation "exp_" => ProfiledOrdinaryOffer.ordinaryExponent G t f g resetCost driftR ar rr
local notation "pack_" => 5+(localSocketRate G t g+Nat.clog 2 G.b*(t+1))

open Filter
theorem profiled_stage_ledger (saving : ℕ) :
    ∃minimumTail minimumBus : ℕ,∀τ B : ℕ,minimumTail ≤ τ → 2*τ+minimumBus ≤ B →
    ∀ᶠ h : ℕ in atTop,let J':=Nat.log 2 h/(2*B)
    let tail':=tail τ J'
    let k':=groupBits t J' (hostRate t resetCost) (capRate G t g) (cutRate t f g)
    PitchCalendar.Purchased G board op t f g resetCost drift driftR bound slots ratio τ B h →
    ReceiverCalendar G board op t f g resetCost τ drift bound B h →
    ∀{cp' nP' : ℕ} (X : Approximation F cp' nP') (copies p w lo header limit : ℕ),let S':=stageNumbers G t J' f g resetCost copies tail'
    ∀(ordinary : OrdinaryRates G S' k' cut) (reset : ResetRates G S' k' (atRound t) n d op.C f g cut tail'),
    reset.board=board → ∀(branch : G.b ≤ 2^(capRate G t g)) (positive : 0 < p)
      (room : 10*(X.size+1) ≤ copies) (shorten : reentryRate d op.C*(1-(2-G.rate)/4)^t ≤ 1/2)
      (fit : S'.firstWidth G.b p < 2^w),
      StageLedger X G board op t f g resetCost cut ratio drift driftR bound slots τ B h copies p w lo header limit
        ordinary reset branch positive room shorten fit :=by
  let cutoff:=ProfiledOrdinaryOffer.ordinaryCutoff G t f g resetCost driftR
  obtain ⟨R,E,T,C,bills⟩:=purchased_calendar G board op K lead_ exp_ 5 saving pack_
  refine ⟨T,max C cutoff,?_⟩
  intro τ B late reserve
  have room₀ : 2*τ+C ≤ B:=by omega
  have enough : cutoff ≤ B:=by omega
  filter_upwards [bills τ B late room₀,ProfiledOrdinaryOffer.chosen_ordinary_charge G board op t f g
    resetCost τ drift bound B driftR ratio saving ar rr slots enough] with h booked charges
  dsimp only
  intro buy lookups cp' nP' X copies p w lo header limit ordinary reset boardAt branch positive room shorten fit initial
  dsimp only
  intro capDrift size chosen seed addrRate headRate address headFit machineFit R₀ H base field wire hist born
    ratioFit ambient upperSites beforeHeader oldHeader
  apply profiled_calendar_ledger X G board op t f g resetCost cut ratio drift driftR bound slots τ B h copies p w
    lo header limit ordinary reset boardAt branch positive room shorten fit initial buy lookups capDrift size
    chosen seed addrRate headRate address headFit machineFit R₀ H base field wire hist born ratioFit ambient
    upperSites beforeHeader oldHeader R E lead_ exp_ 5 saving booked
  intro x
  dsimp only
  intro pos capacity word lower raised headerAt archive guarded live space
  exact charges x live space buy capDrift capacity word lower raised headerAt pos archive guarded

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
