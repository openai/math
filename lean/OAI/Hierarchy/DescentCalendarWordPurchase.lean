import OAI.Hierarchy.DescentOriginalStageLedger
import OAI.Hierarchy.DescentProfiledUniformCalendarRate

namespace OAI
/-! The machine word is chosen first. The epoch tail and logarithmic divisor
then pay the original code of all dates for all admissible certificates. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open DescentCompiler.TerminalScale DescentDatedAddressBook PhysicalReset RegisteredReset DescentHostDegree
set_option quotPrecheck false
open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F)
    {n d : ℕ} (board : NonlinearExpanders.Graph n d) (op : RotorSpec)
    (t f g resetCost cut ratio drift driftR bound slots τ B h copies p w lo header limit : ℕ)
set_option hygiene false
local notation "J" => Nat.log 2 h/(2*B)
local notation "tb" => tail τ J
local notation "S" => stageNumbers G t J f g resetCost copies tb
local notation "cell" => groupBits t J (hostRate t resetCost) (capRate G t g) (cutRate t f g)

/-- The same native ledger applies to all normalized input profiles at the
fixed word-to-height ratio, even when their lengths vary with height. -/
def EveryStage : Prop :=
    ∀{cp' nP' : ℕ} (X : Approximation F cp' nP') (copies p w lo header limit : ℕ),let ss:=stageNumbers G t J f g resetCost copies tb
    ∀(ordinary : OrdinaryRates G ss cell cut) (reset : ResetRates G ss cell (atRound t) n d op.C f g cut tb),
    reset.board=board → ∀(branch : G.b ≤ 2^(capRate G t g)) (positive : 0 < p)
      (room : 10*(X.size+1) ≤ copies) (shorten : reentryRate d op.C*(1-(2-G.rate)/4)^t ≤ 1/2)
      (fit : ss.firstWidth G.b p < 2^w),
      StageLedger X G board op t f g resetCost cut ratio drift driftR bound slots τ B h copies p w lo header limit
        ordinary reset branch positive room shorten fit

open Filter
theorem calendar_with_word (addr head saving : ℕ)
    (machine : t+1+max addr head+2 ≤ ratio)
    (uniform : ProfiledRate.UniformAddresses G board op t f g resetCost drift bound driftR slots addr) :
    ∃ minTail : ℕ, ∀ τ ≥ minTail, ∃ minBus : ℕ, ∀ B ≥ minBus,∀ᶠ h:ℕ in atTop,
      ProfiledRate.Covers G board op t f g resetCost τ drift bound B h addr ∧
      PitchCalendar.Purchased G board op t f g resetCost drift driftR bound slots ratio τ B h ∧
      ReceiverCalendar G board op t f g resetCost τ drift bound B h ∧
      (t+1+max addr head+2)*h ≤ ratio*h ∧
      EveryStage G board op t f g resetCost cut ratio drift driftR bound slots τ B h :=by
  obtain ⟨T,C,bills⟩:=profiled_stage_ledger G board op t f g resetCost cut ratio drift driftR bound slots saving
  refine ⟨T+1,?_⟩
  intro τ large
  let bound₀:=ProfiledRate.threshold G board op t f g resetCost τ drift driftR bound slots
  refine ⟨max (2*τ+C) bound₀,?_⟩
  intro B paid
  have funded:bound₀ ≤ B:=by omega
  have original:2*τ+C ≤ B:=by omega
  have cut:=funded
  unfold bound₀ ProfiledRate.threshold at cut
  have pitch:PitchCalendar.threshold G board op t f g resetCost drift driftR bound slots τ ≤ B:=by omega
  have pos:0 < τ:=by omega
  filter_upwards [uniform τ B funded,
    PitchCalendar.eventually_purchased G board op t f g resetCost drift driftR bound slots ratio τ B pos pitch,
    paid_receiver_calendar G board op t f g resetCost τ drift driftR bound slots B pitch,
    bills τ B (by omega) original] with h addresses old lookup dates
  exact ⟨addresses,old,lookup,Nat.mul_le_mul_right h machine,dates old lookup⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
