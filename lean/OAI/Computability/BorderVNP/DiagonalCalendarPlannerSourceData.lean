import OAI.Computability.BorderVNP.DiagonalCalendarPlannerPostAtSource

/-! # The pointwise data family of the planner's physical post request -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.SignedTaskArena Routing JointHeader

/-- Families of data indexed by an original positive startup, its returning
prefix and the header physically observed on its team. -/
def OriginalWriterDataShape {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pub : Fin (R+1) → Arg → Word w} {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
    {pin : Fin d → Bool} (task : SignedTaskArena.Layout)
    (boot : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G pub reg args pin x.val u)
    (L : WireLayout (R+1) r link) (fixed : Block (R+1)) : Type 1 :=
  (x : {ext // PositiveExterior G args pin w ext}) →
    (_active : PinStart.JointPrefix task.id (fun i => (boot x i).start)) → (_u : Fin (R+1)) →
    (fields : PositiveFields task.cube.header.profile task.cube.n task.cube.header.d task.cube.header.cap task.cube.teams task.dim w) →
    (_seen : fields.bits=observed L x.val fixed) → Type

end TeamContraction.ProcessorSlots.BootedPinStart

namespace Diagonal

open Diagonal.ExternalSew Cover Packing Packing.DeckGrid Crossing Branch Epoch PackedHistoryCircuit
open PackedHistoryCircuit.Normalized SelectedSchedule EnrichedOuter TeamScales TeamContraction ProcessorSlots
open VPVNP ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open FieldProcessor RoutingISA RoutingISA.Evaluator RoutingISA.Transmission
open GeometryAdvice GeometryFrameEncoding RoutingISA.Pins VPVNP.BurstRAM RoutingISA.CompactMachine TeamSite
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins
open Diagonal.ExternalSew GridHosts
open scoped Classical BorderVNP.Epoch.Cube

open Packing.Inherited Packing.Inherited.FrozenTape Shortening.PublicCapacity BorderVNP.Epoch.Round
open ResidueIndex ResidueBox
attribute [local instance] portFintype
attribute [local irreducible] Nat.clog UniversalMachine.programPrefix logWidth prefixCapacity
  FieldProcessor.freeWidth Fintype.equivFin
set_option maxRecDepth 8200
set_option maxHeartbeats 4400000
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {paid : PaidIdentity F D m}
    {S : SiteSchedule paid} {cube : FixedCube K} {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales S (cube.pred+1) extra}
    {b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourcePower+1)}
    {φ : K →+* F} {q : ℕ} {hm : 0 < «m»} {header C A₀ a B₀ b₀ J j coeff addr power cut : ℕ}
    {adv : ℕ → ℕ} {c charge factor l : ℕ}
    (cal : SignedCalendarAt cube b φ q hm header C A₀ a B₀ b₀ J j coeff addr power cut adv c charge factor (l+1))

local notation "r₁" => stretch b.ρ (l+1)
local notation "size₁" => stretch b.σ (l+1)
local notation "budget₁" => adv (adviceScale b.σ b.ρ (l+1))
local notation "pins₁" => (pairedTableParameters (l+1) (size₁)+2)*(budget₁+6)

variable (grid : LocatedSignedGridAt cube b header (l+1)) (qpos : 1 ≤ Q)
    (position : (Fin (Fintype.card (Cube D)) → Deck (CoverScale.initialDepth (Cube D)
      (stretch b.ρ (l+1)) (l+1)-1+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

variable {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField paid (φ ∘ cube.table) q l (stretch b.σ (l+1)) ord}
    (chart : AdvisedBranch common) [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (b.physical.teamsPred (l+1)+1) (stretch b.ρ (l+1))
      (b.physical.multBits (l+1)) (b.physical.tally (l+1)) (b.physical.word (l+1))
      (adv (adviceScale b.σ b.ρ (l+1))+6))
    (chargeFit : reader.charge ≤ c*(adv (adviceScale b.σ b.ρ (l+1))+1)^charge)

local notation3 (prettyPrint := false) "layout₁" => cal.frozenLayout chart reader chargeFit
local notation3 (prettyPrint := false) "selectedTask" => cal.frozenTask grid qpos position chart reader chargeFit

local notation3 (prettyPrint := false) "planner₁" => cal.frozenPlannerTask grid qpos position chart reader chargeFit
local notation3 (prettyPrint := false) "hold₁" => cal.frozenRouteBlock chart reader chargeFit
local notation3 (prettyPrint := false) "boots₁" => cal.frozenSites_boots grid qpos position chart reader chargeFit hold₁

private noncomputable def plannerSourceShape (live : Fin pins₁ → Bool) : Type 1 :=
  BootedPinStart.OriginalWriterDataShape selectedTask ((boots₁).2.choose live) layout₁ hold₁

set_option cleanup.letToHave false in
set_option maxRecDepth 15000 in
set_option maxHeartbeats 6500000 in
/-- The type of a planner request with the original header bits, a transfer
of its charge to the deployed request, and the calibrated argument budget.
It can be supplied directly as the route decoder's pointwise data family. -/
noncomputable def SignedCalendarAt.PlannerSourceData
    (rate : CalendarPostRateAt cube b φ q adv c charge (l+1)) (live : Fin pins₁ → Bool) :
    plannerSourceShape cal grid qpos position chart reader chargeFit live :=
  fun x active u fields seen =>
    let original := cal.frozenPostWriterAt grid qpos position chart reader chargeFit rate live x active u fields seen
    {p : FragmentRows.WriterPostRequest planner₁ (((boots₁).2.choose live) x) active u //
      p.fields.bits=fields.bits ∧ (p.Charge → original.Charge) ∧
      (scales.chosenSignedWindows cube E (l+1) r₁).argumentsCalls=p.budget}

end Diagonal

end BorderVNP
end Computability
end OAI
