import OAI.Computability.VPVNP.CompressorRefreshPassSegments
import OAI.Computability.VPVNP.CompressorRefreshEmit
import OAI.Computability.VPVNP.CompressorPrefixWorkerFit

/-! # Executing every native packet of the refresh pass -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
set_option quotPrecheck false

namespace CompressorRecords.RefreshPass

open BurstRAM Compression DescriptorSpace BlockPlanner PassTimeline Schedule SourceTransport
open PairSimulation.LocalHistory PairSimulation.TraversalRoles ScheduledTrace
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) {g w : ℕ}
variable (pub : Fin 11 → Word w) (positions blocks t n : ℕ)
variable (X : State S.portExponent (S.portExponent + g))
local notation "script" => BlockProgram.script B
local notation "L" => BlockProgram.layout B (pub 2).val positions blocks
local notation "loc" => (⟨t, .refresh⟩ : Located S.steps)
local notation "o" => PassOrigin.refresh (B := B) (f := f) (hf := hf) X
local notation "pass" => Refresh.dyadicRefreshPass X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh S.port_order S.degree_bounds.2
  (f ∘ Sum.inr) ((B.solution_iff f).mp hf).2
local notation "Choice" => (pass).step.Choice
local notation "pt" => Workspace.ports (arity (Script.catalog script)) (pub 2)
local notation "cur" => Script.levelsPerBlock script * t + S.steps
local notation "total" => directoryRows L

variable (initial : TaggedLayer) (initialFrame : Fin 8 → Word w)
local notation "resident" =>
  CompiledResident.resident B f hf (pub 2) positions blocks n initial initialFrame
local notation "shape" => RefreshBlockPlan.shape B
local notation "role" => Scalars.Pass.refresh S.portExponent (S.degreeExponent 0) S.expanderExponent

/-- Execute the common header and demand workers, the selected term worker,
and all succeeding copy and publication workers in the scheduled refresh. -/
theorem realize (termCap cap small : ℕ) (shrinking : Fin S.steps → ℕ)
    (encode : Choice → List Bool) (past : List (SelectedLevel B f hf)) (m : Memory w)
    (ht : t < blocks) (depth : past.length = cur)
    (size : X.positions ≤ positions) (room : endAddress L < 2 ^ w)
    (clock : small ≤ cap) (big : Online.Run.ControlBounds (script).plan cap (w := w))
    (little : Online.Run.ControlBounds (script).plan small (w := w))
    (ready : Boundary resident pub (levelWords L : Word w) total ((loc).first B) past X m)
    (headerClock : SourceOnline.scanCap script
      (ScheduledRates.headerCap (BlockProgram.geometry B) role) ≤ small)
    (termClock : SourceOnline.scanCap script (max 64 termCap) ≤ small)
    (sitesWord : X.positions < 2 ^ w) (degreeWord : slotDegree S < 2 ^ w)
    (portWidth : 2 ^ S.portExponent * X.maxWireWidth < 2 ^ w)
    (selectorWidth : SelectedTermWorker.fitConstant B + 4 * Nat.clog 2 (X.maxWireWidth + 1) ≤ w)
    (nativeWidth : PrefixLevelScale.refreshConstant B + 4 * Nat.clog 2 (X.maxWireWidth + 1) ≤ w)
    (fuel : TermWorker.budget B.refresh (shape).ties ((shape).ports * (shape).dH)
      w X.maxWireWidth ≤ termCap)
    (positive : 0 < termCap) (outputWidth : ∀ c : Choice, ((pass).next c).maxWireWidth < 2 ^ w) :
    Nonempty (PassRun resident pub (levelWords L : Word w) total cap small
      (nativePassRate script (commonRawRate shrinking (RefreshEmit.rawRate B)) * positions)
      loc o encode past m) := by
  have rows : m (pt).rows.val = (total : Word w) := Fin.ext (ready.totalValue.trans
    (Nat.mod_eq_of_lt (ready.totalValue ▸ (m (pt).rows.val).isLt)).symm)
  obtain ⟨hs, ds, term, tail, src⟩ := RefreshEmit.build B f hf (pub 2) positions blocks t small n
    initial initialFrame past X encode m termCap depth ht size room rows ready.stride
    headerClock termClock sitesWord degreeWord portWidth nativeWidth outputWidth fuel positive
    ready.stored
  exact ofSources B f hf pub positions blocks t n X initial initialFrame shrinking m past encode
    ready ht depth size room clock big little hs ds term tail src termCap selectorWidth
    fuel termClock

end CompressorRecords.RefreshPass

end

end VPVNP
end Computability
end OAI
