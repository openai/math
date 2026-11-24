import OAI.Computability.VPVNP.CompressorShrinkPassSegments

/-! # Running the native shrinking pass from a reachable graph -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkScheduledRun

open BurstRAM Compression ShrinkBlockInputs BlockPlanner DescriptorSpace SourceOnline
open PairSimulation.LocalHistory PairSimulation.TraversalRows PairSimulation.TraversalRoles
open ShrinkOutput ScheduledTrace PassTimeline Schedule
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
  (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps)
  {g w : ℕ} (X : GreedyArena.ShrinkingState (a i) g) (pub : Fin 11 → Word w)
  (positions blocks round n : ℕ) (live : round < blocks)
  (initial : TaggedLayer) (initialFrame : Fin 8 → Word w)
  (fuel cap small refreshRate : ℕ) (past : List (SelectedLevel B f hf)) (m : Memory w)
  (encode : SelectedScore.Selection B X → List Bool)
set_option quotPrecheck false
local notation "base" => pub 2
local notation "layout" => BlockProgram.layout B (Fin.val (pub 2)) positions blocks
local notation "script" => BlockProgram.script B
local notation "loc" => (⟨round, .shrink i⟩ : Located S.steps)
local notation "o" => (PassOrigin.shrink i rfl X : PassOrigin B f hf (B.shrinkPassAt f hf i rfl X))
local notation "src" => old B i (Fin.val (pub 2)) positions blocks round live
local notation "dst" => next B i (Fin.val (pub 2)) positions blocks round live
local notation "inc" => packedIncidence layout w src (DemandRAM.oldCount X)
local notation "begin" => tableBase layout src (0 : Fin 6)
local notation "total" => directoryRows layout
local notation "resident" =>
  CompiledResident.resident B f hf (pub 2) positions blocks n initial initialFrame
local notation "rawRate" => commonRawRate (fixedRate B) refreshRate
local notation "rate" => nativePassRate (BlockProgram.script B) rawRate * positions
local notation "pt" => Workspace.ports (arity (BlockProgram.script B).catalog) (pub 2)

set_option maxHeartbeats 900000 in
-- Checking the ten packet families also checks their dependent native run certificates.
/-- Run the true geometry, selection, incidence and publication workers at each admitted term. -/
theorem realize (common : ShrinkCurrentBranch.Common B f hf i X (Fin.val (pub 2))
      positions blocks src dst m fuel)
    (fits : ShrinkBranch.PrefixFits B X inc begin (10 : Word w) fuel)
    (index : past.length = (src).val) (size : X.positions ≤ positions)
    (room : endAddress layout < 2 ^ w) (arith : TableArithmetic B i X w)
    (width : SelectedTermWorker.fitConstant B + 4 * Nat.clog 2 (X.maxWireWidth + 1) ≤ w)
    (h₁ : ShrinkHeaderGreedyPackets.clock B i ≤ small)
    (h₂ : scanCap script (ShrinkBundlePackets.maxFuel B i) ≤ small)
    (h₃ : scanCap script fuel ≤ small) (h₄ : scanCap script 95 ≤ small)
    (clock : small ≤ cap) (large : Online.Run.ControlBounds (script).plan cap (w := w))
    (little : Online.Run.ControlBounds (script).plan small (w := w))
    (ready : ScheduledTrace.Boundary resident pub (levelWords layout : Word w)
      total ((loc).first B) past X m) :
    Nonempty (ScheduledTrace.PassRun resident pub (levelWords layout : Word w) total cap small rate
      loc o encode past m) := by
  have current : CurrentGraph.Current layout (src).val X n m := index ▸ ready.stored.1.2.1
  have headLow := column_lower B i positions blocks round live X base size room
  have rows : m (pt).rows.val = (total : Word w) := Fin.ext (ready.totalValue.trans
    (Nat.mod_eq_of_lt (ready.totalValue ▸ (m (pt).rows.val).isLt)).symm)
  have build (s : SelectedScore.Selection B X) :=
    run B i positions blocks round live f hf X base m fuel small common s (encode s) fits
      current.heads headLow size room rows ready.stride arith h₁ h₂ h₃ h₄
  choose pre marker geom p₅ p₆ p₇ p₈ ms tail tables result using build
  exact ofSources B f hf i X pub positions blocks round n live initial initialFrame fuel cap small
    refreshRate past m encode common fits index size room width clock large little ready pre marker
    geom p₅ p₆ p₇ p₈ ms tail tables result

end CompressorRecords.ShrinkScheduledRun

end

end VPVNP
end Computability
end OAI
