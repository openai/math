import OAI.Computability.VPVNP.CompressorBlockGroups
import OAI.Computability.VPVNP.CompressorRefreshStageVisits
import OAI.Computability.VPVNP.CompressorScriptWindow

/-!
# Actual expander-refresh packets in the complete compressor script

The calendar index includes all preceding shrinking levels and the three
refresh header publishers. At each index the script table is the native
worker used by the degree - refresh proof. The packet sequence reads the
original term tape and leaves the verified refreshed incidence and motif
arrays in its shared data memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshCore

open BurstRAM BlockPlanner Compression Compression.Refresh Compression.DegreeRefresh
open PortRefresh LevelRecipe SourceOnline

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- The block template's dimensions used to enumerate the refresh core stages. -/
abbrev shape := RefreshBlockPlan.shape B
/-- Level-header expressions at the block's refresh step, with table zero as the refresh arena. -/
abbrev input := RefreshBlockPlan.input (BlockProgram.geometry B) S.steps (0 : Fin 6)
/-- The ordered native stages of the refresh core for this template. -/
abbrev stages := LevelRecipe.order (shape B)
/-- The block-planner visits obtained by compiling each refresh core stage against the selected
level input. -/
abbrev entries := (stages B).map (RefreshBlockPlan.stage B (input B))

/-- The precise contiguous range of native refresh stages in one block. -/
def window : BlockPlanner.Window (BlockProgram.script B) (entries B) := BlockGroups.refresh B 1

/-- Embeds a stage's ordinal within the refresh core into the full block script. -/
def index (i : Fin (stages B).length) : Fin (BlockProgram.script B).size :=
  (window B).index (Fin.cast (List.length_map (RefreshBlockPlan.stage B (input B))).symm i)

theorem index_visit (i : Fin (stages B).length) : (BlockProgram.script B).visit (index B i) =
    RefreshBlockPlan.stage B (input B) ((stages B)[i.val]) := by
  have h := (window B).visit (Fin.cast (List.length_map (RefreshBlockPlan.stage B
    (input B))).symm i)
  simpa only [index,entries,List.getElem_map,Fin.val_cast] using h

theorem index_worker (i : Fin (stages B).length) : (BlockProgram.script B).catalog (index B i) =
    ((stages B)[i.val]).worker S.degree_bounds.2 (RefreshBlockPlan.term B) :=
  congrArg BlockPlanner.Visit.worker (index_visit B i)

variable {g w : ℕ} (X : State S.portExponent (S.portExponent + g))
private abbrev connected := (S.port_bound.connected_and_pos S.port_order).1
local notation "hC" => connected (S := S)
local notation "Tₛ" => RefreshBlockPlan.order B
local notation "F" => B.refresh
variable (c : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh)
variable (old : IncidenceDirectory w) (start cap : ℕ)

/-- The source execution of one indexed core stage with its native worker, cursor interval,
fuel, public operands and choice tapes. -/
def visit (i : Fin (stages B).length) : SourceOnline.Visit (BlockProgram.script B) w :=
  let j := (stages B)[i.val]
  let T := RefreshBlockPlan.term B
  let data := j.nativeBank S.degree_bounds.2 S.graph Tₛ X start old
    (TermWorker.motifData F Tₛ finProdFinEquiv.symm w)
  SourceOnline.Visit.ofWorker (A := BlockProgram.script B) (index B i) (j.worker S.degree_bounds.2
    T) (index_worker B i)
    (Scheduled.fuel S.degree_bounds.2 cap j) (Fin.ofNat _ j.first) (Fin.ofNat _ (j.limit X start))
    (fun z ↦ data (Fin.cast (j.worker_params S.degree_bounds.2 T) z))
    (Scheduled.tapes (w := w) X S.graph (Nat.two_pow_pos _) hC F c start (shape B).stride j)

/-- The full native refresh source appears at its actual global program
indices, with no extra branch or reorder between the term worker and the
incidence scans. -/
theorem walk (L : Allocation.PrepareLayout X old (shape B).a₀ (shape B).dH (shape B).ties
    (shape B).stride start)
    (m : Memory w) (rs : List (Report w))
    (run : Build.Run X S.graph (Nat.two_pow_pos _) hC F S.port_order S.degree_bounds.2 c Tₛ old
      start
      (shape B).stride cap L m rs) : SourceWalk (SourceOnline.Visit.Runs
        (A := BlockProgram.script B)) (List.ofFn (visit B X c old start cap)) m rs := by
  have raw := Scheduled.sources X S.graph (Nat.two_pow_pos _) hC F S.port_order S.degree_bounds.2
    c Tₛ old start
    (shape B).stride cap L m rs run
  apply raw.mapAt (visit B X c old start cap)
  intro i mem reports workerRun
  unfold visit
  apply (SourceOnline.Visit.ofWorker_runs (A := BlockProgram.script B) ..).mpr
  exact workerRun

end CompressorRecords.RefreshCore

end

end VPVNP
end Computability
end OAI
