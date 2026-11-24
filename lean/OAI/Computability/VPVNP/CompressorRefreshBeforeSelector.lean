import OAI.Computability.VPVNP.CompressorRefreshVerifiedStages
import OAI.Computability.VPVNP.CompressorRecordRefreshResult

/-!
# Choice-independent native refresh preparation

Before the motif selector runs, the gather, bundle and offset workers and all
ordered demand workers already determine their report sequences. Their only
numerical width requirement is that the sum of the old port widths fits a word.
The post-memory contains the exact demand at every block of the current graph.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.PortRefresh.Scheduled
open BurstRAM PrimedStackRAM Compression Compression.Refresh Compression.DegreeRefresh SpectralGeometry
open LevelRecipe NewSlots Allocation SourceTransport
open private lift_bounds from OAI.Computability.VPVNP.CompressorRefreshVerifiedStages
open private prepare_memory from OAI.Computability.VPVNP.CompressorRecordRefreshBuild

variable {w a a₀ g dH t : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}
variable (X : State a (a+g)) (E : RegularArcGraph (Fin (2^a)) dH) (hdH : 0 < dH)
  (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K') (hd : dH+1 ≤ 2^a₀)
  (ties : Fin t ≃ Tie (2^a)) (old : IncidenceDirectory w) (start stride : ℕ)
local notation "P" => plan X a₀ dH t stride start
local notation "Q" => Plan.scratch P w
local notation "S₀" => shape (t := t) E hdH conn F stride
local notation "J" => Stage S₀
local notation "D" => word (bits := w) (Plan.demand P)
local notation "Lₙ" => word (bits := w) (2^g)
local notation "term" => TermWorker.motifPass F ties (2^a*dH)
local notation "termData" => TermWorker.motifData F ties finProdFinEquiv.symm w
local notation "checks" => StageBounds (t := t) X E hdH conn F start stride

/-- The fixed deterministic worker, initialized from the current public bank, before any choice tape. -/
def PreSource (cap : ℕ) (j : J) (m : Memory w) (rs : List (Report w)) : Prop :=
  let data := fun z ↦ j.nativeBank hd E ties X start old termData (Fin.cast (j.worker_params hd term) z)
  let M := ((j.worker hd term).table.instantiate w data).program
  runSegment M (fuel hd cap j) (some (word j.first)) m (List.replicate (j.limit X start-j.first) []) = some rs

local notation "src" => PreSource X E hdH conn F hd ties old start stride

private theorem pre_demands (low cap : ℕ) (lo : low ≤ start) (room : (P).stop < 2^w)
    {js : List (Fin t)} {m : Memory w} {rs : List (Report w)}
    (h : DemandScan.Runs (DemandScan.words (r := 2^g) ties Q D) (P).blocks js m rs) :
    SourceWalk (fun j mem logs ↦ src cap j mem logs ∧ checks low j mem logs) (js.map Stage.demand) m rs := by
  induction h with
  | nil => exact .done _
  | cons i run _ ih =>
    have s := TermDataFrame.demand_trace X a₀ dH stride start ties room i _ _ run
    exact .next ⟨run,lift_bounds s (fun _ h ↦ lo.trans h.1) (fun _ h ↦ h)⟩ ih

/-- Prepare the actual numerical selector input without a selected term. Each raw
worker comes with its physical bank, ordinal guard, reads above `low`, and writes
only within this level. The report list and demand post-memory are the same ones
used by `Build.Run` and its reverse enumeration. -/
theorem prepare_verified (low cap : ℕ) (L : PrepareLayout X old a₀ dH t stride start)
    (m : Memory w) (rep : old.Represents X m) (above : ∀ j, low ≤ (old.column j).val)
    (before : ∀ j, (old.column j).val+(P).segments ≤ start) (room : (P).stop < 2^w)
    (totalFit : 2^a*X.maxWireWidth < 2^w) :
    ∃ pre : List (Report w), let post := after m (eventLog pre)
      SourceWalk (fun j mem logs ↦ src cap j mem logs ∧ checks low j mem logs)
        ([.gather,.bundles,.offsets] ++ (List.finRange t).map Stage.demand) m pre ∧
      PrepareRun X old Q D ties Lₙ L.regions.fits m post pre ∧ SegmentFields X Q L.regions.fits post ∧
      (∀ s, DemandPreparation.demandAt ties (DemandScan.rowBase X t D s) post =
        blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) s) ∧
      (∀ x, outsideLevel Q (P).segments x → (x < (D).val ∨ (D).val+(P).blocks*t ≤ x) → post x = m x) ∧
      RAMBuckets.cost Report.probes pre = 6*(P).sites+12*(P).segments+3*(P).blocks*t := by
  have widths b := (Build.bundle_total_le_max X b).trans_lt totalFit
  obtain ⟨pre,post,pr,sg,dem,frame,cost⟩ := prepare_demands X old Q D ties m rep Lₙ L.degree L.lanes
    L.regions L.directory L.gather L.baseApart widths L.demandRoom L.demandApart
  have hp := prepare_memory X ties old pr
  subst post
  refine ⟨pre,?_,pr,sg,dem,frame,cost⟩
  obtain ⟨rg,rd,re,ds,ext,runs,_,rfl⟩ := pr
  have h := FrontFrame.external_scans X old a₀ dH t stride start before room widths m rep rg rd re L.regions.fits ext
  have lo := (above 0).trans ((Nat.le_add_right ..).trans (before 0))
  have oldRead (x) (cell : FrontFrame.OldCell old (P).segments x) : low ≤ x := by
    obtain ⟨j,hj,_⟩ := cell
    exact (above j).trans hj
  have arenaRead (x) (cell : TermDataFrame.InArena P x) := lo.trans cell.1
  have ⟨hg,hb,he,_⟩ := ext
  have first : SourceWalk (fun j mem logs ↦ src cap j mem logs ∧ checks low j mem logs) [.gather,.bundles,.offsets]
      m (rg++rd++re) := by
    rw [List.append_assoc]
    exact .next ⟨hg,lift_bounds h.1 oldRead (fun _ h ↦ h)⟩ (.next ⟨hb,lift_bounds h.2.1 oldRead (fun _ h ↦ h)⟩
      (.singleton ⟨he,lift_bounds h.2.2 arenaRead (fun _ h ↦ h)⟩))
  have demandWalk := pre_demands X E hdH conn F hd ties old start stride low cap lo room runs
  exact first.append (by simpa only [SourceWalk.after_append] using demandWalk)

end CompressorRecords.PortRefresh.Scheduled

end

end VPVNP
end Computability
end OAI
