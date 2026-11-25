import OAI.ThreeFlat.Diagonal.HistorySelectedChronology
import OAI.ThreeFlat.RAM.HistorySelectedInterior

namespace OAI
/-! # Source records of the terminal root actually chosen from the S44 chronology -/
noncomputable section
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open RAM RAM.HistoryStageBody.Physical RAM.HistoryCompiledRows Computability.VPVNP.BurstRAM PrivateRAM

private theorem records_eq {F : Type} {W a b : ℕ} (tag : ((Fin 3→Bool)→F)→ℕ)
    (X : BitNetwork F a) (Y : BitNetwork F b) (pins : a=b) (network : HEq X Y)
    (stream : ℕ) (m : Memory W) (rows : Records tag X stream m) : Records tag Y stream m := by
  subst b
  cases eq_of_heq network
  exact rows

private theorem network_sizes {F : Type} {a b : ℕ} (X : BitNetwork F a) (Y : BitNetwork F b)
    (pins : a=b) (network : HEq X Y) : X.cells=Y.cells ∧ X.internal=Y.internal := by
  subst b
  cases eq_of_heq network
  exact ⟨rfl,rfl⟩

variable {F Pins : Type} [Field F] {d l W age : ℕ} {A : State d l}
variable (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (N : Forest F L.ports.form) (C : r.Charges) (O : A.ArchiveSites)
    (path : r.ArchivePath h C O) (zero : O.layer.first=0)
    (v : (r.plan.finish h).Site) (pointer : (Σ u : A.Site,Fin (L.ext u))→ℕ)
    (tag : ((Fin 3→Bool)→F)→ℕ) (m : Memory W)
local notation "i" => r.archivePlanIndex h C O path v
local notation "node" => r.archiveNode h J L N C O path zero i
local notation "stream" => streamAt age O.layer.count (Fin.val i)
local notation "ends" => endsAt age O.layer.count (Fin.val i)
local notation "result" => r.plan.assemble h (r.wordAssembly J L) N

/-- The ordinal is computed by the authentic finalLayer numbering. For each
four-word row the source is the same compiled tree appearing in the factor
forest, including its coefficient identifier. -/
theorem terminal_rows (cached : (NodeValue.ofSite node pointer stream ends).Cached tag age (i).val m) :
    Records tag ((result).2 v).compile stream m := by
  obtain ⟨width,net⟩:=r.archivePlanNetwork h J L N C O path zero v
  exact records_eq tag (node).net ((result).2 v).compile width net stream m cached.rows

/-- The four S13 fields read by the five-word producer give the same S12
source and arity, row and hidden-bit counts as the later gathered tree. -/
theorem terminal_chart (cached : (NodeValue.ofSite node pointer stream ends).Cached tag age (i).val m) :
    let root:=TickWorkspace.base age 13+8*(i).val
    (m root).val=stream ∧ (m (root+1)).val=(result).1.width v ∧
      (m (root+2)).val=((result).2 v).compile.cells ∧
      (m (root+3)).val=((result).2 v).compile.internal := by
  intro root
  obtain ⟨width,net⟩:=r.archivePlanNetwork h J L N C O path zero v
  obtain ⟨cells,bits⟩:=network_sizes (node).net ((result).2 v).compile width net
  have h0:=congrArg HistoryStageRoot.Result.stream cached.header
  have h1:=congrArg HistoryStageRoot.Result.pins cached.header
  have h2:=congrArg HistoryStageRoot.Result.rows cached.header
  have h3:=congrArg HistoryStageRoot.Result.bits cached.header
  exact ⟨h0,h1.trans width,h2.trans cells,h3.trans bits⟩

end Hierarchy.TraceFactorReceiver.Gather
end

end OAI
