import OAI.Computability.BorderVNP.DiagonalReturnedHostSupply
import OAI.Computability.BorderVNP.DiagonalPositiveCoreReceived

/-! # Source-word authentication on all of the true owner report returns -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.ReceivedRows

open VPVNP.BurstRAM Crossing Packing Packing.Directory Packing.CellAddresses
open RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep FiniteEvaluator
open Diagonal.ExternalSew Diagonal.ExternalSew.Fragments DiagonalTallyCellReports DiagonalTallyAllocation
open scoped Classical

variable {D R r t link tiles g ne np C teams dim box lanes copies symbols w : ℕ}
    {l : Fin teams → ReportLayout} (roster : ReceivedRows l C)
    (N : Network D (FreeBlock R tiles) (fun _ => g)) (cell : N.Site → Fin C)
    (edgeID : N.Edge ↪ Fin ne) (portID : FreeBlock R tiles ↪ Fin np)
    (hg : 0<g) (space : r*(2*t+R*link)≤tiles*g) (lp : ℕ → ℕ × ℕ)
    (origin stride : ℕ) (input : FreePort R r t → Bool) (ends : Bool → LiveBit N cell → Bool)
    {pub : Fin teams → Arg → Word w} {mac : Fin teams → TeamOpcode.Macros w 8}
    {s : Fin teams → Bank w} {m : Fin teams → Memory w}
    (scans : ∀ u, ReportsThrough (pub u) (mac u) (s u) (m u))
    {id : TableEntry dim box lanes copies symbols → ℕ}
    (visits : ∀ u, Visits id (pub u) (mac u) (s u) (m u))
    (a : CubeArena.Layout) (H : Fin teams → OpenSuffix.Inputs)
    {pre : Fin teams → BeforeTasks} {post : Fin teams → AfterTasks} {banks : Fin teams → CellBanks.Layout}
    {q : Fin teams → ReportCursor} {description : Fin teams → ℕ}
local notation3 (prettyPrint := false) "src" c => (roster.order.symm c).1

/-- The endpoint and literal bits on the host-scatter image may be read
from the physical report return in the owning team. Ownership and the
reader’s compact ordinal use the same global bijection, including when
a team has no receiving cells. -/
theorem sourceWords_through_reports (placement : LivePlacement N cell edgeID portID lp)
    (ready : ∀ u, OpenSuffix.Ready (H u) (pub u 0).val (readings (m u)) w)
    (placed : ∀ u, OpenSuffix.Placement (H u) a (pre u) (pub u 0).val (readings (m u)))
    (alloc : ∀ u, ReportAllocation (pre u) (post u) (banks u) (l u) (roster.cells u) (q u))
    (seed : ∀ u, PreparedReportInput (pub u) (scans u).controls.val.2.2 (roster.cells u) (q u) (description u))
    (origins : ∀ u, (banks u).bankStart=origin) (strides : ∀ u, (banks u).stride=stride)
    (widths : ∀ u (i : Fin (roster.cells u).length), ((roster.cells u).get i).supplied=suppliedSize N cell (roster.order ⟨u,i⟩))
    (source : SourceWords N cell edgeID portID hg space lp origin stride input ends
      (fun c => OpenSuffix.hostImage (pub (src c) 0).val (readings (m (src c))))) :
    SourceWords N cell edgeID portID hg space lp origin stride input ends
      (fun c => readings (scans (src c)).reports.val.2.2) := by
  apply SourceWords.protected N cell edgeID portID hg space lp origin stride input ends source placement
  intro c j hj
  obtain ⟨⟨u,i⟩,rfl⟩ := roster.order.surjective c
  simp only [Equiv.symm_apply_apply]
  have number := roster.number u i
  have base := ((alloc u).receiving ((roster.cells u).get i) (List.get_mem _ _)).1
  rw [CellBanks.Layout.bank,origins,strides,number] at base
  have small : j < (roster.cells u)[i.val].supplied := hj.trans_eq (widths u i).symm
  have keep := (scans u).report_host_word a (H u) (ready u) (placed u) (alloc u) (seed u) i ⟨j,small⟩
  change (roster.cells u)[i.val].external=origin+(roster.order ⟨u,i⟩).val*stride at base
  rw [base] at keep
  let c := roster.order ⟨u,i⟩
  let who := (roster.order.symm c).1
  let after (v : Fin teams) := (scans v).reports.val.2.2
  have home : who=u := congrArg Sigma.fst (roster.order.symm_apply_apply ⟨u,i⟩)
  change readings (after who) (origin+c.val*stride+j) =
    OpenSuffix.hostImage (pub u 0).val (readings (m u)) (origin+c.val*stride+j)
  rw [congrArg after home]
  exact keep


/-- The endpoint and literal bits on the host-scatter image may be read
from the physical report return in the owning team. Ownership and the
reader’s compact ordinal use the same global bijection, including when
a team has no receiving cells. -/
theorem sourceWords_after_reports (placement : LivePlacement N cell edgeID portID lp)
    (ready : ∀ u, OpenSuffix.Ready (H u) (pub u 0).val (readings (visits u).owned.val.2.2) w)
    (placed : ∀ u, OpenSuffix.Placement (H u) a (pre u) (pub u 0).val (readings (visits u).owned.val.2.2))
    (alloc : ∀ u, ReportAllocation (pre u) (post u) (banks u) (l u) (roster.cells u) (q u))
    (seed : ∀ u, PreparedReportInput (pub u) (visits u).controls.val.2.2 (roster.cells u) (q u) (description u))
    (origins : ∀ u, (banks u).bankStart=origin) (strides : ∀ u, (banks u).stride=stride)
    (widths : ∀ u (i : Fin (roster.cells u).length), ((roster.cells u).get i).supplied=suppliedSize N cell (roster.order ⟨u,i⟩))
    (source : SourceWords N cell edgeID portID hg space lp origin stride input ends
      (fun c => OpenSuffix.hostImage (pub (src c) 0).val (readings (visits (src c)).owned.val.2.2))) :
    SourceWords N cell edgeID portID hg space lp origin stride input ends
      (fun c => readings (visits (src c)).reports.val.2.2) := by
  exact roster.sourceWords_through_reports N cell edgeID portID hg space lp origin stride input ends
    (fun u => (visits u).throughReports) a H placement ready placed alloc seed origins strides widths source

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
