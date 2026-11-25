import OAI.Computability.BorderVNP.DiagonalOwnedReportSourceWords

/-! # Source words for one returned report and the other teams' host copies -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.ReceivedRows

open VPVNP.BurstRAM Crossing Packing Packing.Directory Packing.CellAddresses
open RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep FiniteEvaluator
open Diagonal.ExternalSew Diagonal.ExternalSew.Fragments DiagonalTallyCellReports DiagonalTallyAllocation
open scoped Classical

variable {D R r t link tiles g ne np C teams w : ℕ}
    {l : Fin teams → ReportLayout} (roster : ReceivedRows l C)
    (N : Network D (FreeBlock R tiles) (fun _ => g)) (cell : N.Site → Fin C)
    (edgeID : N.Edge ↪ Fin ne) (portID : FreeBlock R tiles ↪ Fin np)
    (hg : 0<g) (space : r*(2*t+R*link)≤tiles*g) (lp : ℕ → ℕ × ℕ)
    (origin stride : ℕ) (input : FreePort R r t → Bool) (ends : Bool → LiveBit N cell → Bool)
    {pub : Fin teams → Arg → Word w} {mac : Fin teams → TeamOpcode.Macros w 8}
    {s : Fin teams → Bank w} {m : Fin teams → Memory w}
    (a : CubeArena.Layout) (H : Fin teams → OpenSuffix.Inputs)
    {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    {q : ReportCursor} {description : ℕ}
local notation3 (prettyPrint := false) "src" c => (roster.order.symm c).1

/-- Other teams' native host copies already supply the endpoints and literals
needed to fit this team's reported rows. They need no local report choices. -/
theorem sourceWords_one_report (u : Fin teams) (cut : ReportsThrough (pub u) (mac u) (s u) (m u))
    (placement : LivePlacement N cell edgeID portID lp)
    (ready : ∀ v, OpenSuffix.Ready (H v) (pub v 0).val (readings (m v)) w)
    (placed : OpenSuffix.Placement (H u) a pre (pub u 0).val (readings (m u)))
    (alloc : ReportAllocation pre post banks (l u) (roster.cells u) q)
    (seed : PreparedReportInput (pub u) cut.controls.val.2.2 (roster.cells u) q description)
    (base : banks.bankStart=origin) (step : banks.stride=stride)
    (widths : ∀ i : Fin (roster.cells u).length,
      ((roster.cells u).get i).supplied=suppliedSize N cell (roster.order ⟨u,i⟩))
    (source : SourceWords N cell edgeID portID hg space lp origin stride input ends
      (fun c => OpenSuffix.hostImage (pub (src c) 0).val (readings (m (src c))))) :
    ∃ memories : Fin teams → Memory w, memories u=cut.reports.val.2.2 ∧
      (∀ v, v≠u → readings (memories v)=OpenSuffix.hostImage (pub v 0).val (readings (m v))) ∧
      SourceWords N cell edgeID portID hg space lp origin stride input ends
        (fun c => readings (memories (src c))) := by
  classical
  have copies (v : Fin teams) : ∃ out : Memory w, readings out=OpenSuffix.hostImage (pub v 0).val (readings (m v)) := by
    obtain ⟨_,_,out,_,_,_,_,eq⟩ := HostScatter.run_fromFrame (pub v) (mac v) (s v) (m v)
      (ready v).host (ready v).frameRoom (ready v).headerRoom
    exact ⟨out,eq⟩
  let mem (v : Fin teams) := if v=u then cut.reports.val.2.2 else (copies v).choose
  have same : mem u=cut.reports.val.2.2 := by simp [mem]
  have other (v : Fin teams) (h : v≠u) :
      readings (mem v)=OpenSuffix.hostImage (pub v 0).val (readings (m v)) := by
    simpa [mem,h] using (copies v).choose_spec
  refine ⟨mem,same,other,?_⟩
  apply SourceWords.protected N cell edgeID portID hg space lp origin stride input ends source placement
  intro c j small
  obtain ⟨⟨v,i⟩,rfl⟩ := roster.order.surjective c
  simp only [Equiv.symm_apply_apply]
  by_cases h : v=u
  · subst v
    rw [same]
    have b := (alloc.receiving ((roster.cells u).get i) (List.get_mem _ _)).1
    rw [CellBanks.Layout.bank,base,step,roster.number] at b
    have within := small.trans_eq (widths i).symm
    have kept := cut.report_host_word a (H u) (ready u) placed alloc seed i ⟨j,within⟩
    change (roster.cells u)[i.val].external=origin+(roster.order ⟨u,i⟩).val*stride at b
    rwa [b] at kept
  · exact congrFun (other v h) _

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
