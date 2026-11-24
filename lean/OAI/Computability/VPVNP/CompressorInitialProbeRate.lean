import OAI.Computability.VPVNP.CompressorInitialScriptPackets
import OAI.Computability.VPVNP.CompressorIntervalCost

/-!
# Initial source and framed descriptor probe costs

There are three one-call metadata workers and one cursor call per actual
slot. Each cursor call writes six entries. The four scheduled phases also
each execute a calendar, planner, launcher and final stop call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.InitialProbeRate

open BurstRAM DescriptorSpace BlockPlanner BlockHeaderRun BlockInitialPackets Schedule
open scoped Fin.CommRing

variable {w : ℕ}

/-- Position-independent part of the initial probe bound, accounting for scalar and pointer
publication at level zero. -/
def fixed (L : Layout) (a : ℕ) :=
  (Scalars.initialRow (.terminal a)).recipe.reads + (DescriptorHeads.publisher L.shape).recipe.reads +
    L.shape.tables + 16

theorem raw (L : Layout) (a b l width : ℕ) (m : Memory w) :
    let N := CursorRAM.rowCount b l a
    let rs := logs L a b l width m
    rs.length = N+3 ∧ RAMBuckets.cost Report.probes rs = 7*N+fixed L a := by
  intro N rs
  let base := header w L 0
  let row := Scalars.initialRow (.terminal a)
  let mid := initialMemory a L m
  have scalar := (RowRecipe.report_cost row.recipe (scalarPorts base) (base+6) m).2.1
  have head := (RowRecipe.report_cost (DescriptorHeads.publisher L.shape).recipe (headPorts base base) 0 mid).2.1
  change (scalarReport row (base+6) base m).probes = row.recipe.reads+6 at scalar
  change (headReport L 0 mid).probes = (DescriptorHeads.publisher L.shape).recipe.reads+(L.shape.tables+3+3) at head
  have scan : RAMBuckets.cost Report.probes (cursorLogs L w a b l width) = 7*N := CursorRAM.scan_cost ..
  have len : (cursorLogs L w a b l width).length = N := CursorRAM.scanReports_length ..
  have role : (BlockRoleZero.report w L).probes = 1 := rfl
  constructor
  · change (headLogs L a m++cursorLogs L w a b l width++[_]).length = _
    simp only [List.length_append,len,headLogs,List.length_cons,List.length_nil]; omega
  · change RAMBuckets.cost Report.probes (headLogs L a m++cursorLogs L w a b l width++[_]) = _
    rw [RAMBuckets.cost_append,RAMBuckets.cost_append,scan]
    change (1+(scalarReport row (base+6) base m).probes+(1+(headReport L 0 mid).probes+0)) +
      7*N + (1+(BlockRoleZero.report w L).probes+0) = 7*N + fixed L a
    rw [head,scalar,role]
    change _ = 7*N+(row.recipe.reads + (DescriptorHeads.publisher L.shape).recipe.reads + L.shape.tables + 16)
    omega

private theorem workers_length {d : ℕ} (C : Catalog d) (q : ℕ) (pt : Ports w) (j : Fin d)
    (m : Memory w) (rs : List (Report w)) : (Online.workerRows C q pt j m rs).length = rs.length := by
  induction rs generalizing m with
  | nil => rfl
  | cons r rs ih => simp only [Online.workerRows,List.length_cons,ih]

theorem length (A : Script) (pt : Ports w) (m : Memory w) (steps : List (Online.Run.Step A.size A.size w)) :
    (Online.Run.intervalLog A.plan pt m steps).length =
      (steps.flatMap (fun st ↦ st.row.reports)).length + 4*steps.length := by
  induction steps generalizing m with
  | nil => rfl
  | cons st rest ih =>
    simp only [Online.Run.intervalLog,List.length_append,Online.rowLog,Online.preparation,
      workers_length,List.flatMap_cons,List.length_cons,List.length_nil,ih]
    omega

/-- Source probes, the inner interval bound, and the exact six additional
frame reads per physical Fin11 call. The constants use only the finite
script and its geometry. -/
theorem framed (A : Script) (L : Layout) (a b l width cap : ℕ) (base : Word w) (m : Memory w)
    (steps : List (Online.Run.Step A.size A.size w)) (phases : steps.length = 4)
    (source : (steps.map (fun st ↦ st.row.reports)).flatten = logs L a b l width m)
    (run : Online.Run.Interval A.plan (Workspace.ports (arity A.catalog) base) cap m steps) :
    let N := CursorRAM.rowCount b l a
    let src := Online.Run.sourceCost steps
    let es := Online.Run.intervalLog A.plan (Workspace.ports (arity A.catalog) base) m steps
    let inner := RAMBuckets.cost Report.probes es
    let outer := RAMBuckets.cost Report.probes (OnlineWorkspace.framed base m es)
    src = 7*N+fixed L a ∧ es.length = N+19 ∧
      inner ≤ (7*N+fixed L a)*(arity A.catalog+3) + 4*(Online.Run.maxReads A.plan+4*arity A.catalog+26) ∧
      outer = inner+6*(N+19) := by
  intro N src es inner outer
  have concat : steps.flatMap (fun st ↦ st.row.reports) = logs L a b l width m := source
  obtain ⟨hlen,hcost⟩ := raw L a b l width m
  have sc : src = 7*N+fixed L a := (Online.Run.sourceCost_eq_flatMap steps).trans ((congrArg (RAMBuckets.cost Report.probes) concat).trans hcost)
  have el := length A (Workspace.ports (arity A.catalog) base) m steps
  change es.length = _ at el
  rw [concat,phases,hlen] at el
  have count : es.length = N+19 := by omega
  have bound := Online.Run.interval_cost_bound A.plan (Workspace.ports (arity A.catalog) base) steps m run
  change inner ≤ src*(arity A.catalog+3)+_ at bound
  have extra := (OnlineWorkspace.framed_effect base m es (some 0)).2.2
  change outer = 6*es.length+inner at extra
  rw [sc,phases] at bound
  exact ⟨sc,count,bound,by rw [extra,count,Nat.add_comm]⟩

open Compression in
theorem fixed_layout {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
    (base positions blocks a : ℕ) : fixed (BlockProgram.layout B base positions blocks) a =
      fixed (BlockProgram.layout B 0 0 0) a := rfl

end CompressorRecords.InitialProbeRate

end VPVNP
end Computability
end OAI
