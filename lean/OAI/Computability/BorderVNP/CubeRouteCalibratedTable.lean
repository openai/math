import OAI.Computability.BorderVNP.CubeRouteScheduledGuard

/-! # Physical table widths and link capacity from the native group-prefix return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.RouteRecords

open Physical VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator

variable {l : GroupWeights.Layout} {teams : TeamNative.Layout} {orig : ℕ → ℕ}
variable {a blocks b K h w : ℕ} {decl : LengthDeclaration a l.groups}
variable {A : Type*} [Fintype A] {label : Fin l.cells → Label (a+1) l.groups} {recv : A → Fin l.cells} {width : A → ℕ}
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {r t : Bank w}
variable {m mt : Memory w} {events : List (TeamRAM.Event w)}

/-- The actual group guard in the native prefix bounds the total width of the physical records
and both directions of every routed link. No second execution of the guard is required. -/
theorem groupPrefix_table_room {α ξ : ℝ} {scale bits : ℕ} (calibrated : FitsLinksAt α ξ scale)
    (f : BroadcastFrame) (base : (pub 0).val = l.frame)
    (setup : GroupWeights.CheckedFrame l teams orig w (TeamScales.exterior ξ f.processors scale))
    (prefixRun : Runs pub mac (LocalRow.groupPrefix a bits) r m events t mt)
    (sched : GroupWeights.ScheduleResult l teams orig (readings mt))
    (image : GroupWeights.PhysicalImage l orig blocks b K h decl label recv width)
    (dir : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (order : Fin (dir.directory pp lp).length ≃ A)
    (sizes : ∀ i : Fin (dir.directory pp lp).length, (dir.directory pp lp)[i.val].width = width (order i))
    (owner : ℕ → Fin (teams.r+1)) (group : Fin l.groups → Fin (teams.r+1))
    (cells : ∀ i : Fin (dir.directory pp lp).length, owner (dir.directory pp lp)[i.val].cell = group (label (recv (order i)) decl.1))
    (owners : ∀ x : Fin l.groups, readings mt (teams.owners+x.val) = (group x).val)
    (tab : TableLayout) (total : tab.count = (dir.directory pp lp).length+l.groups.choose 2)
    (teamCount : teams.r+1 = tab.teams) (hR : 2 < tab.teams) (senders : dir.teams = teams.r+1)
    (storage : dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2))
    (procs : 0 < dir.processors) (fields : 0 < dir.fields) (fields_le : dir.fields ≤ 2) (block : 0 < dir.block)
    (procEq : dir.processors = f.processors) (literal : dir.literal ≤ TeamScales.literal α scale)
    (teamRoom : (tab.teams : ℝ) ≤ (scale:ℝ)^(2*α)) (headerRoom : (f.header : ℝ) ≤ f.processors*(scale:ℝ)^(24/25:ℝ))
    (link : f.link = TeamScales.link ξ tab.teams scale) :
    let rows := combinedRow (dir.directory pp lp) owner blocks K h decl group
    tab.RowsFit w rows ∧ ∀ u v, f.header+Routing.legLoad hR (tab.widthMatrix rows) u v+
      Routing.legLoad hR (tab.widthMatrix rows) v u ≤ f.capacity := by
  intro rows
  obtain ⟨_,_,reg,_,guard⟩ := groupPrefix_budget_return prefixRun
  obtain ⟨inputs,fits⟩ := scheduled_budget_frame setup sched base
  let budget : TeamBudget.Layout := ⟨teams.r+1,TeamScales.exterior ξ f.processors scale,teams.totals⟩
  have passed := ((TeamBudget.check_test pub mac budget reg mt inputs fits).sound guard).1
  have volume : (∑ i : Fin (dir.directory pp lp).length, (dir.directory pp lp)[i.val].width) = ∑ x, width x := by
    simp_rw [sizes]
    exact order.sum_comp width
  have good := rowsFit_of_schedule dir pp lp procs fields storage owner group image sched passed (budgetLimit_fit fits)
    volume tab total teamCount senders
  exact ⟨good,capacity_of_budget_return calibrated pub mac reg mt sched image dir pp lp order sizes owner group cells owners
    tab total teamCount hR f procs fields fields_le block procEq literal teamRoom headerRoom link good inputs fits guard⟩

end Cube.RouteRecords

end BorderVNP
end Computability
end OAI
