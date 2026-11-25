import OAI.Computability.BorderVNP.CubeRouteIncidentSum
import OAI.Computability.BorderVNP.CubeRouteIncidentLoad
import OAI.Computability.BorderVNP.CubeHostScatterTeamClock

/-! # The physical two-hop link capacity at the signed evaluator's routing seam -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.RouteRecords

open Physical RoutingISA Finset Filter VPVNP.BurstRAM

variable {l : GroupWeights.Layout} {teams : TeamNative.Layout} {orig assigned : ℕ → ℕ}
variable {a blocks b K h : ℕ} {decl : LengthDeclaration a l.groups}
variable {A : Type*} [Fintype A] {label : Fin l.cells → Label (a+1) l.groups} {recv : A → Fin l.cells} {width : A → ℕ}

/-- At any team the real data and shared table has at most its outgoing literal
allocation plus one checked load of incident shared and incoming bits. -/
theorem table_exterior_le (sched : GroupWeights.ScheduleResult l teams orig assigned)
    (image : GroupWeights.PhysicalImage l orig blocks b K h decl label recv width)
    (dir : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (order : Fin (dir.directory pp lp).length ≃ A)
    (sizes : ∀ j : Fin (dir.directory pp lp).length, (dir.directory pp lp)[j.val].width = width (order j))
    (owner : ℕ → Fin (teams.r+1)) (group : Fin l.groups → Fin (teams.r+1))
    (cells : ∀ j : Fin (dir.directory pp lp).length, owner (dir.directory pp lp)[j.val].cell = group (label (recv (order j)) decl.1))
    (owners : ∀ x : Fin l.groups, assigned (teams.owners+x.val) = (group x).val)
    (procs : 0 < dir.processors) (fields : 0 < dir.fields) (block : 0 < dir.block)
    (X : ℕ) (team : Fin (teams.r+1)) (cap : TeamNative.unscale (assigned (teams.totals+team.val)) ≤ (X:ℚ)/256) :
    let data := dir.directory pp lp
    (∑ i ∈ range (data.length+l.groups.choose 2),
      (combinedRow data owner blocks K h decl group i).exteriorWidth team.val) ≤
      (dir.fields+1)*(dir.processors*dir.literal)+X/256 := by
  intro data
  rw [← Fin.sum_univ_eq_sum_range]
  have bound := incident_le data owner blocks K h decl group (fun j => label (recv (order j)) decl.1) cells team
  apply bound.trans
  apply Nat.add_le_add (dir.populated_outgoing pp lp team.val procs fields block)
  simp_rw [incoming_compact data order label recv width sizes decl.1]
  exact charge_le_teamLimit sched image group owners team X cap

/-- The successful native budget check, the literal source layout and the
rounded link scale furnish the capacity required by every physical scheduler
pair, using the actual published data and strict-row table. -/
theorem capacity_of_budget_return {α ξ : ℝ} {n w : ℕ}
    (calibrated : FitsLinksAt α ξ n) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (regs : Bank w) (m : Memory w) (sched : GroupWeights.ScheduleResult l teams orig (readings m))
    (image : GroupWeights.PhysicalImage l orig blocks b K h decl label recv width)
    (dir : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (order : Fin (dir.directory pp lp).length ≃ A)
    (sizes : ∀ j : Fin (dir.directory pp lp).length, (dir.directory pp lp)[j.val].width = width (order j))
    (owner : ℕ → Fin (teams.r+1)) (group : Fin l.groups → Fin (teams.r+1))
    (cells : ∀ j : Fin (dir.directory pp lp).length, owner (dir.directory pp lp)[j.val].cell = group (label (recv (order j)) decl.1))
    (owners : ∀ x : Fin l.groups, readings m (teams.owners+x.val) = (group x).val)
    (tab : TableLayout) (total : tab.count = (dir.directory pp lp).length+l.groups.choose 2)
    (teamCount : teams.r+1 = tab.teams) (hR : 2 < tab.teams) (f : BroadcastFrame)
    (procs : 0 < dir.processors) (fields : 0 < dir.fields) (fields_le : dir.fields ≤ 2) (block : 0 < dir.block)
    (proc_eq : dir.processors = f.processors) (literal : dir.literal ≤ TeamScales.literal α n)
    (teamRoom : (tab.teams : ℝ) ≤ (n:ℝ)^(2*α)) (headerRoom : (f.header : ℝ) ≤ f.processors*(n:ℝ)^(24/25:ℝ))
    (link : f.link = TeamScales.link ξ tab.teams n) :
    let X := TeamScales.exterior ξ f.processors n
    let budget : TeamBudget.Layout := ⟨teams.r+1,X,teams.totals⟩
    let rows := combinedRow (dir.directory pp lp) owner blocks K h decl group
    tab.RowsFit w rows → budget.Fields (readings pub 0) (readings m) → budget.Fits (readings pub 0) w →
    ∀ {es t mt}, Runs pub mac TeamBudget.check regs m es t mt →
      ∀ u v, f.header + Routing.legLoad hR (tab.widthMatrix rows) u v +
        Routing.legLoad hR (tab.widthMatrix rows) v u ≤ f.capacity := by
  intro X budget rows fitted guardFields guardFit es t mt run
  apply calibrated tab rows (fun i hi => (fitted.labels i hi).2) hR f (proc_eq ▸ procs) teamRoom headerRoom link
  intro u
  let j : Fin (teams.r+1) := Fin.cast teamCount.symm u
  have cap := HostScatter.teamCap_of_budget_run pub mac budget regs m guardFields guardFit run j
  have amount := table_exterior_le sched image dir pp lp order sizes owner group cells owners procs fields block X j cap
  have source : (dir.fields+1)*(dir.processors*dir.literal) ≤ 3*(f.processors*TeamScales.literal α n) :=
    Nat.mul_le_mul (by omega) (proc_eq ▸ Nat.mul_le_mul_left dir.processors literal)
  rw [total]
  exact amount.trans (Nat.add_le_add_right source _)

end Cube.RouteRecords

end BorderVNP
end Computability
end OAI
