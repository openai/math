import OAI.Computability.BorderVNP.CubeGroupWeightPhysicalSchedule
import OAI.Computability.BorderVNP.CubeTeamBudgetGuard

/-! # Checked native group schedules and their exact aggregate load -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Physical RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

private theorem loads_sum (r : ℕ) (ws : ℕ → ℕ) (k : ℕ) :
    (∑ j, TeamNative.loads r ws k j) = ∑ i ∈ Finset.range k, ws i := by
  induction k with
  | zero => simp [TeamNative.loads]
  | succ k ih =>
    let j := TeamNative.owner r ws k
    let x := TeamNative.loads r ws k
    change (∑ i, Function.update x j (x j + ws k) i) = _
    rw [Finset.sum_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase,
      Finset.sum_range_succ, ← ih]
    have h := Finset.add_sum_erase Finset.univ x (Finset.mem_univ j)
    change x j + ws k + ∑ u ∈ Finset.univ.erase j, x u = (∑ u, x u)+ws k
    omega

/-- The sum of the actual team-total words counts every group charge exactly once. -/
theorem ScheduleResult.aggregate {l : Layout} {teams : TeamNative.Layout} {orig mem : ℕ → ℕ}
    (result : ScheduleResult l teams orig mem) :
    (∑ i ∈ Finset.range (teams.r+1), mem (teams.totals+i)) =
      ∑ i ∈ Finset.range l.groups, l.weight orig i := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [result.totals, loads_sum]

/-- Aggregate physical cost represented by the written team totals. -/
theorem ScheduleResult.aggregate_physical {l : Layout} {teams : TeamNative.Layout}
    {orig mem : ℕ → ℕ} {n blocks b K h : ℕ} {D : LengthDeclaration n l.groups}
    {A : Type*} [Fintype A] {label : Fin l.cells → Label (n+1) l.groups}
    {recv : A → Fin l.cells} {w : A → ℕ} (result : ScheduleResult l teams orig mem)
    (image : PhysicalImage l orig blocks b K h D label recv w) :
    TeamNative.unscale (∑ i ∈ Finset.range (teams.r+1), mem (teams.totals+i)) =
      ∑ s, jointCost blocks b K h D label recv w s := by
  rw [result.aggregate,← Fin.sum_univ_eq_sum_range,TeamNative.unscale,Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  simpa [TeamNative.unscale, result.weights s.val s.isLt] using result.weight_physical image s

/-- The paper's physical aggregate and team bounds make the exact native
capacity predicates true on the output memory of an authentic schedule. -/
theorem ScheduleResult.passes_of_physical {l : Layout} {teams : TeamNative.Layout}
    {orig mem : ℕ → ℕ} {n blocks b K h : ℕ} {D : LengthDeclaration n l.groups}
    {A : Type*} [Fintype A] {label : Fin l.cells → Label (n+1) l.groups}
    {recv : A → Fin l.cells} {w : A → ℕ} (result : ScheduleResult l teams orig mem)
    (image : PhysicalImage l orig blocks b K h D label recv w) (X : ℕ)
    (caps : (∑ u, jointCost blocks b K h D label recv w u) ≤ ((X*(teams.r+1) : ℕ) : ℚ)/1024 ∧
      ∀ j : Fin (teams.r+1), TeamNative.unscale (mem (teams.totals+j.val)) ≤ (X : ℚ)/256) :
    (TeamBudget.Layout.mk (teams.r+1) X teams.totals).Passes mem := by
  rw [TeamBudget.Layout.passes_iff_rational]
  refine ⟨fun i hi => caps.2 ⟨i,hi⟩,?_⟩
  change TeamNative.unscale (∑ i ∈ Finset.range (teams.r+1), mem (teams.totals+i)) ≤ _
  rw [result.aggregate_physical image]
  simpa only [Nat.cast_mul] using caps.1

/-- Actual histogram and group assignment followed by the two independent capacity checks. -/
def checkedSchedule : Code := schedule.seq TeamBudget.check

/-- The native checks on the physical arrays agree with the mathematical group weights. -/
theorem ScheduleResult.passes_iff {l : Layout} {teams : TeamNative.Layout} {orig mem : ℕ → ℕ}
    (result : ScheduleResult l teams orig mem) (X₀ : ℕ) :
    let budget : TeamBudget.Layout := ⟨teams.r+1,X₀,teams.totals⟩
    budget.Passes mem ↔
      (∀ j, TeamNative.loads teams.r (l.weight orig) l.groups j ≤ budget.teamLimit) ∧
        (∑ i ∈ Finset.range l.groups, l.weight orig i) ≤ budget.totalLimit := by
  dsimp only [TeamBudget.Layout.Passes, TeamBudget.Layout.prefix]
  rw [result.aggregate]
  apply and_congr_left
  intro _
  exact ⟨fun h j => result.totals j ▸ h j.val j.isLt, fun h i hi => result.totals ⟨i,hi⟩ ▸ h ⟨i,hi⟩⟩

/-- From the verified schedule execution, the physical capacity test returns
exactly when the computed allocation obeys the per-team and aggregate bounds. -/
theorem checked_test {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (teams : TeamNative.Layout) (s : Bank w) (m : Memory w) (X₀ : ℕ)
    (hs : BoundedRun pub macros schedule s m (ticks l+TeamNative.assignmentTicks teams)
      (fun z => ScheduleResult l teams (readings m) z.mem))
    (budget : TeamBudget.Layout) (hb : budget = ⟨teams.r+1,X₀,teams.totals⟩)
    (fields : budget.Fields (readings pub 0) (readings m)) (fit : budget.Fits (readings pub 0) w)
    (separate : ∀ f ∈ ([1,31,76] : List ℕ),
      (∀ i < l.groups, readings pub 0+f ≠ l.weights+i) ∧
      (∀ j : Fin (teams.r+1), readings pub 0+f ≠ teams.totals+j.val) ∧
      (∀ i < l.groups, readings pub 0+f ≠ teams.owners+i)) :
    TestRun pub macros checkedSchedule s m
      (ticks l+TeamNative.assignmentTicks teams+(TeamBudget.setup.slots+budget.teams*(TeamBudget.row.slots+1)+1))
      ((∀ j, TeamNative.loads teams.r (l.weight (readings m)) l.groups j ≤ budget.teamLimit) ∧
        (∑ i ∈ Finset.range l.groups, l.weight (readings m) i) ≤ budget.totalLimit)
      (fun z => ScheduleResult l teams (readings m) z.mem) := by
  subst budget
  let cap : TeamBudget.Layout := ⟨teams.r+1,X₀,teams.totals⟩
  let ok := (∀ j, TeamNative.loads teams.r (l.weight (readings m)) l.groups j ≤ cap.teamLimit) ∧
    (∑ i ∈ Finset.range l.groups, l.weight (readings m) i) ≤ cap.totalLimit
  have stage (u : Bank w) (mu : Memory w) (hr : ScheduleResult l teams (readings m) (readings mu)) :
      TestRun pub macros TeamBudget.check u mu
        (TeamBudget.setup.slots+cap.teams*(TeamBudget.row.slots+1)+1) ok
        (fun z => ScheduleResult l teams (readings m) z.mem) := by
    have keep (f : ℕ) (hf : f ∈ ([1,31,76] : List ℕ)) :
        readings mu (readings pub 0+f) = readings m (readings pub 0+f) :=
      hr.other _ (separate f hf).1 (separate f hf).2.1 (separate f hf).2.2
    have fs : cap.Fields (readings pub 0) (readings mu) :=
      ⟨(keep 1 (by decide)).trans fields.teams,
       (keep 31 (by decide)).trans fields.X₀,(keep 76 (by decide)).trans fields.totals⟩
    apply (TeamBudget.check_test pub macros cap u mu fs fit).mono le_rfl (hr.passes_iff X₀)
    intro z hz
    rw [hz]
    exact hr
  exact ((hs.asTest schedule_deterministic).seq stage).mono le_rfl (Iff.of_eq (true_and ok)) (fun _ h => h)

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
