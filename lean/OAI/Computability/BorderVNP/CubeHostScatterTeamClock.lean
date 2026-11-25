import OAI.Computability.BorderVNP.CubeHostScatterIncidence
import OAI.Computability.BorderVNP.CubeTeamRowClock
import OAI.Computability.BorderVNP.CubeTeamBudgetGuard

/-! # Charging the native host scatter to the physical team budget of Section 8.2

A cable can charge both ends to one team. The public owner table assigns those
ends to coordinate symbols, and the native group schedule charges one millionth
of each padded raw wire to the corresponding symbol. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open Physical RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- The physical directed bins and stored owner words associated with the host cable rows. -/
structure Layout.ScheduledCables (l : Layout) (before : ℕ → ℕ) {n d : ℕ}
    (capacity : ℕ) (axis : Fin (n+1)) (owner : Fin d → ℕ) where
  /-- Directed endpoint labels of the cables in their actual row order. -/
  pair : Fin l.count → Label (n+1) d × Label (n+1) d
  /-- The total live cable width of a bin fits its padded block interval. -/
  binFit : ∀ p, Physical.load pair (l.liveWidth before) p ≤ capacity
  /-- For every positive-width crossing cable the physical cell owners agree with the schedule. -/
  owners : ∀ j : Fin l.count, l.width before j ≠ 0 → l.cell before j false ≠ l.cell before j true →
    l.owner before j false = owner ((pair j).1 axis) ∧ l.owner before j true = owner ((pair j).2 axis)

variable {g : GroupWeights.Layout} {teams : TeamNative.Layout} {orig assigned : ℕ → ℕ}
variable {n blocks b K h : ℕ} {D : LengthDeclaration n g.groups}
variable {A : Type*} [Fintype A] {label : Fin g.cells → Label (n+1) g.groups}
variable {recv : A → Fin g.cells} {incoming : A → ℕ}

/-- Actual owned endpoint incidence is at most twice the exterior limit in integer
millionths, using the stored load of the team executing this frame. -/
theorem Layout.incident_le_teamLimit (l : Layout) (before : ℕ → ℕ)
    (schedule : GroupWeights.ScheduleResult g teams orig assigned)
    (image : GroupWeights.PhysicalImage g orig blocks b K h D label recv incoming)
    (team : Fin (teams.r+1)) (teamEq : l.team = team.val)
    (rows : l.ScheduledCables before (blocks*(h*b)) D.1 (fun u : Fin g.groups => assigned (teams.owners+u.val)))
    (X : ℕ) (cap : TeamNative.unscale (assigned (teams.totals+team.val)) ≤ (X : ℚ)/256) :
    l.incident before ≤ 2*(1000000*X/256) := by
  have raw := l.incident_le_raw before D.1 rows.pair
    (fun u : Fin g.groups => assigned (teams.owners+u.val)) rows.binFit rows.owners
  rw [teamEq] at raw
  have stored := TeamRowClock.ownedRaw_le_stored schedule image team
  have limit := (TeamBudget.Layout.le_teamLimit ⟨teams.r+1,X,teams.totals⟩ _).2 cap
  exact raw.trans (Nat.mul_le_mul_left 2 (stored.trans limit))

/-- A successful native budget guard supplies the exact rational cap on its stored
team-total word. This also covers equality at the rounded integer threshold. -/
theorem teamCap_of_budget_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (budget : TeamBudget.Layout) (s : Bank w) (m : Memory w)
    (fields : budget.Fields (readings pub 0) (readings m)) (fit : budget.Fits (readings pub 0) w)
    {es : List (TeamRAM.Event w)} {t : Bank w} {mt : Memory w}
    (run : Runs pub macros TeamBudget.check s m es t mt) (team : Fin budget.teams) :
    TeamNative.unscale (readings m (budget.totals+team.val)) ≤ (budget.X₀ : ℚ)/256 := by
  have passed := ((TeamBudget.check_test pub macros budget s m fields fit).sound run).1
  exact (budget.le_teamLimit _).1 (passed.1 team.val team.isLt)

/-- The complete decoded-frame scatter executes within the physical exterior clock,
including the setup and the two endpoint tests for every public cable row. -/
theorem run_fromFrame_teamClock {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (schedule : GroupWeights.ScheduleResult g teams orig assigned)
    (image : GroupWeights.PhysicalImage g orig blocks b K h D label recv incoming)
    (team : Fin (teams.r+1)) (X : ℕ)
    (cap : TeamNative.unscale (assigned (teams.totals+team.val)) ≤ (X : ℚ)/256) :
    let before := readings m
    let base := readings pub 0
    let l := Layout.fromFrame base before
    l.team = team.val → l.ScheduledCables before (blocks*(h*b)) D.1 (fun u : Fin g.groups => assigned (teams.owners+u.val)) →
    l.Fits w before → base+94 < 2^w → before (base+63)+8 < 2^w →
    BoundedRun pub macros program s m (68+82*l.count+44*(1000000*X/256)) (fun z =>
      l.Ready z ∧ z.reg 13 = l.count ∧ z.mem = l.prefix before l.count) := by
  intro before base l teamEq rows fit frameFit headerFit
  have bound := l.incident_le_teamLimit before schedule image team teamEq rows X cap
  apply (run_fromFrame pub macros s m fit frameFit headerFit).mono _ (fun _ hz => hz)
  change 68+82*l.count+22*l.incident before ≤ 68+82*l.count+44*(1000000*X/256)
  omega

/-- A team that returns from the actual budget guard can start the scatter in the
guard's resulting register bank and memory, with no separate assumption on its load. -/
theorem run_after_budget_check {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (schedule : GroupWeights.ScheduleResult g teams orig (readings m))
    (image : GroupWeights.PhysicalImage g orig blocks b K h D label recv incoming)
    (team : Fin (teams.r+1)) (X : ℕ) {es : List (TeamRAM.Event w)} {t : Bank w} {mt : Memory w}
    (guard : Runs pub macros TeamBudget.check s m es t mt) :
    let before := readings m
    let base := readings pub 0
    let l := Layout.fromFrame base before
    let budget := TeamBudget.Layout.mk (teams.r+1) X teams.totals
    budget.Fields base before → budget.Fits base w → l.team = team.val →
    l.ScheduledCables before (blocks*(h*b)) D.1 (fun u : Fin g.groups => before (teams.owners+u.val)) →
    l.Fits w before → base+94 < 2^w → before (base+63)+8 < 2^w →
    BoundedRun pub macros program t mt (68+82*l.count+44*(1000000*X/256)) (fun z =>
      l.Ready z ∧ z.reg 13 = l.count ∧ z.mem = l.prefix before l.count) := by
  intro before base l budget fields budgetFit teamEq rows fit frameFit headerFit
  have cap := teamCap_of_budget_run pub macros budget s m fields budgetFit guard team
  have preserved : readings mt = readings m :=
    ((TeamBudget.check_test pub macros budget s m fields budgetFit).sound guard).2
  have eq : mt = m := funext fun a => Fin.ext (congrFun preserved a)
  subst mt
  exact run_fromFrame_teamClock pub macros t m schedule image team X cap teamEq rows fit frameFit headerFit

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
