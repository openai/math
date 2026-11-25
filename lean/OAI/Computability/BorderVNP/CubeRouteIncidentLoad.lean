import OAI.Computability.BorderVNP.CubeGroupPhysicalRows
import OAI.Computability.BorderVNP.CubeTeamRowClock
import OAI.Computability.BorderVNP.CubeTeamBudgetFrame
import OAI.Computability.BorderVNP.TransmissionLegCapacity
import OAI.Computability.BorderVNP.PackedDirectoryBudget

/-! # Charging the complete physical exterior incidence to the native team limit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.RouteRecords

open Physical RoutingISA Finset Filter VPVNP.BurstRAM

variable {l : GroupWeights.Layout} {teams : TeamNative.Layout} {orig assigned : ℕ → ℕ}
variable {a blocks b K h : ℕ} {decl : LengthDeclaration a l.groups}
variable {A : Type*} [Fintype A] {label : Fin l.cells → Label (a+1) l.groups} {recv : A → Fin l.cells} {width : A → ℕ}

/-- Every shared width and every delivery into a group's cell is charged in full
to the actual team holding that group. The raw-wire contribution of the schedule
can only increase its stored load. -/
theorem charge_le_stored (sched : GroupWeights.ScheduleResult l teams orig assigned)
    (image : GroupWeights.PhysicalImage l orig blocks b K h decl label recv width)
    (group : Fin l.groups → Fin (teams.r+1)) (owners : ∀ x : Fin l.groups, assigned (teams.owners+x.val) = (group x).val)
    (team : Fin (teams.r+1)) :
    1000000*(∑ x : Fin l.groups, if group x = team then
      SharedRows.incident blocks K h decl x + incomingWidth label recv width decl.1 x else 0) ≤
      assigned (teams.totals+team.val) := by
  rw [Finset.mul_sum,TeamRowClock.stored_team_eq sched team]
  apply Finset.sum_le_sum
  intro x _
  simp only [owners,Fin.val_inj,sched.weights x.val x.isLt,image.weight_eq,GroupWeights.incidentWidth_eq_strict]
  by_cases e : group x = team <;> simp [e,TeamNative.scaledWeight]

/-- A passing native per-team limit bounds the sum of real incident shared and
incoming widths in ordinary (unscaled) bits, with the advertised integer rounding. -/
theorem charge_le_teamLimit (sched : GroupWeights.ScheduleResult l teams orig assigned)
    (image : GroupWeights.PhysicalImage l orig blocks b K h decl label recv width)
    (group : Fin l.groups → Fin (teams.r+1)) (owners : ∀ x : Fin l.groups, assigned (teams.owners+x.val) = (group x).val)
    (team : Fin (teams.r+1)) (X : ℕ) (cap : TeamNative.unscale (assigned (teams.totals+team.val)) ≤ (X:ℚ)/256) :
    (∑ x : Fin l.groups, if group x = team then
      SharedRows.incident blocks K h decl x + incomingWidth label recv width decl.1 x else 0) ≤ X/256 := by
  have charged := charge_le_stored sched image group owners team
  have lim := (TeamBudget.Layout.le_teamLimit ⟨teams.r+1,X,teams.totals⟩ _).mpr cap
  change assigned (teams.totals+team.val) ≤ 1000000*X/256 at lim
  omega

/-- A public ordering of the emitted data records preserves their full incoming
symbol sum, even when a delivery is split across processor boundaries. -/
theorem incoming_compact {A : Type*} [Fintype A] {n d : ℕ} {C : Type*}
    (data : List Packing.Directory.Row) (order : Fin data.length ≃ A) (label : C → Label (n+1) d)
    (recv : A → C) (width : A → ℕ) (sizes : ∀ j : Fin data.length, data[j.val].width = width (order j))
    (i : Fin (n+1)) (s : Fin d) :
    (∑ j : Fin data.length, if label (recv (order j)) i = s then data[j.val].width else 0) =
      incomingWidth label recv width i s := by
  simp_rw [sizes]
  exact order.sum_comp (fun x => if label (recv x) i = s then width x else 0)

/-- Capacity estimate for one length at the manuscript's rounded literal and link scales. -/
def FitsLinksAt (α ξ : ℝ) (n : ℕ) : Prop :=
    ∀ (tab : TableLayout) (row : ℕ → TableRow),
      (∀ i < tab.count, (row i).first < tab.teams ∧ (row i).second < tab.teams) →
      ∀ (hR : 2 < tab.teams) (f : BroadcastFrame), 1 ≤ f.processors →
      (tab.teams : ℝ) ≤ (n : ℝ)^(2*α) → (f.header : ℝ) ≤ f.processors*(n : ℝ)^(24/25 : ℝ) →
      f.link = TeamScales.link ξ tab.teams n →
      (∀ u : Fin tab.teams, (∑ i ∈ range tab.count, (row i).exteriorWidth u) ≤
        3*(f.processors*TeamScales.literal α n)+TeamScales.exterior ξ f.processors n/256) →
      ∀ u v, f.header + Routing.legLoad hR (tab.widthMatrix row) u v +
        Routing.legLoad hR (tab.widthMatrix row) v u ≤ f.capacity

/-- The paper's literal scale absorbs all three outgoing source fields of a team.
Together with the checked receiving/shared load this gives the actual two-hop
capacity on every unordered team block, uniformly after a single threshold. -/
theorem eventually_leg_capacity_of_incidence {α ξ : ℝ} (hξ : 0 ≤ ξ) (literalGap : ξ < α/3) (gap : ξ+2*α < 1/25) :
    ∀ᶠ n : ℕ in atTop, FitsLinksAt α ξ n := by
  filter_upwards [TeamScales.eventually_literals_le literalGap 768,eventually_table_leg_capacity hξ gap] with n source leg
  intro tab row labels hR f hp ht hh hl bounds
  apply leg tab row labels hR f hp ht hh hl
  intro u
  have bound := bounds u
  have sent := source f.processors
  rw [Nat.mul_assoc] at sent
  omega

end Cube.RouteRecords

end BorderVNP
end Computability
end OAI
