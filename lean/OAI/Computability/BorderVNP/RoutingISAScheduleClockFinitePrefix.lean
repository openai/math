import OAI.Computability.BorderVNP.CubeRouteAllDeclarations
import OAI.Computability.BorderVNP.RoutingISAScheduleClockFiniteIncidence
import OAI.Computability.BorderVNP.RoutingISAScheduleClockTotal
import OAI.Computability.BorderVNP.RoutingISASignedPrepPublic

/-! # The finite field processor's physical clock before the private suffix

The eleven group-schedule fragments use the frame left by the delivery
publication. The subsequent transmission loop charges each incident row,
including local ones, and the two-hop validators use the rounded link capacity.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube Cube.Physical LocalRow Transmission TeamScales Filter Finset
open private groups_deterministic from OAI.Computability.BorderVNP.RoutingISASignedPrepPublic

/-- The precise clock returned by the real pinned schedule on a candidate declaration. -/
def rawScheduleTicks (a : CubeArena.Layout) (frame saved index R dataCount : ℕ) (before : ℕ → ℕ) :=
  ((labelPrefixCost frame before+publicBootCost a saved)+(minimumCost a.n+
    (GroupWeights.ticks (weightLayout a frame index)+TeamNative.assignmentTicks (teamLayout a R)+
      (TeamBudget.setup.slots+(R+1)*(TeamBudget.row.slots+1)+1))))+directoryTicks a frame+writerTicks dataCount a.header.d

/-- The actual decoded cell count, number of product labels, populated demands,
and header coordinate count identify each native loop with its calibrated charge. -/
theorem rawScheduleTicks_eq (a : CubeArena.Layout) (frame saved index R dataCount : ℕ) (before : ℕ → ℕ)
    (cells : before (frame+11)=a.cells) (labels : before (frame+56)=a.alphabet) (rows : before (frame+9)=dataCount)
    (axes : a.header.a=a.n+1) :
    let l := LabelIndex.layout frame before
    rawScheduleTicks a frame saved index R dataCount before =
      descriptorTicks l before (l.labels-1) (a.n+1) (weightLayout a frame index) (teamLayout a R)+
      declarationTicks (a.header.decoder saved) a.n (Tally.selectorWidth a.n a.K a.h) := by
  intro l
  have c : l.cells=a.cells := cells
  have z : l.labels=a.alphabet := labels
  have d : l.deliveryCount=dataCount := rows
  change l.labels=a.header.d^(a.n+1) at z
  simp only [rawScheduleTicks,labelPrefixCost,publicBootCost,minimumCost,directoryTicks,writerTicks,
    descriptorTicks,declarationTicks,GroupWeights.checkedTicks,teamLayout,CubeHeaderInstall.Inputs.cost,
    CubeHeaderInstall.Inputs.decoder,CubeArena.Layout.pairWriter,PairDirectory.Layout.count,PairDirectory.Layout.Z]
  change _=LabelIndex.directoryTicks l (l.labels-1) before+_+_+_+_+(CellBanks.setup.slots+l.cells*15+1)+
    (30+(l.labels*l.labels)*(24+27*(a.n+1)))+(DataWriter.setup.slots+l.deliveryCount*(DataWriter.step.slots+1)+5)+
    SharedRows.budget a.header.d+_
  rw [c,d,z,axes]
  simp only [l,HeaderDecode.cost]
  ring

/-- The schedule run used in the finite return fiber is charged by the same
physical allowance on every returning path from these published words. -/
theorem rawSchedule_return {w R : ℕ} {a : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {owner : ℕ → Fin (R+1)} {decl : LengthDeclaration a.n a.header.d} {group : Fin a.header.d → Fin (R+1)} {pins : Pins.Layout}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w} {pass : Prop} (saved index : ℕ)
    (clocked : PublicSchedule a D pp lp owner decl group pins pub mac s m
      (rawScheduleTicks a (pub 0).val saved index R (D.directory pp lp).length (readings m)) pass)
    (cells : readings m ((pub 0).val+11)=a.cells) (labels : readings m ((pub 0).val+56)=a.alphabet)
    (rows : readings m ((pub 0).val+9)=(D.directory pp lp).length) (axes : a.header.a=a.n+1)
    (z : Returns (scheduleGroups a.n (Tally.selectorWidth a.n a.K a.h)) pub mac s m) :
    let l := LabelIndex.layout (pub 0).val (readings m)
    traceCost z.val.1 ≤ descriptorTicks l (readings m) (l.labels-1) (a.n+1) (weightLayout a (pub 0).val index) (teamLayout a R)+
      declarationTicks (a.header.decoder saved) a.n (Tally.selectorWidth a.n a.K a.h) := by
  obtain ⟨_,_,_,history,_,charge⟩ := clocked.1 (clocked.2 z.property).1
  rw [(z.property.unique_of_deterministic (groups_deterministic ..) history.runs).1]
  exact charge.trans_eq (rawScheduleTicks_eq a _ _ _ _ _ _ cells labels rows axes)

/-- Bound the actual route setup and full endpoint transmission allowance.
Nonlocal traffic is bounded by the same scheduled source table used for
the real local and remote transmission bits. -/
theorem finiteRouteTicks_le {w base n : ℕ} {ξ : ℝ} (f : BroadcastFrame) (l : TableLayout) (row : ℕ → TableRow)
    (actual : ℕ → Range w) (self : Word w) (u : Fin l.teams) (fit : f.Fits w base) (same : f.teams=l.teams)
    (link : f.link=TeamScales.link ξ f.teams n) (labels : ∀ i<l.count, (row i).first<l.teams ∧ (row i).second<l.teams)
    (sent : ℕ) (outgoing : 256*sent ≤ exterior ξ f.processors n)
    (endpoints : ∀ v : Fin l.teams, (∑ i ∈ range l.count, endpointWidth (row i) v.val) ≤ sent+exterior ξ f.processors n/256)
    (readback : (∑ i ∈ range l.count, (actual i).incident self) = ∑ i ∈ range l.count, endpointWidth (row i) u.val) :
    routeSetupBudget l row f+256*(1+l.count+∑ i ∈ range l.count, (actual i).incident self) ≤
      2048*(exterior ξ f.processors n+(l.teams+1)^3+l.count+1) := by
  let X := exterior ξ f.processors n
  have demand (v : Fin l.teams) : ∑ j, Routing.demand (l.widthMatrix row) v j ≤ X/64 := by
    rw [l.demand_sum_eq row labels]
    have le : (∑ i ∈ range l.count, (row i).exteriorWidth v.val) ≤ ∑ i ∈ range l.count, endpointWidth (row i) v.val := by
      apply sum_le_sum
      intro i _
      unfold TableRow.exteriorWidth endpointWidth
      split_ifs <;> omega
    have cap := le.trans (endpoints v)
    dsimp only [X]
    omega
  have checked := routingCheckTicks_le f l row fit same ξ n link demand
  have setup : routeSetupBudget l row f ≤ routingCheckTicks f l row := by unfold routeSetupBudget routingCheckTicks; omega
  have real := endpoints u
  rw [readback]
  omega

/-- Measured startup, geometry, publication and the native schedule/route leave
at least half the original integer clock for the private field computation. -/
theorem finitePrefix_remaining {front publication schedule route ticks : ℕ}
    (startup : 4*front ≤ ticks) (published : 8*publication ≤ ticks) (routed : 8*(schedule+route) ≤ ticks) :
    schedule+route ≤ ticks-(front+publication) ∧
      ticks/2 ≤ (ticks-(front+publication))-(schedule+route) := by omega

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
