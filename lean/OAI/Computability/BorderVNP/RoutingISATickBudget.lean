import OAI.Computability.BorderVNP.RoutingISABroadcastProof
import OAI.Computability.BorderVNP.RoutingISAPaddingSchedule
import OAI.Computability.BorderVNP.RoutingISARelayModel
import OAI.Computability.BorderVNP.RoutingTicks

/-! # Tick allowance for the actual public routing passes

The common-prefix reader scans all incident copies, and the padding reader can
scan to the ends of all physical links. Their charge is bounded by the total
exterior capacity. The relay scan charges only occupied quotients plus the
upper triangle of endpoint pairs, while table construction charges records
and the cubic prefix directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

/-- With the rounded processor link, the total capacity of all incident block
scans is at most the exterior budget, even when the division has a remainder. -/
theorem BroadcastFrame.total_capacity_le (f : BroadcastFrame) (ξ : ℝ) (n : ℕ)
    (link : f.link = TeamScales.link ξ f.teams n) :
    f.teams*f.capacity ≤ TeamScales.exterior ξ f.processors n := by
  let bits := TeamScales.width n (1-ξ)
  change f.link = bits/f.teams at link
  change f.teams*(f.link*f.processors) ≤ f.processors*bits
  rw [link]
  calc
    _ = f.processors*(bits/f.teams*f.teams) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)

/-- True budget of the fixed native reference copy and comparison with every
incident physical header, uniformly in the processor count. -/
theorem BroadcastFrame.readTicks_le_exterior (f : BroadcastFrame) {w base : ℕ}
    (fit : f.Fits w base) (ξ : ℝ) (n : ℕ) (link : f.link = TeamScales.link ξ f.teams n) :
    f.readTicks ≤ 90*(TeamScales.exterior ξ f.processors n+f.teams+1) := by
  have total := f.total_capacity_le ξ n link
  have many : f.teams*f.header ≤ TeamScales.exterior ξ f.processors n :=
    (Nat.mul_le_mul_left _ fit.cap).trans total
  have one : f.header ≤ TeamScales.exterior ξ f.processors n :=
    (Nat.le_mul_of_pos_left _ (by have := fit.three; omega)).trans many
  have eq : f.readTicks = 53+42*f.header+6*f.teams+42*(f.teams*f.header) := by
    unfold readTicks
    change 49 + ((2+f.header*(41+1))+(2+f.teams*(6+f.header*(41+1)))) = _
    ring
  rw [eq]
  omega

/-- Sum of the four native time bounds consumed by broadcast, public schedule,
zero padding, and the actual occupied relay comparisons. -/
def routingCheckTicks (f : BroadcastFrame) (l : TableLayout) (row : ℕ → TableRow) : ℕ :=
  f.readTicks + 256*((l.teams+1)^3+l.count+1) +
    f.linkCheckTicks (headerSetup.slots+(readFrame 19 62 63 18).slots+1) paddingStartBlock.slots +
    relayCheckCost l.teams (fun u j ↦ l.partnerLength row u f.team j)

/-- The compiled physical route validators use O(X₀+R³+#rows) ticks per team,
with the actual double rounding and numerical ISA constants. -/
theorem routingCheckTicks_le (f : BroadcastFrame) (l : TableLayout) (row : ℕ → TableRow)
    {w base : ℕ} (fit : f.Fits w base) (same : f.teams = l.teams)
    (ξ : ℝ) (n : ℕ) (link : f.link = TeamScales.link ξ f.teams n)
    (budget : ∀ u, ∑ j, Routing.demand (l.widthMatrix row) u j ≤ TeamScales.exterior ξ f.processors n/64) :
    routingCheckTicks f l row ≤ 768*(TeamScales.exterior ξ f.processors n+(l.teams+1)^3+l.count+1) := by
  let X := TeamScales.exterior ξ f.processors n
  have b := f.readTicks_le_exterior fit ξ n link
  have p := f.linkCheckTicks_le_exterior ξ n
    (headerSetup.slots+(readFrame 19 62 63 18).slots+1) paddingStartBlock.slots link
  change f.readTicks ≤ 90*(X+f.teams+1) at b
  change f.linkCheckTicks _ _ ≤ 120*(X+f.teams+1) at p
  let v : Fin l.teams := ⟨f.team,fit.own.trans_eq same⟩
  have r := relayCheckCost_le l row (fit.three.trans_eq same) v X budget
  change relayCheckCost l.teams (fun u j ↦ l.partnerLength row u f.team j) ≤
    37+6+l.teams*4+l.teams^2*(29+4)+(X+l.teams^2)*(157+1) at r
  have sq : l.teams^2 ≤ (l.teams+1)^3 := by nlinarith only [Nat.zero_le (l.teams^3)]
  have team : l.teams ≤ (l.teams+1)^3 := by nlinarith only [Nat.zero_le (l.teams^3),Nat.zero_le (l.teams^2)]
  rw [same] at b p
  unfold routingCheckTicks
  change _ ≤ 768*(X+(l.teams+1)^3+l.count+1)
  omega

end RoutingISA

end BorderVNP
end Computability
end OAI
