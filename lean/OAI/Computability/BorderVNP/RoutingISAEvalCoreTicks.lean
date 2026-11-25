import OAI.Computability.BorderVNP.RoutingISATickBudget
import OAI.Computability.BorderVNP.RoutingISATransmissionTicks
import OAI.Computability.BorderVNP.TransmissionJointPacket

/-! # Combined physical clock for startup, pins, and actual transmissions

These passes run on every signed evaluation path. Their sum includes the
original register-frame stores, all true advice and pin reads, the physical
branch, the native route tables, both validators and the per-team payload
scans. Only the group-local data and the public geometry remain to be charged
when applying equation (8.3).
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM Finset Filter
open TeamContraction.ProcessorSlots

/-- The concrete clock allowances of the linked startup, branch, pin and
transmission instructions on one evaluating team. -/
def coreTicks {w : ℕ} (count : ℕ) (f : BroadcastFrame) (l : TableLayout) (row : ℕ → TableRow)
    (actual : ℕ → Transmission.Range w) (self : Word w) : ℕ :=
  jointBudget count w + 2 + (pinSetup.slots+17*(f.processors*f.literal)+1) +
  routingCheckTicks f l row +
  (Transmission.setup.slots + (20+Transmission.decision.depth)*l.count +
    (∑ i ∈ range l.count, (actual i).teamCost self) + 1)

/-- At the paper's scales the physical instruction allowances use at most a
fixed multiple of the exterior budget, the public cubic table, the number of
records and processors. This includes every co-located copy or guess. -/
theorem eventually_coreTicks {α ξ : ℝ} (gap : ξ < α/3) :
    ∀ᶠ n : ℕ in atTop, ∀ (w base count : ℕ) (f : BroadcastFrame) (l : TableLayout)
      (row : ℕ → TableRow) (actual : ℕ → Transmission.Range w) (self : Word w) (u : Fin l.teams)
      (src dst : Fin l.count → Fin l.teams) (data : Fin l.count → Bool),
      f.Fits w base → f.teams = l.teams → f.link = TeamScales.link ξ f.teams n →
      f.literal ≤ TeamScales.literal α n → w ≤ count → count ≤ f.processors →
      (∀ v, ∑ j, Routing.demand (l.widthMatrix row) v j ≤ TeamScales.exterior ξ f.processors n/64) →
      (∀ i : Fin l.count, (self = (actual i).teamA ↔ src i = u) ∧ (self = (actual i).teamB ↔ dst i = u)) →
      256*(Routing.teamBits src (fun i ↦ (actual i).width.val) (!data ·) u +
        Routing.teamBits dst (fun i ↦ (actual i).width.val) (!data ·) u +
        Routing.teamBits dst (fun i ↦ (actual i).width.val) data u) ≤ TeamScales.exterior ξ f.processors n →
      Routing.teamBits src (fun i ↦ (actual i).width.val) data u ≤ 3*f.processors*TeamScales.literal α n →
      coreTicks count f l row actual self ≤
        2048*(TeamScales.exterior ξ f.processors n+(l.teams+1)^3+l.count+f.processors+1) := by
  filter_upwards [TeamScales.eventually_literals_le gap 17] with n hl
  intro w base count f l row actual self u src dst data fit same link lit wc cr traffic ends assigned outgoing
  let X := TeamScales.exterior ξ f.processors n
  have router := routingCheckTicks_le f l row fit same ξ n link traffic
  have bits := Transmission.sum_teamCost_le actual self u src dst data ends
  have ho : 17*(f.processors*f.literal) ≤ X := by
    have hh := (Nat.mul_le_mul_left (17*f.processors) lit).trans (hl f.processors)
    rwa [Nat.mul_assoc] at hh
  have out := Nat.mul_le_mul_left 17 outgoing
  have litOut := hl f.processors
  have factor : 17*(3*f.processors*TeamScales.literal α n) =
      3*(17*f.processors*TeamScales.literal α n) := by ring
  rw [factor] at out
  unfold coreTicks jointBudget
  change 126+(41+count*10+1)+(19+8*81*(w+1)+8)+2+(44+17*(f.processors*f.literal)+1)+
    routingCheckTicks f l row+(19+24*l.count+(∑ i ∈ range l.count, (actual i).teamCost self)+1) ≤ _
  change 17*f.processors*TeamScales.literal α n ≤ X at litOut
  change routingCheckTicks f l row ≤ 768*(X+(l.teams+1)^3+l.count+1) at router
  change _ ≤ X at assigned
  change _ ≤ 2048*(X+(l.teams+1)^3+l.count+f.processors+1)
  omega

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
