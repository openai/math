import OAI.Computability.VPVNP.CompressorRefreshBeforeGroup
import OAI.Computability.VPVNP.CompressorNativePassRates

/-!
# Communication cost of the entire refresh pass

The three header publications, the selected native core, six incidence copies,
and the traversal publications account for all source reports. Their combined
charge is linear in the number of positions of the old graph. Calendar costs
use the number of actual visits in the fixed block.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.RefreshEmit

open BurstRAM BlockPlanner Schedule Compression DescriptorSpace SourceOnline ScheduledTrace
open PortRefresh PairSimulation.LocalHistory
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
local notation "scr" => BlockProgram.script B
local notation "role" => Scalars.Pass.refresh S.portExponent (S.degreeExponent 0) S.expanderExponent
local notation "headerRate" => ScheduledRates.headerRate (BlockProgram.geometry B) role
local notation "coreRate" => Build.chargeFactor S.graph (Nat.two_pow_pos S.expanderExponent)
  (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh (LevelRecipe.Shape.ties (RefreshBlockPlan.shape B))
local notation "copyRate" => 18*2^(S.degreeExponent 0)+4

/-- One fixed source charge per old position. The two additive publication
costs are absorbed because every incoming state has at least one position. -/
def rawRate : ℕ := headerRate + coreRate + copyRate + 27

/-- Bound the actual combined source charge by the uniform per-position rate. -/
theorem raw_le {a g : ℕ} (X : State a g) {work : ℕ}
    (actual : work ≤ headerRate + coreRate*X.positions + X.positions*copyRate + 27) :
    work ≤ rawRate B * X.positions := by
  have hdr := Nat.le_mul_of_pos_right headerRate X.positions_pos
  have pub := Nat.le_mul_of_pos_right 27 X.positions_pos
  rw [rawRate,Nat.add_mul,Nat.add_mul,Nat.add_mul]
  rw [Nat.mul_comm X.positions copyRate] at actual
  omega

variable {g w : ℕ} (X : State S.portExponent (S.portExponent+g))
local notation "Pkt" => Packet scr w
local notation "logs" => (fun ps : List Pkt ↦ List.flatMap SourceWalk.Packet.reports ps)

/-- The online recipe and frame probes of the shared prefix, selected worker
and remaining packets are included in the same linear bound. -/
theorem groupCost_bound (pre : List Pkt) (term : Pkt) (tail : List Pkt)
    (visits : (pre++term::tail).length ≤ (scr).block.length)
    (source : RAMBuckets.cost Report.probes (logs (pre++term::tail)) ≤
      headerRate + coreRate*X.positions + X.positions*copyRate + 27) :
    groupCost scr pre + groupCost scr [term] + groupCost scr tail ≤ nativePassRate scr (rawRate B)*X.positions := by
  rw [← groupCost_split_selector]
  exact groupCost_nativeRate scr _ (rawRate B) X.positions X.positions_pos visits (raw_le B X source)

variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
variable (base : Word w) (positions blocks t cap termCap : ℕ)
variable (c : Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh)

/-- The deterministic prefix and the selected prefix may have distinct packet
records. Their reports agree at the actual selector, so the original core
bound pays for the shared prefix exactly once. -/
theorem aggregate {m first : Memory w} {hs ds pre tail copies publications : List Pkt} {term : Pkt}
    (before : RefreshBefore.Before B f hf base positions blocks t X cap m hs ds)
    (same : logs ds = logs pre)
    (core : RefreshCore.Built B base positions blocks t X c termCap first (logs (pre++term::tail)))
    (finish : RAMBuckets.cost Report.probes (logs (copies++publications)) ≤ X.positions*copyRate+27) :
    RAMBuckets.cost Report.probes (logs ((hs++ds)++term::(tail++(copies++publications)))) ≤
      headerRate + coreRate*X.positions + X.positions*copyRate + 27 := by
  have hdr := RefreshBefore.header_charge B f hf base positions blocks X m
    ((scr).levelsPerBlock*t+S.steps) ((scr).levelsPerBlock*t+(S.steps+1))
  have hhdr : RAMBuckets.cost Report.probes (logs hs) = headerRate := by
    rw [before.headerReports]; exact hdr
  have all : logs ((hs++ds)++term::(tail++(copies++publications))) =
      logs hs ++ logs (pre++term::tail) ++ logs (copies++publications) := by
    simp only [List.flatMap_append,List.flatMap_cons,List.append_assoc] at same ⊢
    rw [same]
  rw [all,RAMBuckets.cost_append,RAMBuckets.cost_append,hhdr]
  have c₁ := core.charge
  have c₂ := finish
  omega

end CompressorRecords.RefreshEmit

end

end VPVNP
end Computability
end OAI
