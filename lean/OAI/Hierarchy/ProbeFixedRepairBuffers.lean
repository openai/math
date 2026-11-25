import OAI.Hierarchy.ProbeFixedFailureWords
import OAI.Hierarchy.ProbeFixedScalarQuoteCells
import OAI.Hierarchy.ProbeFixedRowPages

namespace OAI
/-! # Price and shape pages consumed by the native failure-row replay -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit PurchaseStage
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "H" => v.publicHeader P z width
local notation "g₀" => JointHeader.scores P.joint z N k
local notation "FEE" => StripChart.charges F (v.sized (v.seed P z width) width) v.cost (H).stop
variable (a : Attempt) (entry : Memory (wordBits z (2^v.W) copies))
local notation "stageMemory" => v.stage P z width r banks src tab dst owners a entry

structure RowPages (state : Memory W) : Prop where
  header : (H).Resident state
  scores : GlobalTests.Resident (DeadlineROM.scorePage v.mesh g₀ z N k a) z N k
    (DeadlineROM.prices v.mesh v.finish (v.basePhase width) (DeadlineROM.index v.mesh a)) state

structure RepairPages : Prop where
  guard : v.RowPages P z width a ((Calendar.guard C a).apply entry)
  checked : v.RowPages P z width a (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))
  stage : v.RowPages P z width a stageMemory
  charges : (FEE).Resident stageMemory

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
