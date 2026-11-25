import OAI.Hierarchy.ProbeFixedFailureWords
import OAI.Hierarchy.ProbePublicStageCount

namespace OAI
/-! # A source-uniform per-event direct and mate width cap -/

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StockCommit StripDirectory
open scoped Classical
noncomputable section
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

/-- Chosen at the public format, before the arbitrary input height, run,
board location, fitted word size and receiver-width amplification. -/
def paidRoleRate := max (Fintype.card (PayloadRole (publicStages v.W) k))
  (Fintype.card (PurchasedRole v.depth k))*v.menu.maximum

theorem paid_role_budget (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks)
    (src tab dst : ℕ) (owners : Bank) (a : Attempt) :
    let batch:=v.ballot P z width r banks src tab dst owners a
    max (Fintype.card (PayloadRole (Stages z (2^v.W)) k)) (Fintype.card (PurchasedRole v.depth k))*
      (batch.maxWidth*batch.copies)≤v.paidRoleRate*width := by
  intro batch
  have dims:=v.ordinary_dimensions P z width a
  have peak : batch.maxWidth=v.menu.maximum := by cases a <;> exact dims.1
  have mass : batch.copies=v.menu.copiesAt v.copyScale width := by cases a <;> exact dims.2
  have copiesLe : v.menu.copiesAt v.copyScale width≤width:=Nat.div_le_self ..
  have stages : Stages z (2^v.W)=publicStages v.W:=fixed_stage_count z v.W
  rw [peak,mass,stages,←Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ copiesLe

end
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end OAI
