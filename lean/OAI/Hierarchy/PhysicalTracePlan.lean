import OAI.Hierarchy.TraceNativeScale
import OAI.ThreeFlat.Diagonal.TraceCursorState
import OAI.ThreeFlat.Diagonal.PhysicalBlockCharge

namespace OAI
/-! # The selected physical compression plan and its native grid instance -/

noncomputable section
namespace Hierarchy.TraceDistribution.Physical
open ThreeFlat Diagonal Diagonal.HistoryContraction Diagonal.LaneCursor
open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.RAMMemory
open scoped BigOperators Classical
variable {F : Type} [Field F]
variable (B : PhysicalStage.Block F) {k : ℕ} (hk : 2≤k+1) (low offsets slots : ℕ)

def run (s : ℕ) (fits : B.blockCharge*s ≤ k+1) :
    PhysicalStage.Run F (B.cursorState hk low offsets slots) := by
  let P := B.repeat s
  let bits := k+1-P.charge
  have e : k+1=P.charge+bits := by
    dsimp [P,bits]
    rw [B.charge_repeat]
    omega
  let A := B.cursorState hk low offsets slots
  exact PhysicalStage.Program.recast e A (P.run bits (e ▸ A))

variable {low}
variable [Fintype F] {w pc regs words S base fuel : ℕ}
variable (M : Machine w pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F ≤ 2^w) (st : Word w)

abbrev nativeRun (s : ℕ) (fits : B.blockCharge*s ≤ k+1) :=
  run B hk low (1+(((k+1)+low)+((k+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words ((k+1)+low)).cells s fits

end Hierarchy.TraceDistribution.Physical

end
end OAI
