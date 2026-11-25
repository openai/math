import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Hardware size of a fixed list of contiguous physical array passes -/
namespace Hierarchy.DescentOperandVectorArena
open DescentPackedFlowBatch DescentStaticWordColumn Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
theorem names_passes (base rows pitch w L : ℕ) (e : ℕ→Expr) (j n : ℕ)
    (he : ∀i,j ≤ i→i<j+n→(e i).work≤L) :
    names (ProtocolRAM.program w (passes base rows pitch e j n)) ≤ 15+n*(11+4*L) :=by
  induction n generalizing j with
  | zero=>norm_num [passes,ProtocolRAM.program,names_scan,Expr.work]
  | succ n ih=>
    have bounds:=ih (j+1) (fun i low hi=>he i (by omega) (by omega))
    have elem:=he j le_rfl (by omega)
    simp only [passes,ProtocolRAM.program,ProtocolRAM.Pass.procedure,names_seq,names_scan]
    rw [Nat.succ_mul n (11+4*L)]
    omega

end
end Hierarchy.DescentOperandVectorArena

end OAI
