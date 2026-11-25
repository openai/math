import OAI.Hierarchy.DescentSignedRoleScans

namespace OAI
/-! Literal code size of an original role-dependent SIMD scan. -/
namespace Hierarchy.DescentSIMDLookup.RoleScans
open DescentStaticWordColumn DescentPackedFlowBatch ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
theorem column_names (a H G M base w output j n : ℕ) (src : Bank) :
    names (ProtocolRAM.program w (passes output (H*chunks G M) (H*chunks G M)
      (fun t=>lookup (banks a H G M base src t)) j n))=15+n*(11+4*20) :=by
  induction n generalizing j with
  | zero=>simp [passes,ProtocolRAM.program,names_scan,Expr.work]
  | succ n ih=>
    simp only [passes,ProtocolRAM.program,names_seq,Pass.procedure,names_scan,lookup_work,ih,Nat.succ_mul]
    omega

theorem cpu_names {a b : ℕ} (f : ℕ→Cell a→Cell b) (H G M w base pages : ℕ) (src : Bank) :
    names (cpu f H G M w base pages src)=
      15*(pages*pitch a H G M+1)+(15+pages*(11+4*20)) :=by
  rw [cpu,names_seq,install,names_mount,jobs,column_names]

end
end Hierarchy.DescentSIMDLookup.RoleScans

end OAI
