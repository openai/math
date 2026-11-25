import OAI.Hierarchy.ProbeStageColumnScan

namespace OAI
/-! # Hardware size of the fixed packed column scan -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
theorem labels_registers (es : List Expr) (base rows L w : ℕ) (h : ∀e∈es,e.work≤L) :
    let p:=program w (ProbeStage.Native.columns rows base es)
    p.labels+p.registers+p.slots≤15+es.length*(11+4*L) :=by
  induction es generalizing base with
  | nil =>
      simpa [ProbeStage.Native.columns,program,Expr.work] using (show (scan w 0 0 (.lit 0)).labels+(scan w 0 0 (.lit 0)).registers+(scan w 0 0 (.lit 0)).slots≤15 from by
        obtain ⟨hr,hg,hs⟩:=scan_size w 0 0 (.lit 0);simp [hr,hg,hs,Expr.work])
  | cons e es ih =>
      have he:=h e (.head _);have tail:=ih (base+rows) (fun u hu=>h u (.tail _ hu))
      have l:=scan_size w base rows e
      simp only [ProbeStage.Native.columns,program,Pass.procedure,Procedure.seq,List.length_cons,Nat.succ_mul] at *
      omega

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand

end OAI
