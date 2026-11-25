import OAI.Hierarchy.ProbeStageCompactIO

namespace OAI
/-! # The fixed allocator body for a single ordinal -/

namespace Hierarchy.ProbeStage.Native.Compact
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

def body (h d : ℕ) (j : Fin (rounds d)) : Procedure (ramWidth h d) :=
  ((stage h d j).seq (Record.procedure _ (recordAdvice h d j) (recordScratch h d j) (row h))).seq (unstage h d j)

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
