import OAI.Hierarchy.ProtocolRAMSumScores
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Allowed opcodes of the native sum-and-threshold scan -/

namespace Hierarchy.ProtocolRAM.PruneFlag
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure

/-- Each row adds its bounded score to the prefix sum and the final row compares it
with the fixed threshold; the scan uses only the allowed controller instructions. -/
theorem cheap (W out n bound : ℕ) (e : Expr) : CheapCode (SumScores.procedure W out n bound e) := by
  apply writing_cheap
  have back : admissible (SumScores.prior W out) := by
    simp [SumScores.prior,Term.select,Term.binary,Term.load,Term.literal,
      admissible_let,admissible_rename,admissible,opAllowed,allowed]
  simp [SumScores.step,Term.select,Term.binary,Term.literal,admissible_let,admissible_rename,
    admissible,opAllowed,allowed,back,good_compile]


end Hierarchy.ProtocolRAM.PruneFlag

end OAI
