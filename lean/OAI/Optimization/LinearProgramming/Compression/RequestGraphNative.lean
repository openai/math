import OAI.Optimization.LinearProgramming.Compression.RequestGraphPrepare
import OAI.Optimization.LinearProgramming.Compression.RequestProbeDialogue

/-! One fixed finite graph request machine for every dimension. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable

noncomputable def graphRequestDispatch := Dialogue.dispatchWith prepare

noncomputable def graphRequestDispatchP :
    OracleSpec.WordDialogue.ProcedureOf inputCode Dialogue.carryCode graphRequestDispatch :=
  Dialogue.dispatchWithP prepareP

/-- A uniform finite adaptive machine, with the LLL reduction, row scan,
query construction, reply handling, and affine result encoding in the program. -/
noncomputable def graphRequestMachine : OracleSpec.BitProgram :=
  OracleSpec.WordDialogue.machine graphRequestDispatchP

end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
