import OAI.Hierarchy.ProbeStageCompactBody
import OAI.Hierarchy.ProbeStageCompactLoop
import OAI.Hierarchy.ProbeStageProgramCost

namespace OAI
/-! # The counted subdivision program and its uniform allowances -/

namespace Hierarchy.ProbeStage.Native.Compact
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

def level (h d j : ℕ) : Procedure (ramWidth h d) :=
  if good : j< rounds d then
    ((program _ (prepareRows h d j)).seq (CompactLoop.program h (body h d ⟨j,good⟩))).seq (program _ (writeRows h d j))
  else program _ []

def overhead (h : ℕ) := 38+(10+stageClock+unstageClock)*2^h

/-- The short heights have at most eight ordinals and use the directly
mounted reference visit. Every other height uses one mounted copy per level. -/
def subdivision (h d : ℕ) : Procedure (ramWidth h d) :=
  if 4≤ h then chronological (program _ (rootPasses h)) (level h d) (rounds d)
  else subdivisionProgram h d

def constant (d : ℕ) := subdivisionConstant d+(48+stageClock+unstageClock)*rounds d

def codeBound (d : ℕ) := 8*(53+15000*rounds d)

def ticks (h d : ℕ) (m : Memory (ramWidth h d)) :=
  Native.ticks h d m+rounds d*overhead h

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
