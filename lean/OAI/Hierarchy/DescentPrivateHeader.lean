import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # One-word native history register below the reusable per-stage arena -/

namespace Hierarchy.DescentPrivateHeader
open Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM

variable {w : ℕ}

def clearHeader (w header : ℕ) := scan w header 1 (.lit 0)

def initialized (header : ℕ) (m : Memory w) := ProtocolRAM.image header 1 (.lit 0) m

theorem initialize_run (header : ℕ) (m : Memory w) (fits : header+1<2^w) :
    (clearHeader w header).Exec m (initialized header m) 10 :=
  scan_exec header 1 (.lit 0) m trivial fits

theorem initialized_read (header : ℕ) (m : Memory w) : initialized header m header=0 := by
  simpa [initialized,Expr.eval] using ProtocolRAMGeneratedWrite.read_image header 1 (.lit 0) m (0:Fin 1)

theorem initialized_frame (header : ℕ) (m : Memory w) (a : ℕ) (apart : a≠header) :
    initialized header m a=m a :=
  ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)

def commit (w header upper : ℕ) := PhysicalInputPhases.copying w upper 1 header

def committed (header upper : ℕ) (m : Memory w) := PhysicalInputCopy.copied upper 1 header m

theorem commit_run (header upper : ℕ) (m : Memory w) (ordered : header≤upper) (fits : upper+1<2^w) :
    (commit w header upper).Exec m (committed header upper m) 11 :=
  Procedure.Spec.exec (PhysicalInputPhases.copying_spec upper 1 header fits (by omega) (.inl ordered)) m trivial

theorem committed_read (header upper : ℕ) (m : Memory w) :
    committed header upper m header=m upper := by
  simpa [committed] using PhysicalInputCopy.copied_at upper 1 header m 0 (by decide)

theorem committed_frame (header upper : ℕ) (m : Memory w) (a : ℕ) (apart : a≠header) :
    committed header upper m a=m a :=
  PhysicalInputCopy.copied_outside upper 1 header m a (by omega)

end Hierarchy.DescentPrivateHeader

end OAI
