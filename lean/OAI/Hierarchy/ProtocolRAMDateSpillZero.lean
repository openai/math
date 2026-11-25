import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMRowText
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # A single zero-width prefix for every dated spill rank -/

namespace Hierarchy.ProtocolRAM.DateSpill

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {W : ℕ}

def clear (W : ℕ) (paid : Bank) (edges : ℕ) : Procedure W :=
  scan W paid.base edges (.lit 0)

def cleared (paid : Bank) (edges : ℕ) (m : Memory W) : Memory W :=
  image paid.base edges (.lit 0) m

theorem clear_exec (paid : Bank) (edges : ℕ) (m : Memory W)
    (room : paid.base+edges<2^W) :
    (clear W paid edges).Exec m (cleared paid edges m) (4+6*edges) := by
  rw [Nat.mul_comm 6 edges]
  exact scan_exec paid.base edges (.lit 0) m trivial room

theorem cleared_at (paid : Bank) (edges : ℕ) (m : Memory W) (e : Fin edges) :
    (cleared paid edges m (paid.base+e.val)).val=0 := by
  rw [cleared,ProtocolRAMGeneratedWrite.read_image paid.base edges (.lit 0) m e]
  rfl

theorem cleared_frame (paid : Bank) (edges : ℕ) (m : Memory W) (a : ℕ)
    (away : a<paid.base ∨ paid.base+edges≤a) : cleared paid edges m a=m a :=
  ProtocolRAMGeneratedWrite.frame_image paid.base edges (.lit 0) m a away

theorem clear_cheap (W : ℕ) (paid : Bank) (edges : ℕ) : CheapCode (clear W paid edges) :=
  @scan_cheap _ _ _ _

theorem clear_text (W : ℕ) (paid : Bank) (edges : ℕ) : text (clear W paid edges)=15 := by
  rw [clear,Calendar.text_scan]
  rfl


end Hierarchy.ProtocolRAM.DateSpill

end OAI
