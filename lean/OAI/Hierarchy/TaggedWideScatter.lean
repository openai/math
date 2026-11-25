import OAI.Hierarchy.ProtocolRAMTurnReplay

namespace OAI
/-! # Native sparse scatter issued by a width/party observer -/
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
/-- A physical zero-filled array followed by a chronological stream of indexed RAM writes.
Dates use these arrays for historical widths/peer IDs, fixed-party aggregate controls
and the candidate-specific packet fields. -/
structure Scatter where
  base : ℕ
  length : ℕ
  scratch : ℕ
  rows : ℕ
  address : Expr
  value : Expr

def Scatter.code (s : Scatter) (W : ℕ) : Procedure W :=
  ProtocolRAMTurnReplay.program W s.base s.length s.scratch s.rows s.address s.value

def Scatter.ticks (s : Scatter) := ProtocolRAMTurnReplay.work s.length s.rows s.address s.value


def Scatter.floor (s : Scatter) := s.base-1
def Scatter.stop (s : Scatter) := s.scratch+2*s.rows

structure Ordered {n : ℕ} (lo hi : ℕ) (p : Fin n→Scatter) : Prop where
  lower : ∀i,lo≤(p i).floor
  upper : ∀i,(p i).stop≤hi
  separate : ∀i j,i<j→(p i).stop≤(p j).floor


end Hierarchy.ProtocolRAM.Calendar.WideCPU

end OAI
