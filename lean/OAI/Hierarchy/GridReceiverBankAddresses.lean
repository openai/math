import OAI.Hierarchy.GridDescription
import OAI.Hierarchy.TraceReceiverAge
import OAI.Hierarchy.TraceReceiverTasks
import OAI.ThreeFlat.Diagonal.TickWorkspace

namespace OAI
/-! # Addresses of the actual selected-root receiver's static memory banks -/
namespace Hierarchy.GridReceiverBanks
open ThreeFlat Diagonal TraceAdmission

def base (w : ℕ) := 30*GridDescription.sector w
def gap (w : ℕ) := 2^(4*w)
def limit (w : ℕ) := gap w-1
def mapHeader (w : ℕ) := base w+24
def commands (w : ℕ) := base w+9*gap w
def cursor (w : ℕ) := base w+32
def width (w : ℕ) (j : Fin 3) := base w+(6+j.val)*gap w

/-- The standalone command table reserves a fixed collection of disjoint
intervals in sector 30, independently of the number of selected roots. -/
def tasks (w : ℕ) : TraceReceiverTasks.Layout where
  current := base w
  tasks := base w+gap w
  selected := TickWorkspace.base (receiverAge w) 17
  first := TickWorkspace.base (receiverAge w) 11+3*(TickWorkspace.stride (receiverAge w)/4)
  results := TickWorkspace.base (receiverAge w) 13
  parent := base w+16
  maps := base w+2*gap w
  pins := base w+3*gap w
  rows := base w+4*gap w
  bits := base w+5*gap w

end Hierarchy.GridReceiverBanks

end OAI
