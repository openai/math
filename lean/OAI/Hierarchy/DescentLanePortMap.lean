import OAI.Hierarchy.DescentLaneProgram

namespace OAI
namespace Hierarchy.DescentLaneGates
open DescentKernelHistory
noncomputable section
variable {A B : Type} {width : A→ℕ} {nextWidth : B→ℕ} {Y p : ℕ}

structure PortMap (width : A→ℕ) (nextWidth : B→ℕ) where
  slot : A→B
  sameWidth : ∀a,width a=nextWidth (slot a)

def PortMap.bit (f : PortMap width nextWidth) (z : BitRef width) : BitRef nextWidth :=
  ⟨f.slot z.1,Fin.cast (f.sameWidth z.1) z.2⟩

def Lane.transport (l : Lane p width) (f : PortMap width nextWidth) : Lane p nextWidth :=
  ⟨f.slot l.port,l.start,l.stride,fun j=>(f.sameWidth l.port) ▸ l.fits j⟩

def Program.transport (z : Program Y p width) (f : PortMap width nextWidth) : Program Y p nextWidth where
  Node:=z.Node
  op i:={z.op i with arg:=fun j=>((z.op i).arg j).transport f}

end
end Hierarchy.DescentLaneGates

end OAI
