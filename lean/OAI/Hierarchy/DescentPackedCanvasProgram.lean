import OAI.Hierarchy.DescentPackedCanvasRoom
import OAI.Hierarchy.DescentPackedFlowPublication
import OAI.Hierarchy.DescentPackedCanvasMasks
import OAI.Hierarchy.DescentPackedRectanglePublication

namespace OAI
/-! # The public native program and exact clock at the allocated reset dates -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas.Placement
open DescentPackedWalsh DescentPackedRectangle DescentPackedSingletonDepth DescentMeasuredHeader DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {r c : ℕ} (p : Placement) (C : DescentPackedFlowPublication.Layout p.geo.ports r c)
local notation "P" => p.geo.hosts
local notation "D" => p.geo.ports
local notation "u" => p.geo.high
local notation "l" => p.geo.low
local notation "m" => u+l
local notation "N" => P*(m+1)+P*D
local notation "ptr" => p.zeroPtr
def depth (k δ : ℕ) := DescentPackedSingletonDepth.layout P D m k p.geo.f p.geo.budget p.totals C.peers.roster.base p.scratch δ
def metaTape (k δ : ℕ) := let L:=p.depth C k δ
  metadata (H:=P) («u»:=u) («l»:=l) («D»:=D) p.geo.meta ⟨L.base (L.M+1),Nat.clog 2 P⟩ ⟨C.peers.roster.base,Nat.clog 2 (P*D)⟩
def pullTape := gather (H:=P) («u»:=u) («l»:=l) («D»:=D) p.geo.meta ⟨p.headerBase,Nat.clog 2 N⟩
  ⟨p.first,rowBits P u⟩ p.peers

def prepare (count : Bank) (k δ R M w out : ℕ) : Procedure w :=
  let L:=p.depth C k δ
  let T:=p.metaTape C k δ
  let raw:=transformBank p.first P u l
  let pre:=(DescentPackedWalsh.code w p.geo.origin p.first P u l p.geo.bits 0 (axesList u l)).seq
    ((tap raw ptr p.geo.bits p.totals P w).seq (L.cpu w L.M))
  let mask:=DescentPackedRectangle.Canvas.masks T.owner count ⟨p.headerBase+N,Nat.clog 2 N⟩
    ⟨p.headerBase+2*N,Nat.clog 2 N⟩ p.depthPage p.gainPage P m D w
  let read:=(DescentPackedRectangle.code T p.pullTape w p.headerBase out P u l D).seq mask
  (DescentPackedFlowPublication.procedure C P R M w).seq (pre.seq read)

def prepareTicks (k δ R M w : ℕ) :=
  let T:=p.metaTape C k δ
  DescentPackedFlowPublication.duration C P R M+
    (DescentPackedSingletonDepth.clocks P u l D k p.geo.f p.geo.budget p.totals C.peers.roster.base p.scratch w δ+
     ((headerTime T P m D+(4+100*(N*2^u)))+((4+48*N)+(4+48*N))))


end
end Hierarchy.DescentSixParty.PackedFlow.Canvas.Placement

end OAI
