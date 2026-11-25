import OAI.Hierarchy.DescentPackedCanvasExtent
import OAI.Hierarchy.DescentPackedCanvasProgram
import OAI.Hierarchy.DescentPackedWalshStaticText
import OAI.Hierarchy.DescentBaseDepthBill

namespace OAI
/-! # The full pre-estimator native tariff at the packed group pitch -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup
open DescentPackedWalsh DescentSIMDLookup DescentPackedFlowPublication DescentBaseProfile DescentMeasuredHeader
open DescentPackedRectangle DescentPackedSingletonDepth
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

def flowCost (n D r c : ℕ) := 8+D*(4+n*(2*(1+18*(r*c))+4))+D*(4+n*(2*(7+121*D)+4))
def depthCost (H D m : ℕ) :=
  ((4+H*(8+2*(1+7)))+(4+H*(8+2*(1+9*m))))+m*(4+H*(8+2*(13+2*(37*4^(Nat.clog 2 D)))))
def work (H D r c u l : ℕ) :=
  let m:=u+l
  let N:=H*(m+1)+H*D
  flowCost (H*2^u) D r c+
  (DescentPackedWalsh.duration H u m+((4+32*H)+depthCost H D m))+
  ((12+780*N)+(4+100*(N*2^u))+((4+48*N)+(4+48*N)))

theorem depth_time (H D m k f B totals edges scratch δ w : ℕ) :
    let L:=layout H D m k f B totals edges scratch δ
    L.clocks w L.M≤depthCost H D m := by
  intro L
  apply (DepthRAM.Layout.time L w L.M).trans
  simp only [L,layout,DepthRAM.Layout.baseBill,DepthRAM.Layout.stepBill,depthCost]
  gcongr <;> omega

theorem runtime {k c : ℕ} (tokens : Tokens k c) (roster : Bank) (HP D R u l b short M floor f B K grain δ w : ℕ)
    (batchSize : chunks R M=2^u) :
    let C:=core tokens roster HP D u l b short M floor f B K grain
    let p:=plan tokens roster HP D u l b short M floor f B K grain
    p.prepareTicks C k δ R M w≤work HP D (2^k) c u l := by
  intro C p
  have traffic:=DescentPackedFlowPublication.tariff C HP R M
  rw [batchSize] at traffic
  have allocation:=depth_time HP D (u+l) k f B p.totals C.peers.roster.base p.scratch δ w
  have headers:=header_time (p.metaTape C k δ) HP (u+l) D
  let N := HP * (u + l + 1) + HP * D
  let L := layout HP D (u+l) k f B p.totals C.peers.roster.base p.scratch δ
  change L.clocks w (u+l-f) ≤ depthCost HP D (u+l) at allocation
  change headerTime (p.metaTape C k δ) HP (u+l) D ≤ 12+780*N at headers
  change DescentPackedFlowPublication.duration C HP R M ≤ flowCost (HP*2^u) D (2^k) c at traffic
  change DescentPackedFlowPublication.duration C HP R M +
      ((DescentPackedWalsh.duration HP u (u+l) + (4+HP*32+L.clocks w (u+l-f))) +
       ((headerTime (p.metaTape C k δ) HP (u+l) D + (4+100*(N*2^u))) +
        ((4+48*N)+(4+48*N)))) ≤
    flowCost (HP*2^u) D (2^k) c +
      (DescentPackedWalsh.duration HP u (u+l) + (4+32*HP+depthCost HP D (u+l))) +
      ((12+780*N)+(4+100*(N*2^u))+((4+48*N)+(4+48*N)))
  rw [Nat.mul_comm HP 32]
  omega

/-- One unrolled fixed header, the packed site gather, and the complete issued machine. -/
def totalWork (HP D R u l b short M k c : ℕ) :=
  (4+18*(HP*chunks R M)+(4+10*inputWords HP D u l b))+
    Book.charge D (2^k) b short M (Book.pitchBits HP u)+work HP D (2^k) c u l

theorem full_runtime {k c : ℕ} (tokens : Tokens k c) (roster : Bank) (HP D R u l b short M floor f B K grain δ w : ℕ)
    (batchSize : chunks R M=2^u) :
    let C:=core tokens roster HP D u l b short M floor f B K grain
    let p:=plan tokens roster HP D u l b short M floor f B K grain
    ticks HP D u l b short M floor f B K k R+p.prepareTicks C k δ R M w≤totalWork HP D R u l b short M k c := by
  intro C p
  have lo : (staticGeometry HP D u l b floor f B K).stop=floor+inputWords HP D u l b:=by
    simp only [Geometry.stop,Geometry.pointers,Geometry.meta,staticGeometry,inputWords,Nat.add_assoc]
  have t:=runtime tokens roster HP D R u l b short M floor f B K grain δ w batchSize
  simp only [ticks,totalWork,lo,Nat.add_sub_cancel_left]
  exact Nat.add_le_add_left t _

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup

end OAI
