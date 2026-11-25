import OAI.Hierarchy.DescentVenueQuantityPrice
import OAI.Hierarchy.DescentResetStemFunded
import OAI.Hierarchy.DescentDatedResetVenue

namespace OAI
/-! # Row and dictionary costs of the two outgoing reset quantity planes -/
namespace Hierarchy.DescentVenueQuantityPlanes
open DescentSIMDLookup DescentActorRaster DescentDatedAddressBook.CandidateFront ProtocolRAM
noncomputable section

theorem padded_length (n : ℕ) : 2^Nat.clog 2 n≤2*n+1:=by
  by_cases lo : n≤1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp lo with z|z <;> rw [z] <;> decide
  · have lower:=Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<n by omega)
    have pos:=Nat.clog_pos (by decide : 1<2) (show 1<n by omega)
    cases dep : Nat.clog 2 n with
    | zero=>omega
    | succ k=>rw [dep] at lower;simp only [Nat.pred_succ] at lower;rw [Nat.pow_succ];omega

private theorem dense_cells (B H K N : ℕ) :
    DenseRead.cells B H K 0 N ≤ 4*(B*(H*K))+2*N+3:=by
  change 2*(2^Nat.clog 2 (B*(H*K)))+2^Nat.clog 2 N≤_
  have rows:=padded_length (B*(H*K))
  have raw:=padded_length N
  omega

private def scanRate (op : ℕ) := 200+40*op
private theorem scan_paid (c rows op : ℕ) : tableScanBill c rows op≤ scanRate op*(c+rows+1):=by
  unfold scanRate tableScanBill
  nlinarith only [Nat.zero_le c,Nat.zero_le rows,Nat.zero_le op,Nat.zero_le (op*c),Nat.zero_le (op*rows)]

def resetPlaneFactor (B : ℕ) := 2048*volumeFactor 1 B+scanRate 25*(3*volumeFactor 1 B+1)+scanRate denseOp*(5*B+6)

theorem planeFactor_linear (B : ℕ) : resetPlaneFactor B≤resetPlaneFactor 1*(B+1):=by
  unfold resetPlaneFactor volumeFactor
  nlinarith only [Nat.zero_le (scanRate denseOp),Nat.zero_le (scanRate denseOp*B),Nat.zero_le B,Nat.zero_le (scanRate 25*B),Nat.zero_le (scanRate 25)]

def planeEnvelope (p : Dims) (h : ℕ) := 1+stemEnvelope h (p.oldHosts*p.shapes) p.hosts p.groups
  p.blocks p.oldLanes p.lanes

/-- One native quantity plane includes the old-to-new pitch conversion, the block
transpose and the genuine dense map. Unoccupied old and new hosts are counted. -/
theorem fee_funded (p : Dims) (h : ℕ) (blocks : 0<p.blocks) (lanes : 0<p.lanes)
    (oldPitch : p.oldLanes≤h) (newPitch : p.lanes≤h) (oldTable : p.precision*p.oldLanes≤h/2)
    (newTable : (p.precision*p.blocks)*p.lanes≤h/2) :
    fee p≤resetPlaneFactor p.blocks*planeEnvelope p h:=by
  let N:=p.oldHosts*p.shapes
  let B:=p.blocks
  let J:=p.groups
  let H:=p.hosts
  let a:=p.precision
  let A:=p.oldLanes
  let M:=p.lanes
  let K:=chunks J M
  let E:=planeEnvelope p h
  let V:=DescentResetStemProject.volume 1 N J B a A M
  let U:=volumeFactor 1 B
  let O:=(Overlap.pieces (J*B) A (M*B)+1)*(A+1)*2^(a*A)+Overlap.rows N (J*B) A+Overlap.rows N (J*B) (M*B)+1
  let R:=DescentScalarBookReshape.cells p.oldHosts p.shapes J B a M
  have one : 1≤E:=Nat.le_add_right ..
  have envelope : stemEnvelope h N H J B A M≤E:=Nat.le_add_left ..
  have volume : V≤U*E:=(volume_paid h 1 N H J B a A M blocks lanes oldPitch newPitch oldTable newTable).trans
    (Nat.mul_le_mul_left _ envelope)
  have overlap : O≤V:=by
    simp only [O,V,DescentResetStemProject.volume,Nat.one_mul]
    omega
  have reshape : R≤2*V:=by
    simp only [R,V,N,DescentScalarBookReshape.cells,DescentResetStemProject.volume,
      DescentVectorBookReshape.dictionaryWords,DescentVectorBookReshape.rows,Nat.one_mul,Nat.mul_one]
    omega
  have rows₀ : B*(N*K)≤V:=by
    simp only [K,V,DescentResetStemProject.volume,DescentVectorBookReshape.rows,Nat.one_mul,Nat.mul_one]
    omega
  have hs : H*K≤E:=by dsimp only [E,planeEnvelope,stemEnvelope,H,K,J,M];omega
  have hosts : N≤E:=by dsimp only [N,E,planeEnvelope,stemEnvelope];omega
  have rows₁ : B*(H*K)≤B*E:=Nat.mul_le_mul_left _ hs
  have cells:=dense_cells B H K N
  have dense : DenseRead.cells B H K 0 N+B*(H*K)+1≤(5*B+6)*E:=by
    nlinarith only [cells,rows₁,hosts,one]
  have split : R+B*(N*K)+1≤(3*U+1)*E:=by
    nlinarith only [reshape,rows₀,volume,one]
  have paid₀:=(scan_paid R (B*(N*K)) 25).trans (Nat.mul_le_mul_left _ split)
  have paid₁:=(scan_paid (DenseRead.cells B H K 0 N) (B*(H*K)) denseOp).trans (Nat.mul_le_mul_left _ dense)
  have first:=Nat.mul_le_mul_left 2048 (overlap.trans volume)
  unfold fee
  rw [show p.shapes*p.oldHosts=N from Nat.mul_comm ..]
  change 2048*O+tableScanBill R (B*(N*K)) 25+tableScanBill (DenseRead.cells B H K 0 N) (B*(H*K)) denseOp≤_
  calc _ ≤2048*(U*E)+scanRate 25*((3*U+1)*E)+scanRate denseOp*((5*B+6)*E):=
           Nat.add_le_add (Nat.add_le_add first paid₀) paid₁
       _ =resetPlaneFactor B*E:=by dsimp only [U,resetPlaneFactor];ring

end
end Hierarchy.DescentVenueQuantityPlanes

namespace Hierarchy.DescentDatedAddressBook.ResetVenue
open DescentSIMDLookup DescentVenueQuantityPlanes CandidateFront
noncomputable section
variable (v : ResetVenue)

/-- Both old pitches may differ. They share the compacted output geometry. -/
def quantityRows (h : ℕ) := planeEnvelope v.dense h+
  v.rawHosts*chunks (v.dense.groups*v.dense.blocks) v.actorLanes

theorem quantity_funded (h : ℕ) (blocks : 0<v.dense.blocks) (lanes : 0<v.dense.lanes)
    (paidOld : v.dense.oldLanes≤h) (actorOld : v.actorLanes≤h) (newPitch : v.dense.lanes≤h)
    (paidIn : v.dense.precision*v.dense.oldLanes≤h/2) (paidOut : (v.dense.precision*v.dense.blocks)*v.dense.lanes≤h/2)
    (actorIn : v.actorLanes≤h/2) (actorOut : v.dense.blocks*v.dense.lanes≤h/2) :
    DescentVenueQuantityPlanes.fee v.dense+DescentVenueQuantityPlanes.fee v.actorDims ≤ 2*resetPlaneFactor 1*(v.dense.blocks+1)*v.quantityRows h:=by
  have left:=fee_funded v.dense h blocks lanes paidOld newPitch paidIn paidOut
  have right:=fee_funded v.actorDims h blocks lanes actorOld newPitch
    (show 1*v.actorLanes≤h/2 by simpa only [Nat.one_mul] using actorIn)
    (show (1*v.dense.blocks)*v.dense.lanes≤h/2 by simpa only [Nat.one_mul] using actorOut)
  have a : planeEnvelope v.dense h≤v.quantityRows h:=Nat.le_add_right ..
  have b : planeEnvelope v.actorDims h≤v.quantityRows h:=by
    unfold quantityRows planeEnvelope stemEnvelope actorDims rawHosts
    dsimp only
    omega
  have c:=planeFactor_linear v.dense.blocks
  have l:=left.trans (Nat.mul_le_mul c a)
  have r:=right.trans (Nat.mul_le_mul c b)
  calc _≤resetPlaneFactor 1*(v.dense.blocks+1)*v.quantityRows h+resetPlaneFactor 1*(v.dense.blocks+1)*v.quantityRows h:=
           Nat.add_le_add l r
       _=_:=by ring

end
end Hierarchy.DescentDatedAddressBook.ResetVenue

end OAI
