import OAI.Hierarchy.DescentResetFieldReturn
import OAI.Hierarchy.DescentGLPackedScale

namespace OAI
/-! # Bit cost of the original-field gather and the issued basis circuit -/
namespace Hierarchy.DescentGLPacked.BankImage
open DescentGLPacked DescentGLNielsen DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

def fieldFactor (D n keyWork : ℕ) := 4*(D+1)*(n+1)*(keyWork+256)

theorem gather_reset_price (C : Chart) (H D h l : ℕ) (field : ℕ→Expr) (T : DescentGLControlCode.Tables)
    (key : Expr) (fetch : ∀j<D,(field j).work≤7) :
    let n:=(schedule (h+l)).length
    let rows:=H*2^h
    let gs:=DescentPackedFlowBatch.passes C.input.base rows rows field 0 D
    let ps:=steps (C.chosen (h+l)) (D*H) (2^h) 0 n
    clock gs+(4+n*(2*(T.expr key).work+4)+clock ps)≤fieldFactor D n key.work*(1+rows) := by
  let n:=(schedule (h+l)).length
  let rows:=H*2^h
  have copied:=DescentPackedFlowBatch.tariff C.input.base rows rows D field 7 fetch
  have transformed:=DescentGLPacked.tariff (C.chosen (h+l)) (D*H) h 0 n
  have arbitrary (z d t u : ℕ) :
      (4+d*(4+z*18))+(4+t*(2*(u+13)+4)+(4+t*(4+d*z*224)))≤fieldFactor d t u*(1+z) := by
    unfold fieldFactor;ring_nf;omega
  apply (Nat.add_le_add copied (Nat.add_le_add_left transformed _)).trans
  simpa only [DescentGLControlCode.rate,Nat.mul_assoc,rows,n] using arbitrary rows D n key.work

theorem dyadic_fields (C : Chart) (H D c r unit payload cpu K : ℕ) (field : ℕ→Expr)
    (T : DescentGLControlCode.Tables) (key : Expr) (fetch : ∀j<D,(field j).work≤7)
    (positive : 0<unit) (width : 4*unit≤payload) (hardware : cpu≤K*payload) :
    let e:=lowBits c unit payload
    let h:=c-e
    let l:=e+r
    let n:=(schedule (h+l)).length
    let rows:=H*2^h
    let gs:=DescentPackedFlowBatch.passes C.input.base rows rows field 0 D
    let ps:=steps (C.chosen (h+l)) (D*H) (2^h) 0 n
    (clock gs+(4+n*(2*(T.expr key).work+4)+clock ps))*cpu≤
      fieldFactor D n key.work*K*(payload+H*payload+8*H*2^c*unit) := by
  let e:=lowBits c unit payload
  let h:=c-e
  let l:=e+r
  let n:=(schedule (h+l)).length
  have price:=gather_reset_price C H D h l field T key fetch
  have bill:=charged H c unit payload cpu K positive width hardware
  have pair : (1+H*2^h)*cpu≤K*(payload+H*payload+8*H*2^c*unit) := by
    dsimp only [h,e]
    rw [Nat.add_mul,Nat.one_mul]
    calc _ ≤ K*payload+K*(H*payload+8*H*2^c*unit):=Nat.add_le_add hardware bill
         _ = _ := by ring
  exact (Nat.mul_le_mul_right cpu price).trans
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (fieldFactor D n key.work) pair)

end
end Hierarchy.DescentGLPacked.BankImage

end OAI
