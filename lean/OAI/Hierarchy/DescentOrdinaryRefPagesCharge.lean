import OAI.Hierarchy.DescentOrdinaryRefsROM

namespace OAI
/-! # Both immutable receiver reference pages charged once at the true word size -/
namespace Hierarchy.DescentOrdinaryRefsROM.Chart
open DescentStaticWordColumn Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
theorem word_bill (C : Chart) (h w ratio : ℕ) (bus : w≤ratio*h)
    (digits : C.digitBits≤h/2) (keys : C.keyBits*C.lanes≤h/2) (room : C.endAddress<2^w) :
    (((4+10*C.digitSize)+(4+10*C.tableSize))+7*names (C.program w))*w≤
      256*ratio*(C.oldNodes+C.count+1)*2^(h/2)*h :=by
  have actual:=(C.any (fun _=>0 : Memory w) room).2.2.1
  have cells:=C.cells_le h digits keys
  have one : 1≤2^(h/2) := Nat.two_pow_pos _
  have cost : (4+10*C.digitSize+(4+10*C.tableSize))+7*names (C.program w)≤
      256*(C.oldNodes+C.count+1)*2^(h/2) :=by
    rw [actual]
    nlinarith only [cells,one,Nat.zero_le (C.oldNodes*2^(h/2)),Nat.zero_le (C.count*2^(h/2))]
  exact (Nat.mul_le_mul cost bus).trans_eq (by ring)
end
end Hierarchy.DescentOrdinaryRefsROM.Chart

end OAI
