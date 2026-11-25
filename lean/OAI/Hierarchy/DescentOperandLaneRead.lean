import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # The value of one genuine packed operand cell in its physical row -/
namespace Hierarchy.DescentOperandStateBanks.Reset
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

theorem lane_read {a H G M w : ℕ} (out : ℕ) (v : Fin H→Fin G→Cell a) (m : Memory w)
    (read : ∀p : Row H G M,m (out+(row H G M p).val)=((data v p).val:Word w))
    (room : a*M≤w) (hm : 0<M) (h : Fin H) (g : Fin G) :
    digit a (lane g hm).val (m (out+(row H G M (position h g hm)).val)).val=(v h g).val := by
  let pp:=position h g hm
  have inside:=(data v pp).isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) room)
  have addr : pp.2.val*M+(lane g hm).val=g.val := Nat.div_add_mod' ..
  have valid:=addr.trans_lt g.isLt
  rw [read,Fin.val_cast_of_lt inside]
  change digit a _ (data v pp).val=_
  unfold data
  rw [digit_encode,dite_eq_left valid]
  exact congrArg (fun j=>(v h j).val) (Fin.ext addr)

end
end Hierarchy.DescentOperandStateBanks.Reset

end OAI
