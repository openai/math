import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # A measured packed page determines every physical host and group cell -/
namespace Hierarchy.DescentPackedColony
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M a w : ℕ} {B : Bank} {m : Memory w}
theorem Reads.determined {x y : Fin H→Fin G→Cell a} (left : Reads B x M m) (right : Reads B y M m)
    (live : 0<M) (room : a*M≤w) : x=y :=by
  funext h g
  let c : Fin (chunks G M):=⟨g.val/M,by
    change g.val/M<(G+M-1)/M
    apply (Nat.le_div_iff_mul_le live).2
    rw [Nat.succ_mul]
    have old:=Nat.div_mul_le_self g.val M
    have inside:=g.isLt
    omega⟩
  let i : Fin M:=⟨g.val%M,Nat.mod_lt _ live⟩
  let p : Row H G M:=(h,c)
  have eqn:=congrArg Fin.val ((left p).symm.trans (right p))
  have narrow:=Nat.pow_le_pow_right (by decide : 0<2) room
  have hw : data x p=data y p:=by
    apply Fin.ext
    simpa only [Fin.val_natCast,Nat.mod_eq_of_lt ((data x p).isLt.trans_le narrow),
      Nat.mod_eq_of_lt ((data y p).isLt.trans_le narrow)] using eqn
  have hit:c.val*M+i.val=g.val:=Nat.div_add_mod' _ _
  have seen:=congrArg (fun z=>(encode a M).symm z i) hw
  simpa only [data,Equiv.symm_apply_apply,p,dite_eq_left (hit.trans_lt g.isLt),
    show (⟨c.val*M+i.val,hit.trans_lt g.isLt⟩:Fin G)=g by exact Fin.ext hit] using seen

end
end Hierarchy.DescentPackedColony

end OAI
