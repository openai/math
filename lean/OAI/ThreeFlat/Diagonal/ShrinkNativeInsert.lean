import OAI.ThreeFlat.Diagonal.ShrinkNativeOwner

namespace OAI
/-! # Restoring the deleted binary color coordinate of an ordered child -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.ChildRows
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalPinsExpr
open scoped Classical Fin.NatCast Fin.CommRing
variable {w c : ℕ}

private theorem restore_nat (x p bit : ℕ) (mid : x/2^p%2=bit) :
    let k:=2^p
    let free:=Owner.removeDigit x p
    (free/k)*(2*k)+(bit*k+free%k)=x := by
  let k:=2^p
  have hk : 0<k:=Nat.two_pow_pos _
  have lt : x%k<k:=Nat.mod_lt _ hk
  have lo : Owner.removeDigit x p%k=x%k := by simp [Owner.removeDigit,k,Nat.add_mod]
  have hi : Owner.removeDigit x p/k=(x/k)/2 := by
    unfold Owner.removeDigit
    rw [show 2^p=k from rfl,Nat.add_comm,Nat.mul_add_div hk,Nat.div_eq_of_lt lt,Nat.add_zero]
    rw [Nat.div_div_eq_div_mul,pow_succ]
  have r0:=Nat.mod_add_div x k
  have r1:=Nat.mod_add_div (x/k) 2
  change (Owner.removeDigit x p/k)*(2*k)+(bit*k+Owner.removeDigit x p%k)=x
  rw [lo,hi]
  rw [show x/k%2=bit from mid] at r1
  calc
    _=x%k+k*(bit+2*(x/k/2)) := by ring
    _=x%k+k*(x/k) := by rw [r1]
    _=x := r0

theorem insert_value (cur : Word w) (m : Memory w) (vs : Fin 1→Word w) (u color : F)
    (cw : c+1≤w) (v : BitWord (c+1)) (p : Fin (c+1)) (thin : Bool)
    (atU : (Formula.value (fun _=>cur) m vs u).val=Owner.removeDigit (tagOrdinal _ v).val p.val)
    (atColor : (Formula.value (fun _=>cur) m vs color).val=p.val)
    (atBit : v p=if thin then 0 else 1) :
    Formula.value (fun _=>cur) m vs (insert u color thin)=tagWord cw v := by
  let V:=Formula.value (fun _=>cur) m vs
  let k:=2^p.val
  let x:=(tagOrdinal _ v).val
  let free:=Owner.removeDigit x p.val
  let step:=Formula.op .shiftLeft (.lit 1) color
  have pc : p.val<w:=p.isLt.trans_le cw
  have fit : k<2^w:=(Nat.pow_lt_pow_iff_right (by decide : 1<2)).mpr pc
  have one : 1<2^w:=by have:=Nat.two_pow_pos p.val;change 2^p.val<2^w at fit;omega
  have vstep : (V step).val=k := by
    change (BinaryOp.shiftLeft.eval (1:Word w) (V color)).val=_
    have colorVal : (V color).val=p.val := atColor
    have oneVal : (1:Word w).val=1 := Fin.val_cast_of_lt one
    simp only [BinaryOp.eval,colorVal,ite_eq_left pc,oneVal,Nat.shiftLeft_eq,one_mul]
    exact Nat.mod_eq_of_lt fit
  have low : V (.op .mod u step)=((free%k:ℕ):Word w) := by
    apply Fin.ext;rw [Incidents.mod_value,atU,vstep,Fin.val_cast_of_lt ((Nat.mod_lt _ (Nat.two_pow_pos _)).trans fit)]
  have high : V (.op .div u step)=((free/k:ℕ):Word w) := by
    apply Fin.ext
    rw [Incidents.div_value,atU,vstep,Fin.val_cast_of_lt (by have h:=(V u).isLt;rw [atU] at h;exact (Nat.div_le_self ..).trans_lt h)]
  have vsWord : V step=(k:Word w) := by apply Fin.ext;rw [vstep,Fin.val_cast_of_lt fit]
  have mid : x/k%2=(v p).val := congrArg Fin.val (congrFun ((tagOrdinal _).symm_apply_apply v) p)
  rw [←Demand.tag_cast]
  cases thin with
  | false =>
    change V (.op .div u step)*(2*V step)+(V step+V (.op .mod u step))=(x:Word w)
    have mid' : x/k%2=1 := by rw [mid,atBit];rfl
    have natEq:=restore_nat x p.val 1 mid'
    rw [low,high,vsWord]
    simpa only [Nat.one_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using congrArg (fun n : ℕ=>(n:Word w)) natEq
  | true =>
    change V (.op .div u step)*(2*V step)+V (.op .mod u step)=(x:Word w)
    have mid' : x/k%2=0 := by rw [mid,atBit];rfl
    have natEq:=restore_nat x p.val 0 mid'
    rw [low,high,vsWord]
    simpa only [Nat.zero_mul,Nat.zero_add,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using congrArg (fun n : ℕ=>(n:Word w)) natEq


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.ChildRows

end OAI
