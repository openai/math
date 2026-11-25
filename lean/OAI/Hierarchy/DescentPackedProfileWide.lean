import OAI.Hierarchy.DescentPackedProfileTape

namespace OAI
/-! # Fixed zero extension in a wider local matching digit format -/
namespace Hierarchy.DescentPackedProfileWide
open DescentPackedProfileTape DescentPackedProfileWindow DescentSIMDLookup DescentTerminalEpochBits
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory
open scoped Classical Fin.CommRing
noncomputable section
variable {A : Type} {C n : ℕ} (pin : Pins C n→A) (z : A→Bool) (d : ℕ) (extend : width C ≤ d)

def wideCell (q : ℕ) : Cell d := (cell pin z q).castLE (Nat.pow_le_pow_right (by decide) extend)

theorem cell_eq (q : ℕ) : (wideCell pin z d extend q).val=(cell pin z q).val := rfl

def widePin (R r j : ℕ) : A⊕Bool :=
  if j < d*R then
    if q : r*R+j/d < n then
      if b : j%d < width C then .inl (pin (⟨_,q⟩,⟨_,b⟩)) else .inr false
    else .inr false
  else .inr false

theorem wide_bit (R r j : ℕ) :
    (widePin pin d R r j).elim z id=(word d R (wideCell pin z d extend) r).val.testBit j := by
  by_cases span : j < d*R
  · have pos : 0 < d:=by by_contra! h;rw [show d=0 by omega] at span;simp at span
    let i : Fin R:=⟨j/d,(Nat.div_lt_iff_lt_mul pos).mpr (by simpa [Nat.mul_comm] using span)⟩
    have addr : j%d+d*i.val=j:=Nat.mod_add_div ..
    have low : j%d+d*i.val < d*(i.val+1) := by
      rw [Nat.mul_add,Nat.mul_one];have :=Nat.mod_lt j pos;omega
    have bit:=congrArg (fun t : ℕ=>t.testBit (j%d))
      (digit_encode (fun b : Fin R=>wideCell pin z d extend (r*R+b.val)) i)
    change (digit d i.val (word d R (wideCell pin z d extend) r).val).testBit (j%d)=_ at bit
    have under : j < d*(i.val+1) := addr ▸ low
    simp only [digit,Nat.testBit_div_two_pow,Nat.testBit_mod_two_pow,addr,under,decide_true,Bool.true_and,cell_eq] at bit
    rw [bit]
    by_cases slot : r*R+j/d < n
    · by_cases actual : j%d < width C
      · let q : Fin n:=⟨_,slot⟩
        change _=(cell pin z q.val).val.testBit (j%d)
        rw [active pin z q]
        have original:=congrFun ((DescentTerminalEpochBits.wordBits (width C)).apply_symm_apply (fun b=>z (pin (q,b))))
          (⟨j%d,actual⟩:Fin (width C))
        simpa only [widePin,ite_eq_left span,dite_eq_left slot,dite_eq_left actual,Sum.elim_inl,select_bit,DescentTerminalEpochBits.raw,Function.comp_apply,q] using original.symm
      · have bound:=(cell pin z (r*R+i.val)).isLt.trans_le
          (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_not_gt actual))
        simp [widePin,span,slot,actual,Nat.testBit_lt_two_pow bound]
    · simp [widePin,span,slot,i,inactive pin z (by omega : n ≤ r*R+j/d)]
  · have hi:=(word d R (wideCell pin z d extend) r).isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt span))
    simp [widePin,span,Nat.testBit_lt_two_pow hi]

def wideMemory {w : ℕ} (lo R : ℕ) (old : Memory w) : Memory w :=
  initialMemory (lo+slots n R) fun a=>
    if a < lo then old a else ((word d R (wideCell pin z d extend) ((a-lo))).val:Word w)

theorem wideAt {w : ℕ} (lo R r : ℕ) (old : Memory w) (pos : 0 < R) :
    wideMemory pin z d extend lo R old (lo+r)=((word d R (wideCell pin z d extend) r).val:Word w) := by
  by_cases inside : r < slots n R
  · simp [wideMemory,initialMemory,show lo+r < lo+slots n R by omega]
  · have gone : n/R<r := by unfold slots at inside;omega
    have stop:=(Nat.div_lt_iff_lt_mul pos).mp gone
    have zero : word d R (wideCell pin z d extend) r=0 := by
      apply (encode d R).symm.injective
      funext i
      change (encode d R).symm ((encode d R) _) i=_
      rw [Equiv.symm_apply_apply]
      apply Fin.ext
      have h:=digit_encode ((encode d R).symm 0) i
      simpa [cell_eq,inactive pin z (by omega : n ≤ r*R+i.val),digit] using h
    simp [wideMemory,initialMemory,zero,show ¬lo+r < lo+slots n R by omega]

theorem memory_pin {w : ℕ} (lo R r j : ℕ) (old : Memory w) (pos : 0 < R) (room : d*R ≤ w) :
    (widePin pin d R r j).elim z id=(wideMemory pin z d extend lo R old (lo+r)).val.testBit j := by
  rw [wideAt pin z d extend lo R r old pos,Fin.val_cast_of_lt
    ((word d R (wideCell pin z d extend) r).isLt.trans_le (Nat.pow_le_pow_right (by decide) room))]
  exact wide_bit pin z d extend R r j

end
end Hierarchy.DescentPackedProfileWide

end OAI
