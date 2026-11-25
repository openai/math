import OAI.ThreeFlat.Diagonal.CompressorChildOrder

namespace OAI
/-! # Numerical deletion of the public color digit in a shrinking child index -/
namespace ThreeFlat.Diagonal.CompressorPacking.Owner
open Computability.VPVNP.Compression Native

def removeDigit (x p : ℕ) := x%2^p+2^p*(x/2^(p+1))

theorem removeDigit_bit (x p i : ℕ) :
    (removeDigit x p).testBit i=if i<p then x.testBit i else x.testBit (i+1) := by
  let k := 2^p
  have hk : 0<k := Nat.two_pow_pos p
  have lo : (removeDigit x p)%k=x%k := by simp [removeDigit,k,Nat.add_mod]
  have hi : (removeDigit x p)/k=x/2^(p+1) := by
    unfold removeDigit
    rw [show 2^p=k from rfl,Nat.add_comm,Nat.mul_add_div hk,Nat.div_eq_of_lt (Nat.mod_lt _ hk),Nat.add_zero]
  by_cases lt : i<p
  · have h := congrArg (fun n=>n.testBit i) lo
    simpa [k,Nat.testBit_mod_two_pow,lt] using h
  · have h := congrArg (fun n=>n.testBit (i-p)) hi
    rw [ite_eq_right lt]
    simpa only [k,Nat.testBit_div_two_pow,show i-p+p=i by omega,
      show i-p+(p+1)=i+1 by omega] using h

theorem bitOfOrdinal {c : ℕ} (u : BitWord c) (j : Fin c) :
    (tagOrdinal c u).val.testBit j.val=decide (u j=1) := by
  have hu := congrFun (decodeOrdinal c (tagOrdinal c u)) j
  rw [Equiv.symm_apply_apply] at hu
  change u j=(if ((tagOrdinal c u).val >>> 0).testBit j.val then 1 else 0) at hu
  rw [Nat.shiftRight_zero] at hu
  cases h : (tagOrdinal c u).val.testBit j.val <;> simp [h] at hu ⊢ <;> simp [hu]

theorem removeOrdinal {c : ℕ} (p : Fin (c+1)) (u : BitWord (c+1)) :
    (tagOrdinal c (fun j=>u (p.succAbove j))).val=removeDigit (tagOrdinal (c+1) u).val p.val := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [removeDigit_bit]
  by_cases hi : i<c
  · let j : Fin c := ⟨i,hi⟩
    rw [show ((tagOrdinal c fun j=>u (p.succAbove j)).val).testBit i =
      decide (u (p.succAbove j)=1) from bitOfOrdinal _ j]
    by_cases hp : i<p.val
    · rw [ite_eq_left hp,Fin.succAbove_of_castSucc_lt _ _ (show j.castSucc<p from hp)]
      exact (bitOfOrdinal u j.castSucc).symm
    · rw [ite_eq_right hp,Fin.succAbove_of_le_castSucc _ _ (show p≤j.castSucc by exact Nat.le_of_not_gt hp)]
      exact (bitOfOrdinal u j.succ).symm
  · have lt2 : ¬i<p.val := by have := p.isLt; omega
    rw [ite_eq_right lt2]
    exact (Nat.testBit_lt_two_pow ((tagOrdinal c _).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)))).trans
        (Nat.testBit_lt_two_pow ((tagOrdinal (c+1) _).isLt.trans_le
          (Nat.pow_le_pow_right (by decide) (by omega : c+1≤ i+1)))).symm

variable {V H Tag L : Type*} {c d : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d (c+1)) (lay : Bool) (v : Site V Tag L)
omit [AddCommGroup H] in
theorem freeOrdinal_value (thin : Bool) (i : Fin d) (u : freeWords P lay v thin i) :
    (freeOrdinal P lay v thin i u).val =
      removeDigit (tagOrdinal (c+1) u.val).val (chosenColor P lay v thin i).val :=
  removeOrdinal (chosenColor P lay v thin i) u.val

def indexValue (i : Index d (c+1)) :=
  ((if i.1 then d else 0)+i.2.1.val)*2^c+
    removeDigit (tagOrdinal (c+1) i.2.2).val (chosenColor P lay v i.1 i.2.1).val

omit [AddCommGroup H] in
theorem indexOrder_value (i : {z : Index d (c+1) // valid P lay v z}) :
    (indexOrder P lay v i).val=indexValue P lay v i.val := by
  rcases i with ⟨⟨thin,h,u⟩,ok⟩
  change (freeOrdinal P lay v thin h ⟨u,ok⟩).val+
    2^c*(h.val+d*(finTwoEquiv.symm thin).val)=_
  rw [freeOrdinal_value]
  have off : (finTwoEquiv.symm false).val = 0 := rfl
  have on : (finTwoEquiv.symm true).val = 1 := rfl
  cases thin <;> simp [indexValue,off,on] <;> ring

omit [AddCommGroup H] in
theorem childNumber_value (x : {z // P.placement lay z=v}) :
    ((childOrder P lay v).symm x).val=indexValue P lay v (index P lay x.val) :=
  indexOrder_value P lay v ((children P lay v).symm x)

omit [AddCommGroup H] in
private theorem child_base (i : Index d (c+1)) :
    (child P lay v (i.1,i.2.1,0)).1.1=(child P lay v i).1.1 := by
  rcases i with ⟨thin,h,u⟩
  cases thin <;> rfl

omit [AddCommGroup H] in
theorem chosenColor_index (x : {z // P.placement lay z=v}) :
    chosenColor P lay v (index P lay x.val).1 (index P lay x.val).2.1=P.color x.val.1.1 := by
  unfold chosenColor
  have restored : child P lay v (index P lay x.val) = x.val :=
    (congrArg (fun site => child P lay site (index P lay x.val)) x.property).symm.trans
      (child_index P lay x.val)
  exact (congrArg P.color (child_base P lay v (index P lay x.val))).trans
    (congrArg (fun z : Position V H Tag L (c+1) => P.color z.1.1) restored)

omit [AddCommGroup H] in
theorem childNumber_physical (x : {z // P.placement lay z=v}) :
    ((childOrder P lay v).symm x).val =
      (if P.thick x.val then (P.slotLabel x.val.2.2).val
        else d + (port P lay (P.assignedBundle x.val)).2.val)*2^c +
      removeDigit (tagOrdinal (c+1) x.val.2.1).val (P.color x.val.1.1).val := by
  rw [childNumber_value,indexValue,chosenColor_index]
  by_cases thick : P.thick x.val <;> simp [index,thick]

end ThreeFlat.Diagonal.CompressorPacking.Owner

end OAI
