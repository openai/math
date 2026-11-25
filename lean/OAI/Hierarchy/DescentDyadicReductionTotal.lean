import OAI.Hierarchy.DescentDyadicReductionRun
import OAI.Hierarchy.DescentWalshDyadicChosen

namespace OAI
/-! # Reading every host sum from the terminal word array, with the clock of that same program -/
namespace Hierarchy.DescentPackedWalshReduction.Plan
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable (P : Plan)

private theorem digitFits {w t : ℕ} (height : P.height≤w) (limit : P.bits+t≤w) :
    (P.bits+t)*P.lanes t≤w := by
  by_cases large : P.scalar t
  · rw [(P.scalar_lanes large).1,Nat.mul_one]
    exact limit
  · change ¬P.height<8*(P.bits+t) at large
    have p:=P.positive
    have pos : 0<P.height/(8*(P.bits+t)) := Nat.div_pos (by omega) (by omega)
    have lanes : P.lanes t≤P.height/(8*(P.bits+t)) :=
      (Nat.pow_le_pow_right (by decide : 0<2) (Nat.min_le_right ..)).trans (Nat.pow_log_le_self 2 pos.ne')
    have room:=(Nat.le_div_iff_mul_le (show 0<8*(P.bits+t) by omega)).mp lanes
    nlinarith only [room,height,Nat.zero_le ((P.bits+t)*P.lanes t)]

theorem final_digit (x : Fin P.sites→Fin (2^P.axis)→ℕ) (hx : ∀i d,x i d<2^P.bits)
    {w : ℕ} (first : ℕ) (m : Memory w) (width : P.height≤w) (prec : P.bits+P.depth≤w)
    (stored : Stored (P.dataAt first P.depth) (P.hosts P.depth) (P.chunks P.depth)
      (P.lanes P.depth) (P.bits+P.depth) (P.values x P.depth) m) (d : Fin (2^P.axis)) :
    let L:=P.lanes P.depth
    digit (P.bits+P.depth) (d.val%L) (m (P.dataAt first P.depth+d.val/L)).val=
      ∑v : Fin P.sites,x v d := by
  let t:=P.depth
  let L:=P.lanes t
  have positive : 0<L:=Nat.two_pow_pos _
  have below : P.laneBits t≤P.axis:=Nat.min_le_left ..
  have cover : P.chunks t*L=2^P.axis:=by simp [L,chunks,lanes,←pow_add,Nat.sub_add_cancel below]
  let i:=d.val/L
  let j : Fin L:=⟨d.val%L,Nat.mod_lt _ positive⟩
  have within : i<P.chunks t:=(Nat.div_lt_iff_lt_mul positive).2 (by rw [cover];exact d.isLt)
  have row:=stored 0 (Nat.two_pow_pos _) i within
  simp only [Nat.zero_mul,Nat.add_zero] at row
  let f (j : Fin L) : Cell (P.bits+t):=(P.values x t 0 (i*L+j.val):Cell (P.bits+t))
  have lift : (encode (P.bits+t) L f).val<2^w:=(encode _ _ f).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (P.digitFits width prec))
  change digit (P.bits+t) j.val (m (P.dataAt first t+i)).val=_
  rw [row]
  change digit (P.bits+t) j.val (((encode (P.bits+t) L f).val:Word w)).val=_
  rw [Fin.val_cast_of_lt lift,digit_encode]
  have address : i*L+j.val=d.val := Nat.div_add_mod' ..
  have small:=P.value_bound x hx t 0 (i*L+j.val)
  calc
    (f j).val = P.values x t 0 (i*L+j.val) := Fin.val_cast_of_lt small
    _ = P.values x t 0 d.val := congrArg (P.values x t 0) address
    _ = _ := by
      simpa only [values,t,depth,Fin.cast_val_eq_self] using
        (DescentWalshDyadicSums.value_finish x d)

/-- The final central lookup receives the entire authentically stored word. -/
theorem final_word (x : Fin P.sites→Fin (2^P.axis)→ℕ) {w : ℕ} (first : ℕ) (mem : Memory w)
    (width : P.height≤w) (prec : P.bits+P.depth≤w)
    (stored : Stored (P.dataAt first P.depth) (P.hosts P.depth) (P.chunks P.depth)
      (P.lanes P.depth) (P.bits+P.depth) (P.values x P.depth) mem)
    (i : Fin (P.chunks P.depth)) :
    let s:=P.bits+P.depth
    let L:=P.lanes P.depth
    let word:=mem (P.dataAt first P.depth+i.val)
    word.val=packNat s L (fun j=>∑v,x v ((i.val*L+j):Fin (2^P.axis))) ∧ word.val<2^(s*L) := by
  let s:=P.bits+P.depth
  let L:=P.lanes P.depth
  let f:=fun j : ℕ=>∑v,x v ((i.val*L+j):Fin (2^P.axis))
  have insert : (fun j=>P.values x P.depth 0 (i.val*L+j))=f := by
    funext j
    let index := ((i.val*L+j : ℕ) : Fin (2^P.axis))
    simpa only [values,depth,f,index,Nat.cast_add,Nat.cast_mul] using
      (DescentWalshDyadicSums.value_finish x index)
  have row:=stored 0 (Nat.two_pow_pos _) i.val i.isLt
  simp only [Nat.zero_mul,Nat.add_zero] at row
  change mem (P.dataAt first P.depth+i.val)=(packNat s L _ : Word w) at row
  rw [insert] at row
  have fit : packNat s L f<2^(s*L):=(encode s L _).isLt
  have wordFit:=fit.trans_le (Nat.pow_le_pow_right (by decide : 0<2) (P.digitFits width prec))
  have exactWord : (mem (P.dataAt first P.depth+i.val)).val=packNat s L f :=
    (congrArg Fin.val row).trans (Fin.val_cast_of_lt wordFit)
  exact ⟨exactWord,exactWord.trans_lt fit⟩

theorem extract_key_room (t : ℕ) (live : 0<P.laneBits t) :
    (P.bits+t)*P.lanes t+P.laneBits t≤P.height/2 := by
  have unit : 0<P.bits+t:=Nat.add_pos_left P.positive _
  have ratio : 0<P.height/(8*(P.bits+t)):=by
    apply Nat.pos_of_ne_zero
    intro hz
    simp [laneBits,hz] at live
  have width : P.lanes t≤P.height/(8*(P.bits+t)) :=
    (Nat.pow_le_pow_right (by decide) (Nat.min_le_right ..)).trans (Nat.pow_log_le_self 2 ratio.ne')
  have paid:=(Nat.le_div_iff_mul_le (show 0<8*(P.bits+t) by omega)).mp width
  have tag : P.laneBits t≤(P.bits+t)*P.lanes t := calc
    P.laneBits t ≤ 2^(P.laneBits t) := Nat.lt_two_pow_self.le
    _ = P.lanes t := rfl
    _ ≤ _ := Nat.le_mul_of_pos_left (P.lanes t) unit
  apply (Nat.le_div_iff_mul_le (by decide)).2
  nlinarith only [tag,paid,Nat.zero_le ((P.bits+t)*P.lanes t)]

/-- A complete pass starting with the true host input; no scalar arithmetic
table is allocated at the late, high-precision levels. -/
theorem full (x : Fin P.sites→Fin (2^P.axis)→ℕ) (hx : ∀i d,x i d<2^P.bits)
    {w : ℕ} (root first : ℕ) (m old : Memory w) (stat : P.headerAt root P.depth≤first)
    (space : P.dataAt first (P.depth+1)<2^w) (width : P.height≤w) (prec : P.bits+P.depth≤w)
    (rom : ∀j<first,m j=P.mount root old P.depth j)
    (base : Stored first (P.hosts 0) (P.chunks 0) (P.lanes 0) P.bits
      (fun v d=>DescentWalshDyadicSums.sample x v (d : Fin (2^P.axis))) m) :
    let dst:=P.state root first m P.depth
    (P.code w root first P.depth).Exec m dst (P.duration P.depth) ∧
      (∀d : Fin (2^P.axis),let L:=P.lanes P.depth
        digit (P.bits+P.depth) (d.val%L) (dst (P.dataAt first P.depth+d.val/L)).val=∑v,x v d) ∧
      (∀j<first,dst j=m j) ∧ ∀j,P.dataAt first (P.depth+1)≤j→dst j=m j := by
  have input_eq : P.values x 0 =
      (fun (v d : ℕ) => DescentWalshDyadicSums.sample x v (d : Fin (2^P.axis))) := by
    funext v d
    exact DescentWalshDyadicSums.value_zero x v _
  obtain ⟨run,slots,lo,hi⟩:=P.runTo x hx root first m old P.depth le_rfl stat space rom
    (by simpa only [input_eq] using base)
  exact ⟨@run,P.final_digit x hx first _ width prec slots,lo,hi⟩

/-- Install the explicit public ROM into the same initial memory containing
the old score words, then run the entire chronological program. -/
theorem full_mounted (x : Fin P.sites→Fin (2^P.axis)→ℕ) (hx : ∀i d,x i d<2^P.bits)
    {w : ℕ} (root first : ℕ) (old : Memory w) (stat : P.headerAt root P.depth≤first)
    (space : P.dataAt first (P.depth+1)<2^w) (width : P.height≤w) (prec : P.bits+P.depth≤w)
    (base : Stored first (P.hosts 0) (P.chunks 0) (P.lanes 0) P.bits
      (fun v d=>DescentWalshDyadicSums.sample x v (d : Fin (2^P.axis))) old) :
    let initial:=P.mount root old P.depth
    let dst:=P.state root first initial P.depth
    (P.code w root first P.depth).Exec initial dst (P.duration P.depth) ∧
      (∀d : Fin (2^P.axis),let L:=P.lanes P.depth
        digit (P.bits+P.depth) (d.val%L) (dst (P.dataAt first P.depth+d.val/L)).val=∑v,x v d) ∧
      (∀j<first,dst j=initial j) ∧ ∀j,P.dataAt first (P.depth+1)≤j→dst j=old j := by
  have loaded : Stored first (P.hosts 0) (P.chunks 0) (P.lanes 0) P.bits
      (fun v d=>DescentWalshDyadicSums.sample x v (d : Fin (2^P.axis))) (P.mount root old P.depth) := by
    intro v hv i hi
    rw [P.mount_high root old P.depth (first+v*P.chunks 0+i) (by omega)]
    exact base v hv i hi
  obtain ⟨exec,digits,lo,hi⟩:=P.full x hx root first (P.mount root old P.depth) old stat space
    width prec (fun _ _=>rfl) loaded
  refine ⟨@exec,digits,lo,?_⟩
  intro j hj
  exact (hi j hj).trans (P.mount_high root old P.depth j (stat.trans ((P.data_mono first (Nat.zero_le _)).trans hj)))

private theorem duration_sum (t : ℕ) : P.duration t=4+∑s ∈ Finset.range t,P.ticks s := by
  induction t with
  | zero=>simp [duration]
  | succ t ih=>simp only [duration,ih,Finset.sum_range_succ,Nat.add_assoc]

theorem clock (W K : ℕ) (scale : W≤K*P.height) (host : P.sites≤2^W) (precision : P.bits≤W+1) :
    P.duration P.depth*W≤4*W+2008*(P.sites+1)*W+
      25600*K*(P.sites+1)*2^P.axis*(P.bits+1)+12800*K*2^P.axis*(W+1)^2 := by
  have each (t : ℕ) : P.ticks t≤4+90*2^(P.depth-(t+1))*
      2^(P.axis-DescentPackedWalsh.laneBits P.axis P.height (P.bits+t+1)) := by
    have count : 2^(P.axis-DescentPackedWalsh.laneBits P.axis P.height (P.bits+t+1))=P.chunks (t+1) := by
      simp only [chunks,laneBits,DescentPackedWalsh.laneBits,Nat.add_assoc]
    rw [count]
    unfold ticks pageWords hosts
    split <;> simp only [Nat.mul_assoc] <;> omega
  have sum:=(Finset.sum_le_sum (fun t (_:t∈Finset.range P.depth)=>Nat.mul_le_mul_right W (each t))).trans
    (DescentWalshDyadicBudget.padded_reduction P.sites P.axis P.bits W P.height K scale host precision)
  rw [P.duration_sum,Nat.add_mul,Finset.sum_mul]
  omega

/-- The entire finite static header consists of three pointer words per
produced row and two short tables per live packed level. -/
theorem step_header_bound (t : ℕ) : P.headerSize t≤3*(P.hosts (t+1)*P.chunks (t+1))+2*2^(P.height/2) := by
  by_cases late : P.scalar t
  · simp [headerSize,late]
  · have pay : 8*(P.bits+t)≤P.height := Nat.le_of_not_gt late
    let A:=P.bits+t
    have positive : 0<A:=by have g:=P.positive;dsimp [A];omega
    have ratio : 0<P.height/(8*A):=Nat.div_pos pay (by omega)
    have lbound : P.lanes t≤P.height/(8*A):=
      (Nat.pow_le_pow_right (by decide) (Nat.min_le_right ..)).trans (Nat.pow_log_le_self 2 ratio.ne')
    have volume:=(Nat.le_div_iff_mul_le (show 0<8*A by omega)).mp lbound
    have cap : (P.tile t).payload=A*P.lanes t:=by unfold Tile.payload;rw [P.old_lanes];rfl
    have index : (P.tile t).subdivisions≤A*P.lanes t := by
      calc
        _ ≤ P.laneBits t := Nat.sub_le ..
        _ ≤ P.lanes t := Nat.lt_two_pow_self.le
        _ ≤ A*P.lanes t := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (P.lanes t) positive
    have key : (P.tile t).keyBits≤3*(A*P.lanes t) := by
      unfold Tile.keyBits
      rw [P.old_lanes]
      change (P.tile t).subdivisions+(A+A)*P.lanes t≤_
      rw [Nat.add_mul];omega
    have raw : A*P.lanes t≤P.height/2 := (Nat.le_div_iff_mul_le (by decide)).2 (by nlinarith only [volume])
    have tag : (P.tile t).keyBits≤P.height/2 := (Nat.le_div_iff_mul_le (by decide)).2 (by nlinarith only [key,volume])
    have r:=Nat.pow_le_pow_right (by decide : 0<2) (cap.le.trans raw)
    have k:=Nat.pow_le_pow_right (by decide : 0<2) tag
    rw [headerSize,ite_eq_right late,Tile.span,P.rows];omega

theorem static_extent (root first n : ℕ) : P.headerAt root n+3*first≤
    root+3*P.dataAt first (n+1)+2*n*2^(P.height/2) := by
  induction n with
  | zero=>simp only [headerAt,dataAt,Nat.mul_zero,Nat.zero_mul,Nat.add_zero];omega
  | succ n ih=>
    have next:=P.step_header_bound n
    change P.headerAt root n+P.headerSize n+3*first≤
      root+3*(P.dataAt first (n+1)+P.hosts (n+1)*P.chunks (n+1))+2*(n+1)*2^(P.height/2)
    rw [Nat.mul_add,Nat.mul_succ,Nat.add_mul]
    omega

end
end Hierarchy.DescentPackedWalshReduction.Plan

end OAI
