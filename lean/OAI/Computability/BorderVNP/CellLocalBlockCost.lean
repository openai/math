import OAI.Computability.BorderVNP.CellLocalPrepareCost
import OAI.Computability.BorderVNP.CellEmitSequenceCost
import OAI.Computability.BorderVNP.CellEmitStatementCost

/-! # Sharp native cost of printing one prepared private box

The box is traversed once in factor order. Only the one-copy bodies are printed under
the loop header. At each ordinal the call sends the prepared scalar header and that
factor's own table to the local printer.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit.Local

open ExactQuantumFactoring.BitStackProgram
open CellMacro.Generator (serialized)

private abbrev ctxCode := prodCode paramsCode fieldsCode
private abbrev tailCode := prodCode Nat.bits (listCode Typed.factor)

private noncomputable abbrev copiesP :=
  (Procedure.first Nat.bits (listCode Typed.factor)).comp (Procedure.second ctxCode tailCode)

private noncomputable abbrev factorsP :=
  (Procedure.second Nat.bits (listCode Typed.factor)).comp (Procedure.second ctxCode tailCode)

private theorem fields_read (x : BlockData) : copiesP.meter x ≤ 4000*((blockDataCode x).length+1) ∧
    factorsP.meter x ≤ 4000*((blockDataCode x).length+1) := by
  have h := Procedure.meter_second ctxCode tailCode x
  have c := Procedure.meter_first Nat.bits (listCode Typed.factor) x.2
  have f := Procedure.meter_second Nat.bits (listCode Typed.factor) x.2
  have hc := Procedure.meter_comp (Procedure.first Nat.bits (listCode Typed.factor)) (Procedure.second ctxCode tailCode) x
  have hf := Procedure.meter_comp (Procedure.second Nat.bits (listCode Typed.factor)) (Procedure.second ctxCode tailCode) x
  change copiesP.meter x ≤ 6*(_+(Procedure.first Nat.bits (listCode Typed.factor)).meter x.2) at hc
  change factorsP.meter x ≤ 6*(_+(Procedure.second Nat.bits (listCode Typed.factor)).meter x.2) at hf
  change _ ≤ 300*((blockDataCode x).length+1) at h
  have hw : (tailCode x.2).length ≤ (blockDataCode x).length := by
    simp only [blockDataCode,tailCode,prodCode,pairBits_length]; omega
  change _ ≤ 10*((tailCode x.2).length+1) at c
  change _ ≤ 300*((tailCode x.2).length+1) at f
  omega

set_option maxHeartbeats 2400000 in
/-- A prepared block costs one indexed traversal of its one-copy factor list.
The separate input-sensitive local printer bound is required only for the factors
actually present at their real ordinals. -/
theorem blockPrinter_meter (mode : Pass) : ∃ K : ℕ, ∀ (x : BlockData) (P : ℕ),
    (∀ i : Fin x.2.2.length, (printer mode).meter (x.1,i.val,(x.2.2[i.val]'i.isLt)) ≤ P) →
    (blockPrinter mode).meter x ≤ K*(x.2.2.length+1)*((blockDataCode x).length+1)^9*(P+1)^2 := by
  obtain ⟨I,item⟩ := itemPacket_measured
  obtain ⟨M,seqBound⟩ := meter_sequenceMapIdx blockDataCode Typed.factor (Factor.truth [] [])
  let row := (printer mode).comp itemPacket
  let tree := fun (b : BlockData) (j : ℕ) (f : Factor) => body mode b.1.1 f
    (index (b.1,j,f) 0) (offset (b.1,j,f) 0) (.index 0)
  let cmds := sequenceMapIdx (f:=tree) (.truth [] []) factorsP row
  let overhead := 48*I+4^9+4043
  let hdr := 10^19*(4001+layoutSize (.lit 0))
  refine ⟨10^20*(hdr+M*overhead+1),?_⟩
  intro x P hP
  let S := (blockDataCode x).length+1
  let N := x.2.2.length
  let D := S^9*(P+1)^2
  let Z := (N+1)*D
  let R := prodCode blockDataCode (listCode Typed.factor)
  have hs : 0 < S := Nat.zero_lt_succ _
  have hlist : (listCode Typed.factor x.2.2).length+1 ≤ S := by
    simp only [S,blockDataCode,prodCode,pairBits_length]; omega
  have hn : N+1 ≤ S := by have := list_length_le_code Typed.factor x.2.2; dsimp [N]; omega
  have hraw : (R (x,x.2.2)).length+1 ≤ 4*S := by
    change (pairBits (blockDataCode x) (listCode Typed.factor x.2.2)).length+1 ≤ _
    rw [pairBits_length]
    dsimp only [S] at hlist ⊢; omega
  have hw (i : Fin x.2.2.length) :
      (prodCode blockDataCode (prodCode Nat.bits Typed.factor) (x,i.val,(x.2.2[i.val]'i.isLt))).length+1 ≤ 8*S := by
    have hb : i.val.bits.length ≤ i.val := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr Nat.lt_two_pow_self
    have ht := code_le_of_mem Typed.factor (List.getElem_mem (l:=x.2.2) i.isLt)
    have hi := i.isLt
    change (pairBits (blockDataCode x) (pairBits i.val.bits (Typed.factor (x.2.2[i.val]'i.isLt)))).length+1 ≤ _
    rw [pairBits_length,pairBits_length]
    dsimp only [S] at hn hlist ⊢; omega
  let C := 6*(8*I*S+P)
  have rcost (i : Fin x.2.2.length) : row.cost (x,i.val,(x.2.2[i.val]'i.isLt)) ≤ C := by
    have it := (item (x,i.val,(x.2.2[i.val]'i.isLt))).trans (by
      simpa only [pow_one] using Nat.mul_le_mul_left I (hw i))
    have hp := hP i
    have hm := Procedure.meter_comp (printer mode) itemPacket (x,i.val,(x.2.2[i.val]'i.isLt))
    change row.meter (x,i.val,(x.2.2[i.val]'i.isLt)) ≤ 6*(itemPacket.meter (x,i.val,(x.2.2[i.val]'i.isLt))+
      (printer mode).meter (x.1,i.val,(x.2.2[i.val]'i.isLt))) at hm
    change itemPacket.meter (x,i.val,(x.2.2[i.val]'i.isLt)) ≤ I*(8*S) at it
    apply (Procedure.cost_le_meter ..).trans hm |>.trans
    rw [show C=6*(I*(8*S)+P) by dsimp [C]; ring]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add it hp)
  have rout (i : Fin x.2.2.length) : (serialized 8 (tree x i (x.2.2[i.val]'i.isLt))).length ≤ P := by
    have h := Procedure.words_le_meter (printer mode) (x.1,i.val,(x.2.2[i.val]'i.isLt))
    change _+(serialized 8 (tree x i (x.2.2[i.val]'i.isLt))).length+1 ≤ _ at h
    have := hP i
    omega
  have seq := seqBound (f:=tree) factorsP row x rout rcost
  change cmds.meter x ≤ M*(factorsP.meter x+(N+1)*(C+((R (x,x.2.2)).length+1)^9+
    (Procedure.tabSpan R N (x,x.2.2) P)^2+1)) at seq
  have sD : S ≤ D := (show S ≤ S^9 from by simpa only [pow_one] using (Nat.pow_le_pow_right hs (show 1 ≤ 9 by decide))).trans
    (Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos P) _))
  have powD : S^9 ≤ D := Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos P) _)
  have pD : P+1 ≤ D := (show P+1 ≤ (P+1)^2 from by simpa only [pow_one] using (Nat.pow_le_pow_right (Nat.succ_pos P) (show 1 ≤ 2 by decide))).trans
    (Nat.le_mul_of_pos_left _ (pow_pos hs _))
  have hC : C ≤ (48*I+6)*D := by
    have hi := Nat.mul_le_mul_left I sD
    dsimp [C]
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
    omega
  have hR : ((R (x,x.2.2)).length+1)^9 ≤ 4^9*D := by
    have h := Nat.pow_le_pow_left hraw 9
    rw [Nat.mul_pow] at h
    exact h.trans (Nat.mul_le_mul_left _ powD)
  have hS : Procedure.tabSpan R N (x,x.2.2) P ≤ 6*(S*(P+1)) := by
    have hmul := Nat.mul_le_mul_right (P+1) hn
    have hle : S ≤ S*(P+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos P)
    unfold Procedure.tabSpan; omega
  have hS2 : (Procedure.tabSpan R N (x,x.2.2) P)^2 ≤ 36*D := by
    calc _ ≤ (6*(S*(P+1)))^2 := Nat.pow_le_pow_left hS 2
         _ = 36*(S^2*(P+1)^2) := by ring
         _ ≤ 36*D := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hs (by decide)))
  have dpos : 1 ≤ D := hs.trans_le sD
  have dZ : D ≤ Z := Nat.le_mul_of_pos_left _ (Nat.succ_pos N)
  have hx := fields_read x
  have hv : C+((R (x,x.2.2)).length+1)^9+(Procedure.tabSpan R N (x,x.2.2) P)^2+1
      ≤ (48*I+4^9+43)*D := by
    simp only [Nat.add_mul] at hC ⊢
    norm_num at hR ⊢
    omega
  have hsum := Nat.mul_le_mul_left (N+1) hv
  rw [Nat.mul_left_comm (N+1) (48*I+4^9+43) D] at hsum
  change _ ≤ (48*I+4^9+43)*Z at hsum
  have hf : factorsP.meter x ≤ 4000*Z := hx.2.trans (Nat.mul_le_mul_left _ (sD.trans dZ))
  have hv' : factorsP.meter x+(N+1)*(C+((R (x,x.2.2)).length+1)^9+(Procedure.tabSpan R N (x,x.2.2) P)^2+1)
      ≤ overhead*Z := by dsimp [overhead]; simp only [Nat.add_mul] at hsum ⊢; omega
  have hc := seq.trans (Nat.mul_le_mul_left M hv')
  have hl := meter_litAddr copiesP x
  have cp := hx.1.trans (Nat.mul_le_mul_left 4000 (sD.trans dZ))
  have hhdr : addrMeter (litAddr copiesP) x ≤ hdr*Z := by
    have hsmall := Nat.le_mul_of_pos_right (layoutSize (.lit 0)) (dpos.trans dZ)
    dsimp [hdr]
    simp only [Nat.mul_assoc,Nat.add_mul]
    omega
  have hloop := meter_loopStmt (litAddr copiesP) cmds x
  change (blockPrinter mode).meter x ≤ 10^20*(addrMeter (litAddr copiesP) x+cmds.meter x+1) at hloop
  apply hloop.trans
  have hb : addrMeter (litAddr copiesP) x+cmds.meter x+1 ≤ (hdr+M*overhead+1)*Z := by
    rw [← Nat.mul_assoc] at hc
    simp only [Nat.add_mul,Nat.one_mul]; omega
  calc 10^20*(addrMeter (litAddr copiesP) x+cmds.meter x+1) ≤ 10^20*((hdr+M*overhead+1)*Z) := Nat.mul_le_mul_left _ hb
       _ = _ := by dsimp [Z,D,N,S]; ring

end CellSparse.Packet.Emit.Local

end BorderVNP
end Computability
end OAI
