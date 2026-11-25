import OAI.Computability.BorderVNP.CellLocalVisitMeter
import OAI.Computability.BorderVNP.CellEmitSequenceCost

/-! # Operational clock for traversing resolved private boxes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit.Local

open ExactQuantumFactoring.BitStackProgram

set_option maxHeartbeats 3600000
set_option maxRecDepth 30000

/-- One actual box traversal, including index preparation, global prefix computation,
the chosen fragment printer, storage of compact output prefixes and concatenation.
A degree-fourteen per-fragment charge is sufficient, even when used as the bound
on the emitted fragment's own bit length. -/
theorem sweepPrinter_meter (mode : Pass) :
    ∃ K : ℕ, ∀ (x : SweepInput) (P : ℕ),
      (∀ i : Fin x.2.blocks.length, (fragment mode).meter (visit x i x.2.blocks[i]) ≤
        P*(sweepSpan x+1)^14) →
      (sweepPrinter mode).meter x ≤ K*(P+1)^2*(sweepSpan x+1)^31 := by
  let dir := Procedure.second paramsCode Typed.directory
  let rows := getBlocks.comp dir
  let step := (fragment mode).comp visitPacket
  let emit := fun (x : SweepInput) (i : ℕ) (b : BoxBlock) =>
    b.fragment (((x.2.blocks.take i).map fun z => z.copies*z.factors.length).sum) (body mode x.1)
  obtain ⟨G,hG⟩ := measured_sweepBlocks
  obtain ⟨V,hV⟩ := measured_visitPacket
  obtain ⟨Q,hQ⟩ := meter_sequenceMapIdx sweepCode blockCode (⟨0,0,0,[]⟩ : BoxBlock)
  let J := 6*(V*3^30+1)
  refine ⟨Q*(G+J+4^9+64+1),?_⟩
  intro x P hP
  let t := sweepSpan x+1
  let n := x.2.blocks.length
  let a := (prodCode sweepCode (listCode blockCode) (x,x.2.blocks)).length
  let z := (P+1)^2*t^30
  have ht : 1 ≤ t := Nat.succ_le_succ (Nat.zero_le _)
  have hm (i j : ℕ) (h : i ≤ j) : t^i ≤ t^j := Nat.pow_le_pow_right ht h
  have hz : t^30 ≤ z := by
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hpt : P*t^14 ≤ z := Nat.mul_le_mul (by nlinarith only [Nat.zero_le (P*P)]) (hm 14 30 (by decide))
  have hn : n+1 ≤ t := by
    have h := list_length_le_code blockCode x.2.blocks
    dsimp only [n,t,sweepSpan,blockSpan]
    omega
  have ha : a+1 ≤ 4*t := by
    change (prodCode (prodCode paramsCode Typed.directory) (listCode blockCode) (x,x.2.blocks)).length+1 ≤ _
    rw [prodCode,pairBits_length,prodCode,pairBits_length]
    dsimp only [t,sweepSpan,blockSpan]
    omega
  have hstep (i : Fin x.2.blocks.length) : step.cost (x,i.val,(x.2.blocks[i.val]'i.isLt)) ≤ J*z := by
    let arg := (x,i.val,(x.2.blocks[i.val]'i.isLt))
    have h₁ := Procedure.meter_comp (fragment mode) visitPacket arg
    have hv := (hV arg).trans (Nat.mul_le_mul_left V (Nat.pow_le_pow_left (visitSpan_le x i) 30))
    rw [Nat.mul_pow,←Nat.mul_assoc] at hv
    change visitPacket.meter arg ≤ V*3^30*t^30 at hv
    have hv' := hv.trans (Nat.mul_le_mul_left (V*3^30) hz)
    have hf := (hP i).trans hpt
    change (fragment mode).meter (visit x i (x.2.blocks[i.val]'i.isLt)) ≤ z at hf
    change step.meter arg ≤ 6*(visitPacket.meter arg+(fragment mode).meter (visit x i (x.2.blocks[i.val]'i.isLt))) at h₁
    exact (Procedure.cost_le_meter step arg).trans (h₁.trans (by
      change _ ≤ 6*(V*3^30+1)*z
      rw [Nat.mul_assoc,Nat.add_mul,Nat.one_mul]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add hv' hf)))
  have hword (i : Fin x.2.blocks.length) :
      (CellMacro.Generator.serialized 8 (emit x i (x.2.blocks[i.val]'i.isLt))).length ≤ P*t^14 := by
    have h := (fragment mode).words_le_meter (visit x i (x.2.blocks[i.val]'i.isLt))
    have hf := hP i
    change _+(CellMacro.Generator.serialized 8 (emit x i (x.2.blocks[i.val]'i.isLt))).length+1 ≤ _ at h
    exact (show (CellMacro.Generator.serialized 8 (emit x i (x.2.blocks[i.val]'i.isLt))).length ≤
      (fragment mode).meter (visit x i (x.2.blocks[i.val]'i.isLt)) by omega).trans hf
  have hseq := hQ (f:=emit) rows step x hword hstep
  let span := Procedure.tabSpan (prodCode sweepCode (listCode blockCode)) n (x,x.2.blocks) (P*t^14)
  have ht₁ : t ≤ t^15 := by simpa only [pow_one] using hm 1 15 (by decide)
  have hspan : span ≤ 8*(P+1)*t^15 := by
    change a+n+(n+1)*(P*t^14+1)+1 ≤ _
    calc
      _ ≤ 4*t+t+t*(P*t^14+1)+1 := by
        have hp := Nat.mul_le_mul_right (P*t^14+1) hn
        omega
      _ = 6*t+P*t^15+1 := by ring
      _ ≤ 7*t^15+P*t^15 := by omega
      _ ≤ 8*(P+1)*t^15 := by nlinarith only [Nat.zero_le (P*t^15),Nat.zero_le (t^15)]
  have hspan₂ := Nat.pow_le_pow_left hspan 2
  rw [show (8*(P+1)*t^15)^2 = 64*z by dsimp [z]; ring] at hspan₂
  have ha₉ := Nat.pow_le_pow_left ha 9
  rw [Nat.mul_pow] at ha₉
  have ha' := ha₉.trans (Nat.mul_le_mul_left (4^9) ((hm 9 30 (by decide)).trans hz))
  have hone : 1 ≤ z := (Nat.one_le_pow _ _ ht).trans hz
  have hrow := (hG x).trans (Nat.mul_le_mul_left G hz)
  change rows.meter x ≤ G*z at hrow
  have hwork : J*z+(a+1)^9+span^2+1 ≤ (J+4^9+64+1)*z := by
    simp only [Nat.add_mul,Nat.one_mul]
    omega
  have hscaled := Nat.mul_le_mul hn hwork
  have hbase := Nat.le_mul_of_pos_left z (show 0 < t from ht)
  have htotal : rows.meter x+(n+1)*(J*z+(a+1)^9+span^2+1) ≤
      (G+J+4^9+64+1)*(t*z) := by
    have hR := hrow.trans (Nat.mul_le_mul_left G hbase)
    rw [Nat.mul_left_comm t (J+4^9+64+1)] at hscaled
    rw [show G+J+4^9+64+1=G+(J+4^9+64+1) by omega,Nat.add_mul G]
    exact Nat.add_le_add hR hscaled
  unfold sweepPrinter
  rw [Procedure.meter_congrFun]
  apply hseq.trans
  change Q*(rows.meter x+(n+1)*(J*z+(a+1)^9+span^2+1)) ≤ Q*(G+J+4^9+64+1)*(P+1)^2*t^31
  rw [← show Q*((G+J+4^9+64+1)*(t*z)) = Q*(G+J+4^9+64+1)*(P+1)^2*t^31 by dsimp only [z]; ring]
  exact Nat.mul_le_mul_left Q htotal

end CellSparse.Packet.Emit.Local

end BorderVNP
end Computability
end OAI
