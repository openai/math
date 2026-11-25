import OAI.Hierarchy.ProtocolRAMPurchaseNative
import OAI.Hierarchy.ProbeStageProgramSize
import OAI.Hierarchy.ProbeStageCheap
import OAI.Hierarchy.ProtocolRAMMarkCost

namespace OAI
/-! # Instruction, register, and public-slot bounds for the complete purchase processor -/

namespace Hierarchy.ProtocolRAM.PurchaseCT

open ProbeStage ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure

variable {z d k : ℕ}

set_option maxHeartbeats 1200000 in
theorem program_cheap (S : PurchaseSampler) (t : StageAt z d) (c : PassConfig k) (j : Fin (2*k)) :
    CheapCode (program S t c j) := by
  let s := embedded S t c
  let b := sign S t c
  let w := wordBits z d copies
  let n := 2^z
  let groups := Fintype.card (stageAt z d t).Group
  let m := (stageAt z d t).span
  let init := subdivisionProgram z d
  let gather := PurchaseTape.signedPrefix s b j w n groups m c.depth
  let dispatch := PurchaseStage.dispatch (PurchaseStage.layout s b n c.depth) w
  have staged : CheapCode (gather.seq dispatch) :=
    @cheap_seq w gather dispatch (@PurchaseTape.cheap_signed S.degree k s b j w n groups m c.depth)
      (@PurchaseStage.dispatch_cheap (PurchaseStage.layout s b n c.depth) w)
  exact @cheap_seq w init (gather.seq dispatch) (@subdivision_cheap z d) (@staged)

private theorem scan_text (w out n : ℕ) (e : Expr) : text (scan w out n e)=11+4*e.work := by
  obtain ⟨labels,regs,slots⟩ := scan_size w out n e
  simp only [text,labels,regs,slots]
  omega

theorem owners_text (w n groups m scratch : ℕ) (x : ProtocolRAMPurchaseOwners.Columns) :
    text (ProtocolRAMPurchaseOwners.program w n groups m scratch x)=161 := by
  simp only [ProtocolRAMPurchaseOwners.program,ProtocolRAMGeneratedWrite.program,text_seq,scan_text]; rfl

private theorem path_text {D : ℕ} (s : PurchaseTape.Plan D) (w n h : ℕ) :
    text (ProtocolRAM.program w (PurchaseColumns.passes s.directory s.source.base n h (PurchaseTape.edge s))) ≤
      15+(h+1)*(11+4*PurchaseColumns.fieldBudget D h) := by
  have small (j : Fin (h+1)) := PurchaseColumns.field_cost s.directory n (PurchaseTape.edge s) j
    (fun u => by simp [PurchaseTape.edge,ProtocolRAMPurchaseOwners.nextWord_work,Expr.work])
  have bound := columns_text w (PurchaseTape.count n D h) s.source.base (PurchaseColumns.fieldBudget D h)
    (List.ofFn (PurchaseColumns.field s.directory n h (PurchaseTape.edge s))) (by
      intro e he
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
      exact small j)
  simpa only [PurchaseColumns.passes,List.length_ofFn,PurchaseTape.count] using bound

def suffixText (D h k : ℕ) :=
  (161+(15+(h+1)*(11+4*PurchaseColumns.fieldBudget D h))) + (11+4*(10+15*(2*k))) + 525

theorem signed_text {D : ℕ} (s : PurchaseTape.Plan D) (b : PurchaseTape.Signed k) (j : Fin (2*k))
    (w n groups m h : ℕ) : text (PurchaseTape.signedPrefix s b j w n groups m h) ≤
      (161+(15+(h+1)*(11+4*PurchaseColumns.fieldBudget D h))) + (11+4*(10+15*(2*k))) := by
  simp only [PurchaseTape.signedPrefix,PurchaseTape.prefixCode,text_seq,owners_text,scan_text,
    PurchaseMarks.markExpr_work]
  exact Nat.add_le_add_right (Nat.add_le_add_left (path_text s w n h) 161) _

theorem dispatch_text (L : PurchaseStage.Dispatch) (w : ℕ) : text (PurchaseStage.dispatch L w)=525 := by
  have shape := GateColumns.code_size w (L.candidates*(4*L.depth+3)) L.source L.directory L.work L.tape
  have marks := MarkTape.native_text w L.tiles L.work L.first L.candidates L.tape
    (L.candidates*(4*L.depth+3)) L.marks
  rw [PurchaseStage.dispatch,text_seq]
  change text (ProtocolRAM.program w (GateColumns.passes L.source L.directory L.work
      (L.candidates*(4*L.depth+3)) L.tape)) + _ = _
  simp only [text,shape.1,shape.2.1,shape.2.2,marks.1,marks.2.1,marks.2.2]

def hardwareFactor (d D h k : ℕ) := (53+15000*rounds d)+suffixText D h k

/-- Only the CT subdivision text grows with the input length. The added sampler,
signed-mark and purchase opcodes depend on the sampler degree, depth and stock dimension. -/
theorem hardware_linear (S : PurchaseSampler) (t : StageAt z d) (c : PassConfig k) (j : Fin (2*k)) :
    text (program S t c j) ≤ hardwareFactor d S.degree c.depth k*2^z := by
  let s := embedded S t c
  let b := sign S t c
  let w := wordBits z d copies
  have ct := subdivision_program_size z d
  have signBound := signed_text s b j w (2^z) (Fintype.card (stageAt z d t).Group)
    (stageAt z d t).span c.depth
  have dispatch := dispatch_text (PurchaseStage.layout s b (2^z) c.depth) w
  have tail : suffixText S.degree c.depth k ≤ suffixText S.degree c.depth k*2^z := by
    simpa using Nat.mul_le_mul_left (suffixText S.degree c.depth k) (show 1≤2^z from Nat.one_le_two_pow)
  change text ((subdivisionProgram z d).seq ((PurchaseTape.signedPrefix s b j w (2^z)
    (Fintype.card (stageAt z d t).Group) (stageAt z d t).span c.depth).seq
    (PurchaseStage.dispatch (PurchaseStage.layout s b (2^z) c.depth) w))) ≤ _
  rw [text_seq,text_seq,dispatch,hardwareFactor,Nat.add_mul]
  have suff := Nat.add_le_add_right signBound 525
  exact Nat.add_le_add ct (suff.trans tail)

theorem hardware_fields (S : PurchaseSampler) (t : StageAt z d) (c : PassConfig k) (j : Fin (2*k)) :
    let p := program S t c j
    let bound := hardwareFactor d S.degree c.depth k*2^z
    p.labels≤bound ∧ p.registers≤bound ∧ p.slots≤bound := by
  have h := hardware_linear S t c j
  unfold text at h
  dsimp
  omega

end Hierarchy.ProtocolRAM.PurchaseCT

end OAI
