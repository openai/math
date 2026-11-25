import OAI.ThreeFlat.RAM.HistoryOperandScan
import OAI.ThreeFlat.RAM.HistoryBatchTape
import OAI.ThreeFlat.RAM.HistoryPortMap
import OAI.ThreeFlat.RAM.HistoryPairSeeds

namespace OAI
/-! # Width independence of the six auxiliary history opcodes -/

namespace ThreeFlat.RAM.HistorySelectedOps

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr HistoryOperandScan
open scoped Fin.CommRing

noncomputable section

/-- Additional selected generators. A batch seed can generate later commands
on this same tape. The final two primitives copy or generate consecutive
source addresses without repeatedly materializing an identity pin vector. -/
def auxiliary (W : ℕ) : List (Term W 1 1) :=
  let basis (ty : Bool) (stride : ℕ) := program (HistoryBatchTape.program W ty) (0 : Fin 1)
    stride ![.header 2,.row,.column]
  let port := program (HistoryPortMap.word W 1) (0 : Fin 1) 1 ![.row,.header 2,.header 3,.header 4]
  let pair := program (HistoryPairSeeds.program W 0) (0 : Fin 1) 1 ![.row,.header 2,.header 3]
  let sourceAddress := Term.binary .add (operand (0 : Fin 1) 1 (.header 2)) (operand (0 : Fin 1) 1 .row)
  [basis true 21,basis false 23,port,pair,sourceAddress.load,sourceAddress]

private theorem aux_binary_binds {W K n : ℕ} (op : BinaryOp) (a b : Term W K n) :
    (Term.binary op a b).binds = a.binds + b.binds + 1 := by
  simp [Term.binary, Term.binds, Nat.add_assoc]

private theorem aux_load_binds {W K n : ℕ} (a : Term W K n) :
    a.load.binds = a.binds + 1 := by
  simp [Term.load, Term.binds]

private theorem aux_select_binds {W K n : ℕ} (cmp : DescriptorExpr.Comparison) (a b x y : Term W K n) :
    (Term.select cmp a b x y).binds = a.binds + b.binds + x.binds + y.binds + 1 := by
  simp [Term.select, Term.binds, Nat.add_assoc]

private theorem aux_operand_size (W stride : ℕ) (op : Operand) :
    (operand (w:=W) (0 : Fin 1) stride op).binds =
      (operand (w:=1) (0 : Fin 1) stride op).binds := by
  cases op <;> simp only [operand, field, aux_binary_binds, aux_load_binds,
    Term.parameter, Term.literal, Term.binds]

private theorem aux_mounted_size {W a : ℕ} (lhs : Term W 1 a) (rhs : Term 1 1 a)
    (same : lhs.binds = rhs.binds) (stride : ℕ) (ops : Fin a → Operand) :
    (program lhs 0 stride ops).binds = (program rhs 0 stride ops).binds := by
  simp only [program, Term.binds_instantiate]
  exact congrArg₂ Nat.add same (Finset.sum_congr rfl (fun j _ => aux_operand_size W stride (ops j)))

private theorem aux_batch_size (W : ℕ) (commandBank : Bool) :
    (HistoryBatchTape.program W commandBank).binds = (HistoryBatchTape.program 1 commandBank).binds := by
  simp only [HistoryBatchTape.program, PhysicalPinsExpr.Formula.binds_compile]

private theorem aux_pair_size (W : ℕ) :
    (HistoryPairSeeds.program W 0).binds = (HistoryPairSeeds.program 1 0).binds := by
  simp only [HistoryPairSeeds.program, PhysicalPinsExpr.Formula.binds_compile]

private theorem aux_port_size (W : ℕ) :
    (HistoryPortMap.word W 1).binds = (HistoryPortMap.word 1 1).binds := by
  simp only [HistoryPortMap.word, aux_select_binds, aux_binary_binds, Term.binds]

private theorem aux_six_sum (W : ℕ) (a b c d e f : (U : ℕ) → Term U 1 1)
    (ha : (a W).binds = (a 1).binds) (hb : (b W).binds = (b 1).binds)
    (hc : (c W).binds = (c 1).binds) (hd : (d W).binds = (d 1).binds)
    (he : (e W).binds = (e 1).binds) (hf : (f W).binds = (f 1).binds) :
    ([a W,b W,c W,d W,e W,f W].map Term.binds).sum =
      ([a 1,b 1,c 1,d 1,e 1,f 1].map Term.binds).sum := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ha,hb,hc,hd,he,hf]

theorem aux_size (W : ℕ) :
    ((auxiliary W).map Term.binds).sum=((auxiliary 1).map Term.binds).sum := by
  let tapeOps : Fin 3 → Operand := ![.header 2,.row,.column]
  let portOps : Fin 4 → Operand := ![.row,.header 2,.header 3,.header 4]
  let pairOps : Fin 3 → Operand := ![.row,.header 2,.header 3]
  let basis (ty : Bool) (stride U : ℕ) : Term U 1 1 :=
    program (HistoryBatchTape.program U ty) 0 stride tapeOps
  let port (U : ℕ) := program (HistoryPortMap.word U 1) 0 1 portOps
  let pair (U : ℕ) := program (HistoryPairSeeds.program U 0) 0 1 pairOps
  let addr (U : ℕ) : Term U 1 1 :=
    Term.binary .add (operand 0 1 (.header 2)) (operand 0 1 .row)
  have haddr : (addr W).binds = (addr 1).binds := by
    simp only [addr, aux_binary_binds, aux_operand_size W]
  have hload : (addr W).load.binds = (addr 1).load.binds := by simp only [aux_load_binds, haddr]
  exact aux_six_sum W (basis true 21) (basis false 23) port pair (fun U => (addr U).load) addr
    (aux_mounted_size (HistoryBatchTape.program W true) (HistoryBatchTape.program 1 true)
      (aux_batch_size W true) 21 tapeOps)
    (aux_mounted_size (HistoryBatchTape.program W false) (HistoryBatchTape.program 1 false)
      (aux_batch_size W false) 23 tapeOps)
    (aux_mounted_size (HistoryPortMap.word W 1) (HistoryPortMap.word 1 1) (aux_port_size W) 1 portOps)
    (aux_mounted_size (HistoryPairSeeds.program W 0) (HistoryPairSeeds.program 1 0) (aux_pair_size W) 1 pairOps)
    hload haddr


end
end ThreeFlat.RAM.HistorySelectedOps

end OAI
