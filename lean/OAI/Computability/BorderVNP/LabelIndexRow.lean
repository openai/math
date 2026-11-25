import OAI.Computability.BorderVNP.LabelIndex

/-! # Physical word calculations for each row of the sparse chooser directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open RoutingISA VPVNP.BurstRAM

/-- All addresses and cumulative values actually used by a row fit the physical word. -/
def Phase.room (p : Phase) (l : Layout) (w i : ℕ) (a : Acc) : Prop :=
  let B := 2^w
  match p with
  | .clear => l.heads+i < B ∧ l.data+i < B
  | .cable =>
    let b := l.cables+i*3
    b+2 < B ∧ l.heads+a.mem b < B ∧ l.heads+a.mem (b+1) < B ∧
      l.nodes+(i*2+1)*4+3 < B ∧ i*2+2 < B ∧ a.cableTotal+a.mem (b+2) < B
  | .delivery =>
    let b := l.deliveries+i*7
    let dest := l.data+a.mem (b+4)
    b+6 < B ∧ dest < B ∧ a.mem dest+a.mem (b+6) < B ∧ a.dataTotal+a.mem (b+6) < B
  | .cableBins => l.cableMean+i < B
  | .dataBins => l.dataMean+i < B ∧ a.dataTotal*l.labels < B

set_option maxHeartbeats 4000000 in
/-- The native row preserves the cursor and configuration, and implements the
linked insertion, width aggregation or bin write exactly. -/
theorem Phase.row_eval (p : Phase) (l : Layout) (a : Acc) (z : NatState) (pub : Arg → ℕ)
    (i : ℕ) (h : Ready l a z) (hc : z.reg 20 = i) :
    let t := p.row.fixedEval pub z
    Ready l (p.step l i a) t ∧ t.reg 20 = i := by
  obtain ⟨params,ct,dt,mem⟩ := h
  constructor
  · constructor
    · intro j hj
      exact (Code.fixedEval_protected _ _ _ (lo := 18) (by cases p <;> decide) _ hj).trans (params j hj)
    · cases p <;>
        simp (config := { decide := true }) [Phase.step, Phase.row, insertNode, push, Code.block,
          Code.fixedEval,Code.evalNat,addressOp,params,Layout.param,ct,dt,mem,hc,Nat.add_assoc]; split <;> simp_all
  · cases p <;> simp (config := { decide := true }) [Phase.row, insertNode, Code.block,Code.fixedEval,Code.evalNat,hc]; split <;> simp_all

set_option maxHeartbeats 4000000 in
/-- The natural address and volume bounds imply every primitive operation of the row
is valid on the actual finite word bank. -/
theorem Phase.row_safe (p : Phase) (l : Layout) (w i : ℕ) (a : Acc) (z : NatState)
    (pub : Arg → ℕ) (h : Ready l a z) (hc : z.reg 20 = i) (bounds : p.room l w i a) :
    p.row.fixedSafe w pub z := by
  obtain ⟨params,ct,dt,mem⟩ := h
  cases p <;>
    simp (config := { decide := true }) [Phase.row,insertNode,Code.block, Code.fixedSafe,
      Code.fixedEval, Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,
      params,Layout.param,ct,dt,mem,hc,Nat.add_assoc] <;>
    simp [Phase.room,Nat.add_assoc] at bounds <;> omega

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
