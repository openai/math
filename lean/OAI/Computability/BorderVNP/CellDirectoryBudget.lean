import OAI.Computability.BorderVNP.CellDirectoryCompact
import OAI.Computability.BorderVNP.CellGadgetBudget
import OAI.Computability.BorderVNP.CellRecordGuardsBudget

/-! # Execution budget of the complete signed cell validator

Source-level bounds on the actual directory fields imply bounds on all addresses
reached by private copies. The resulting degree-ten clock accounts for wire
guesses, every local scratch rectangle, all checks and the signed factor sweep.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro

/-- Compact directory fields bound all addresses of all expanded factor occurrences,
including copies of a repeated box and outer reported-use wires. -/
theorem Directory.CompactFields.boxBounds {D : Directory} {p M : ℕ} (h : D.CompactFields p M) :
    D.BoxBounds M (4*(M+1)^3) := by
  intro o ho
  rw [← D.blocks_visits] at ho
  obtain ⟨b,hb,ho⟩ := List.mem_flatMap.mp ho
  obtain ⟨i,hi,ho'⟩ := List.mem_flatMap.mp ho
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp ho'
  obtain ⟨hbase,hstride,hcopies,_⟩ := (h.boxes b hb).1
  have hiM := (List.mem_range.mp hi).le.trans hcopies
  obtain ⟨ht,hf'⟩ := (h.boxes b hb).2 f hf
  refine ⟨ht,?_⟩
  have addr (x : ℕ) (hx : x ≤ M) : b.base + i*b.stride + x ≤ 4*(M+1)^3 := by
    calc
      _ ≤ M + M*M + M := by gcongr
      _ ≤ _ := by nlinarith only [Nat.zero_le M,Nat.zero_le (M^2),Nat.zero_le (M^3)]
  cases f with
  | truth ws rs | sign ws rs | gadget ws rs => exact fun w hw => addr w (hf' w hw)
  | unary w port =>
    obtain ⟨hw,hpb,hpc,_⟩ := hf'
    refine ⟨addr w hw,?_⟩
    calc
      _ = port.base + i*port.copyStride := by simp [Port.atBit]
      _ ≤ M + M*M := by gcongr
      _ ≤ _ := by nlinarith only [Nat.zero_le M,Nat.zero_le (M^2),Nat.zero_le (M^3)]

/-- Complete private binary instruction-stream length for the actual generated
program, in terms of the compact field, descriptor-count and subtotal-count bounds. -/
theorem Directory.program_work_polynomial (D : Directory) (p : ℕ) (env : List ℕ) (M : ℕ)
    (h : D.CompactFields p M) (hr : D.records.length ≤ M) (hg : D.reportedCounts.length ≤ M) :
    work (D.program p) env ≤ 30000*(M+2)^10 := by
  let A := 4*(M+1)^3
  have hM : M ≤ A := by dsimp [A]; nlinarith only [Nat.zero_le M,Nat.zero_le (M^2),Nat.zero_le (M^3)]
  have hguess : work (.loop (.lit p) (.fixed .guess)) env = 2*p := by
    simp [work_loop,NatExpr.eval,Op.bits,List.map_const',Nat.mul_comm]
  have hw := D.recordGuards_work_le env M h.records
  have hb := h.boxBounds
  have hf := factorSweep_work_le D 0 env hb
  have hrg := D.rangeGuard_work_le env hb
  have hs := D.subtotalGuards_work_polynomial env hb h.visits hg le_rfl (fun bits hbits =>
    ⟨(h.reports bits hbits).1, fun b hbit => ((h.reports bits hbits).2 b hbit).trans hM⟩)
  simp only [Directory.program,Directory.checkAssignment,Directory.countGuards,work_seq,hguess]
  calc
    _ ≤ 2*M + (M*(16000*(M+2)^9) +
          (M*(2*guardCost A (factorNodeBound M)) + (M*guardCost A (factorNodeBound M) + 5000*(M+2)^8))) := by
      apply Nat.add_le_add (Nat.mul_le_mul_left _ h.privateWires)
      apply Nat.add_le_add (hw.trans (Nat.mul_le_mul_right _ hr))
      apply Nat.add_le_add (by simpa [A] using hf.trans (Nat.mul_le_mul_right _ h.visits))
      exact Nat.add_le_add (hrg.trans (Nat.mul_le_mul_right _ h.visits)) hs
    _ ≤ _ := by
      dsimp [guardCost,factorNodeBound,A]
      nlinarith only [Nat.zero_le M,Nat.zero_le (M^2),Nat.zero_le (M^3),Nat.zero_le (M^4),Nat.zero_le (M^5),
        Nat.zero_le (M^6),Nat.zero_le (M^7),Nat.zero_le (M^8),Nat.zero_le (M^9),Nat.zero_le (M^10)]

/-- Every execution branch of the decoded private cell program has this polynomial
clock, including the unary read offsets and terminal fetch. -/
theorem Directory.program_budget_polynomial (D : Directory) (p : ℕ) (env : List ℕ) (M : ℕ)
    (h : D.CompactFields p M) (hr : D.records.length ≤ M) (hg : D.reportedCounts.length ≤ M) :
    budget ((D.program p).expand env) ≤ 150000*(M+2)^10 + 2 := by
  apply (budget_le _).trans
  change 5 * work (D.program p) env + 2 ≤ _
  rw [show 150000 = 5*30000 by decide, Nat.mul_assoc]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (D.program_work_polynomial p env M h hr hg)) _

end CellSparse

end BorderVNP
end Computability
end OAI
