import OAI.Optimization.LinearProgramming.Recovery.MaskedProgramCode
import OAI.Optimization.LinearProgramming.Recovery.MaskedLayout

/-! Fixed preprocessing of the normal, reentrant support query. The protected
caller supplies only the immutable opposite basis and the current scalar flags. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace MaskedInput
open RAM Geometry

variable {h n : ℕ}

theorem program_run (E : Matrix (Fin h) (Fin n) ℚ) (S : Finset (Fin n)) (P : ℚ→Prop) (zero : P 0) (one : P 1)
    (input : ∀ j:ℕ,P (((bundle E S)[j]?).getD 0)) :
    ∃ t k,k ≤ programTime h n ∧ Block.Eval (Memory.AllData P) program (start [h,n] (bundle E S)).memory k t ∧
      PairBuilder.InputRegs (pairLayout h n) t ∧ uniformRect (h+n) n (base h n) t=maskedEquations E S := by
  obtain ⟨v,c,clock,prepared,header,top,flags⟩:=snapshot_run E S P input
  obtain ⟨t,k,hk,cell,table,_,index⟩:=MaskedTable.program_spec E S P zero one v prepared.safe_end header.zero
    header.rows header.cols header.diagonal header.flags flags (by unfold base;omega) (by unfold flagBase bottom base;omega) (Or.inr le_rfl) top
  refine ⟨t,c+k,Nat.add_le_add clock hk,prepared.seq cell,?_,table⟩
  exact ⟨(index 200 (Or.inr (by decide))).trans header.count,(index 201 (Or.inr (by decide))).trans header.width,
    (index 202 (Or.inr (by decide))).trans header.matrix,(index 203 (Or.inr (by decide))).trans header.output,
    (index 204 (Or.inr (by decide))).trans header.scratch,(index 205 (Or.inr (by decide))).trans header.dirty⟩

theorem bundle_height (E : Matrix (Fin h) (Fin n) ℚ) (S : Finset (Fin n)) (H : ℕ) (small : 3 ≤ H)
    (rows : ∀i j,ratBits (E i j) ≤ H) : ∀a : ℕ,ratBits (((bundle E S)[a]?).getD 0) ≤ H := by
  intro a
  cases eq : (bundle E S)[a]? with
  | none => exact small
  | some z =>
    have mem:=List.mem_of_getElem? eq
    change z∈encodedGramInput E++List.ofFn (fun j : Fin n => if j∈S then (1:ℚ) else 0) at mem
    rcases List.mem_append.mp mem with before|after
    · obtain ⟨ij,rfl⟩:=List.mem_ofFn.mp before
      exact rows _ _
    · obtain ⟨i,rfl⟩:=List.mem_ofFn.mp after
      split <;> exact small

end MaskedInput
end Recovery
end LinearProgramming
end Optimization
end OAI
