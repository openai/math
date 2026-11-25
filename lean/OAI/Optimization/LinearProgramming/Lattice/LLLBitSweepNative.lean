import OAI.Optimization.LinearProgramming.Lattice.LLLBitSweep
import OAI.Optimization.LinearProgramming.Lattice.BitColumnNative
import OAI.Optimization.LinearProgramming.Lattice.LLLColumnTrace

/-! Every sweep-cursor state is a column visit of the actual native computation or its
terminal state. Thus size estimates on those visits justify the checked tape guard. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec.Fuel
open Hex.Internal

variable {n m : ℕ}

/-- The column program instantiated at the actual row-major signed matrix encoding. -/
def packedSweep (x : ℕ × Cursor) := runSweep stateCode sizeReduceColumn
  (fun c => (cursorCode c).length) x

noncomputable def packedSweepP : Procedure (prodCode unaryCode cursorCode) stateCode packedSweep :=
  runSweepP (lengthInUnary cursorCode) sizeReduceColumnP

private theorem foldColumns_pack (hcol : ∀ (s : LLLState n m) (j k : Fin n) (h : j < k),
    sizeReduceColumn j.val k.val (packState s) = packState (s.sizeReduceColumn j k h))
    (k : Fin n) (j : ℕ) (hj : j ≤ k.val) (s : LLLState n m) :
    foldColumns sizeReduceColumn k.val j (packState s) = packState (columnTraceFrom k j hj s).1 := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    let l : Fin n := ⟨j,by omega⟩
    have hl : l < k := by change j < k.val; omega
    change foldColumns _ _ j (sizeReduceColumn l.val k.val (packState s)) =
      packState (columnTraceFrom k j (by omega) (s.sizeReduceColumn l k hl)).1
    rw [hcol s l k hl]
    exact ih (by omega) _

/-- A nonterminal sweep frame is precisely a native visit, including its column cursor. -/
theorem sweep_iterate_visit (hcol : ∀ (s : LLLState n m) (j k : Fin n) (h : j < k),
    sizeReduceColumn j.val k.val (packState s) = packState (s.sizeReduceColumn j k h))
    (k : Fin n) (j : ℕ) (hj : j ≤ k.val) (s : LLLState n m) (i : ℕ) :
    let result := (sweepStep sizeReduceColumn)^[i] (j,k.val,packState s)
    (∃ v ∈ (columnTraceFrom k j hj s).2, result = (v.1.val+1,k.val,packState v.2)) ∨
      result = (0,k.val,packState (columnTraceFrom k j hj s).1) := by
  dsimp only
  induction j generalizing s i with
  | zero =>
    right
    exact Function.iterate_fixed (show sweepStep sizeReduceColumn (0,k.val,packState s) = _ by rfl) i
  | succ j ih =>
    let l : Fin n := ⟨j,by omega⟩
    have hl : l < k := by change j < k.val; omega
    let r := s.sizeReduceColumn l k hl
    cases i with
    | zero =>
      exact Or.inl ⟨(l,s), List.mem_cons_self, rfl⟩
    | succ i =>
      rw [Function.iterate_succ_apply]
      have hstep : sweepStep sizeReduceColumn (j+1,k.val,packState s) = (j,k.val,packState r) := by
        change (if j+1=0 then _ else (j+1-1,k.val,sizeReduceColumn (j+1-1) k.val _)) = _
        simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_one_sub_one]
        exact congrArg (fun a => (j,k.val,a)) (hcol s l k hl)
      rw [hstep]
      rcases ih (by omega) r i with ⟨v,hv,he⟩ | he
      · exact Or.inl ⟨v, List.mem_cons_of_mem _ hv, he⟩
      · exact Or.inr he

/-- Correctness for this exact state encoding only needs the reachable native visit
widths, including the last state; every comparison and column update is executable. -/
theorem packedSweep_eq_native (hcol : ∀ (s : LLLState n m) (j k : Fin n) (h : j < k),
    sizeReduceColumn j.val k.val (packState s) = packState (s.sizeReduceColumn j k h))
    (s : LLLState n m) (k : Fin n) (cap : ℕ) (ht : k.val ≤ (cursorCode (k.val,packState s)).length)
    (hvisit : ∀ v ∈ (sizeReduceColumnTrace s k).2,
      (sweepCode stateCode (v.1.val+1,k.val,packState v.2)).length ≤ cap)
    (hfinal : (sweepCode stateCode (0,k.val,packState (s.sizeReduce k.val))).length ≤ cap) :
    packedSweep (cap,k.val,packState s) = packState (s.sizeReduce k.val) := by
  unfold packedSweep
  rw [runSweep_exact _ _ _ _ _ _ ht]
  · exact (foldColumns_pack hcol k k.val le_rfl s).trans (congrArg packState (sizeReduceColumnTrace_result s k))
  · intro i _ _
    rcases sweep_iterate_visit hcol k k.val le_rfl s i with ⟨v,hv,he⟩ | he
    · rw [he]
      exact hvisit v hv
    · rw [he]
      change (sweepCode stateCode (0,k.val,packState (sizeReduceColumnTrace s k).1)).length ≤ _
      rw [sizeReduceColumnTrace_result]
      exact hfinal

/-- Unconditional column correspondence for the actual deployed signed integer program. -/
theorem packedSweep_correct (s : LLLState n m) (k : Fin n) (cap : ℕ)
    (ht : k.val ≤ (cursorCode (k.val,packState s)).length)
    (hvisit : ∀ v ∈ (sizeReduceColumnTrace s k).2,
      (sweepCode stateCode (v.1.val+1,k.val,packState v.2)).length ≤ cap)
    (hfinal : (sweepCode stateCode (0,k.val,packState (s.sizeReduce k.val))).length ≤ cap) :
    packedSweep (cap,k.val,packState s) = packState (s.sizeReduce k.val) :=
  packedSweep_eq_native sizeReduceColumn_packState s k cap ht hvisit hfinal

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
