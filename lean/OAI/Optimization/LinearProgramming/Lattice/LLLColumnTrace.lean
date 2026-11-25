import OAI.Optimization.LinearProgramming.Lattice.LLLRationalTrace

/-! Inspecting each native size-reduction column in chronological order. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal

/-- Visit columns `t-1,…,0` of the current row `k`. Each list entry contains the
column number and the state immediately before its native update. -/
def columnTraceFrom {n m : ℕ} (k : Fin n) : (t : ℕ) → t ≤ k.val → LLLState n m →
    LLLState n m × List (Fin n × LLLState n m)
  | 0, _, s => (s, [])
  | t+1, ht, s =>
    let j : Fin n := ⟨t, Nat.lt_of_lt_of_le (Nat.lt_succ_self t) (ht.trans k.isLt.le)⟩
    let next := s.sizeReduceColumn j k (Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht)
    let rest := columnTraceFrom k t (Nat.le_of_succ_le ht) next
    (rest.1, (j,s) :: rest.2)

private theorem columnTraceFrom_foldr {n m : ℕ} (k : Fin n) (t : ℕ) (ht : t ≤ k.val)
    (s : LLLState n m) : (columnTraceFrom k t ht s).1 =
    Fin.foldr t (fun j state => (state : LLLState n m).sizeReduceColumn
      ⟨j.val, lt_of_lt_of_le j.isLt (ht.trans k.isLt.le)⟩ k (lt_of_lt_of_le j.isLt ht)) s := by
  induction t generalizing s with
  | zero => simp [columnTraceFrom]
  | succ t ih =>
    rw [columnTraceFrom, Fin.foldr_succ_last]
    exact ih _ _

/-- Complete inner trace and the resulting state for one native size-reduction pass. -/
def sizeReduceColumnTrace {n m : ℕ} (s : LLLState n m) (k : Fin n) :=
  columnTraceFrom k k.val le_rfl s

theorem sizeReduceColumnTrace_result {n m : ℕ} (s : LLLState n m) (k : Fin n) :
    (sizeReduceColumnTrace s k).1 = s.sizeReduce k.val := by
  rw [sizeReduceColumnTrace, columnTraceFrom_foldr]
  simp only [LLLState.sizeReduce, k.isLt, ↓reduceDIte]

theorem columnTraceFrom_indices {n m : ℕ} (k : Fin n) (t : ℕ) (ht : t ≤ k.val)
    (s : LLLState n m) :
    (columnTraceFrom k t ht s).2.map (fun v => v.1.val) = (List.range t).reverse := by
  induction t generalizing s with
  | zero => simp [columnTraceFrom]
  | succ t ih => simp [columnTraceFrom, ih, List.range_succ]

theorem sizeReduceColumnTrace_length {n m : ℕ} (s : LLLState n m) (k : Fin n) :
    (sizeReduceColumnTrace s k).2.length = k.val := by
  simpa only [sizeReduceColumnTrace, List.length_map, List.length_reverse, List.length_range] using
    congrArg List.length (columnTraceFrom_indices k k.val le_rfl s)

/-- Induct over every state of an actual native pass. A visit to column `j` occurs after
exactly `t-1-j` updates, and the returned state occurs after all `t`. -/
theorem columnTraceFrom_invariant {n m : ℕ} (k : Fin n) (P : ℕ → LLLState n m → Prop)
    (hstep : ∀ z (s : LLLState n m) (j : Fin n) (hj : j < k), P z s →
      P (z+1) (s.sizeReduceColumn j k hj)) (t : ℕ) (ht : t ≤ k.val)
    (s : LLLState n m) (start : ℕ) (hs : P start s) :
    P (start+t) (columnTraceFrom k t ht s).1 ∧
    ∀ v ∈ (columnTraceFrom k t ht s).2, v.1.val < t ∧ P (start+(t-1-v.1.val)) v.2 := by
  induction t generalizing s start with
  | zero => simp [columnTraceFrom, hs]
  | succ t ih =>
    let j : Fin n := ⟨t, by omega⟩
    have hj : j < k := by change t < k.val; omega
    let next := s.sizeReduceColumn j k hj
    obtain ⟨hfinal, hall⟩ := ih (Nat.le_of_succ_le ht) next (start+1) (hstep start s j hj hs)
    constructor
    · change P (start+(t+1)) (columnTraceFrom k t _ next).1
      convert hfinal using 1; omega
    · intro v hv
      change v ∈ (j,s) :: (columnTraceFrom k t _ next).2 at hv
      rcases List.mem_cons.mp hv with he | he
      · subst v
        exact ⟨Nat.lt_succ_self t, by simpa [j] using hs⟩
      · obtain ⟨hlt, hp⟩ := hall v he
        exact ⟨by omega, (show start+(t+1-1-v.1.val) = start+1+(t-1-v.1.val) by omega) ▸ hp⟩

/-- Arithmetic coordinate replacements triggered by a column: `m` basis coordinates,
`j` earlier stored coefficients, and the pivot coefficient. A skipped column has zero. -/
def columnReplacements {n m : ℕ} (k : Fin n) (v : Fin n × LLLState n m) : ℕ :=
  if 2 * Int.natAbs ((v.2.ν.getRow k).get v.1) >
       v.2.d.get ⟨v.1.val+1, Nat.succ_lt_succ v.1.isLt⟩ then m+v.1.val+1 else 0

private theorem replacement_sum_le {n m : ℕ} (k : Fin n) (visits : List (Fin n × LLLState n m)) :
    (visits.map (columnReplacements k)).sum ≤ (m+n)*visits.length := by
  induction visits with
  | nil => simp
  | cons v vs ih =>
    have h : columnReplacements k v ≤ m+n := by
      unfold columnReplacements
      split <;> have hj := v.1.isLt <;> omega
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

/-- At most `k(m+n)` arithmetic coordinate replacements in a complete pass at row `k`. -/
theorem sizeReduceColumnTrace_replacements_le {n m : ℕ} (s : LLLState n m) (k : Fin n) :
    ((sizeReduceColumnTrace s k).2.map (columnReplacements k)).sum ≤ (m+n)*k.val := by
  simpa only [sizeReduceColumnTrace_length] using replacement_sum_le k (sizeReduceColumnTrace s k).2

end Lattice
end LinearProgramming
end Optimization
end OAI
