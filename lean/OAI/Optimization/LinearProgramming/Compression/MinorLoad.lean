import OAI.Optimization.LinearProgramming.Compression.MinorLoadCell
import OAI.Optimization.LinearProgramming.RAM.MinorLoadLoops
import OAI.Optimization.LinearProgramming.Compression.MinorLoadInput
import OAI.Optimization.LinearProgramming.Compression.RationalMinorSize

/-! A fixed program for loading any square minor from a dense rational or ordered-field
matrix. The address bank supplies the selected input matrix and the two index arrays. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorLoad

open RAM

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def prepareRow : Block := .seq (.op (.addrLoad 10 8))
  (.seq (.op (.addrConst 7 0)) (.op (.addrCopy 9 4)))

def finishRow : Block := .seq (.op (.incr 8 8)) (.op (.incr 6 6))

def rowBody : Block := .seq prepareRow (.seq (.loop (.addrLT 7 2) cellBody) finishRow)

def rowCost (v : Layout K) (i : Fin v.k) : ℕ := (∑ j, (cellCost v i j + 2)) + 6

private theorem prepare_eval {P : K → Prop} {v : Layout K} {src s : Memory K} (hin : Input v src)
    (i : Fin v.k) (h : Outer P v src i.val s) :
    ∃ t, Block.Eval (Good P) prepareRow s 3 t ∧ Inner P v src i 0 t := by
  have inp := hin.of_frame h.frame
  let a := s.putIndex 10 (s.index (s.index 8))
  let b := a.putIndex 7 0
  let t := b.putIndex 9 (b.index 4)
  refine ⟨t, (Block.Eval.op_addrLoad s 10 8 h.safe h.safe).seq
    ((Block.Eval.op_addrConst a 7 0 h.safe h.safe).seq (Block.Eval.op_addrCopy b 9 4 h.safe h.safe)),
    ⟨((h.frame.putIndex (by decide) (by decide) _).putIndex (by decide) (by decide) _).putIndex
      (by decide) (by decide) _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.safe⟩⟩
  · exact h.copied
  all_goals simp [t,b,a,Memory.putIndex,h.cnt,h.ptr,h.dst,inp.rows,inp.colBase]

private theorem finish_eval {P : K → Prop} {v : Layout K} {src s : Memory K}
    (i : Fin v.k) (h : Inner P v src i v.k s) :
    ∃ t, Block.Eval (Good P) finishRow s 2 t ∧ Outer P v src (i.val+1) t := by
  let a := s.putIndex 8 (s.index 8 + 1)
  let t := a.putIndex 6 (a.index 6 + 1)
  refine ⟨t, (Block.Eval.op_incr s 8 8 h.safe h.safe).seq (Block.Eval.op_incr a 6 6 h.safe h.safe),
    ⟨(h.frame.putIndex (by decide) (by decide) _).putIndex (by decide) (by decide) _, ?_, ?_, ?_, ?_, h.safe⟩⟩
  · change Copied v s ((i.val+1)*v.k)
    rw [Nat.succ_mul]; exact h.copied
  all_goals simp [t,a,Memory.putIndex,h.rcnt,h.rptr,h.dst,Nat.succ_mul,Nat.add_assoc]

theorem row_eval {P : K → Prop} {v : Layout K} {src s : Memory K} (hi : Input v src)
    (i : Fin v.k) (h : Outer P v src i.val s) :
    ∃ t, Block.Eval (Good P) rowBody s (rowCost v i) t ∧ Outer P v src (i.val+1) t := by
  obtain ⟨a, ha, hstart⟩ := prepare_eval hi i h
  obtain ⟨b, hb, hafter⟩ := Block.Eval.loop_varying_exact (safe := Good P) (c := .addrLT 7 2)
    (body := cellBody) v.k (cellCost v i) (Inner P v src i) a hstart
    (fun j u hu => ⟨by simp [Cond.test, hu.ccnt, (hi.of_frame hu.frame).order],
      cell_eval hi i j hu⟩)
    (fun u hu => ⟨by simp [Cond.test, hu.ccnt, (hi.of_frame hu.frame).order], hu.safe⟩)
  obtain ⟨t, ht, hout⟩ := finish_eval i hafter
  refine ⟨t, ?_, hout⟩
  unfold rowBody rowCost
  convert ha.seq (hb.seq ht) using 1; omega

def initBlock : Block :=
  .seq (.op (.addrConst 6 0)) (.seq (.op (.addrCopy 8 3)) (.op (.addrCopy 15 5)))

/-- All bounds and addresses are read from the memory; this instruction block is independent
of matrix dimensions and all matrix entries. -/
def loader : Block := .seq initBlock (.loop (.addrLT 6 2) rowBody)

def loaderCost (v : Layout K) : ℕ := (∑ i, (rowCost v i+2))+4

def program : Program := loader.compile 0 ++ [.halt 0]

private theorem init_eval {P : K → Prop} {v : Layout K} (m : Memory K) (hi : Input v m)
    (hs : Good P m) : ∃ s, Block.Eval (Good P) initBlock m 3 s ∧ Outer P v m 0 s := by
  let a := m.putIndex 6 0
  let b := a.putIndex 8 (a.index 3)
  let s := b.putIndex 15 (b.index 5)
  refine ⟨s, (Block.Eval.op_addrConst m 6 0 hs hs).seq
    ((Block.Eval.op_addrCopy a 8 3 hs hs).seq (Block.Eval.op_addrCopy b 15 5 hs hs)),
    ⟨(((Frame.refl m).putIndex (by decide) (by decide) _).putIndex (by decide) (by decide) _).putIndex
      (by decide) (by decide) _, ?_, ?_, ?_, ?_, hs⟩⟩
  · simpa using (Copied.zero (v := v) s)
  all_goals simp [s,b,a,Memory.putIndex,hi.rowBase,hi.out]

/-- Exact time, output layout and preserved registers for the fixed minor-loading program. -/
theorem loader_eval {P : K → Prop} {v : Layout K} (m : Memory K) (hi : Input v m) (hs : Good P m) :
    ∃ t, Block.Eval (Good P) loader m (loaderCost v) t ∧ Frame v m t ∧
      ∀ i j, t.data (v.dst+(i.val*v.k+j.val)) = v.matrix (v.row i) (v.col j) := by
  obtain ⟨s, hinit, h0⟩ := init_eval m hi hs
  obtain ⟨t, hloop, ht⟩ := Block.Eval.loop_varying_exact (safe := Good P) (c := .addrLT 6 2)
    (body := rowBody) v.k (rowCost v) (Outer P v m) s h0
    (fun i u hu => ⟨by simp [Cond.test, hu.cnt, (hi.of_frame hu.frame).order],
      row_eval hi i hu⟩)
    (fun u hu => ⟨by simp [Cond.test, hu.cnt, (hi.of_frame hu.frame).order], hu.safe⟩)
  refine ⟨t, ?_, ht.frame, fun i j => ht.copied i j (flat_lt i.isLt j.isLt)⟩
  unfold loader loaderCost
  convert hinit.seq hloop using 1; omega

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem loaderCost_le (v : Layout K) : loaderCost v ≤ v.k*(v.k*(v.m*(4*v.n+5)+4*v.n+13)+8)+4 := by
  have hc (i j : Fin v.k) : cellCost v i j + 2 ≤ v.m*(4*v.n+5)+4*v.n+13 := by
    unfold cellCost
    have hr := Nat.mul_le_mul_right (4*v.n+5) (v.row i).isLt.le
    have hl := Nat.mul_le_mul_left 4 (v.col j).isLt.le
    omega
  have hr (i : Fin v.k) : rowCost v i + 2 ≤ v.k*(v.m*(4*v.n+5)+4*v.n+13)+8 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) fun j _ => hc i j
    simpa [rowCost, Nat.add_assoc] using Nat.add_le_add_right hh 8
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ => hr i
  simpa [loaderCost] using Nat.add_le_add_right hh 4

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
/-- The scalar RAM bound for loading a minor is uniform in its dimensions and includes halt. -/
theorem loaderCost_polynomial (v : Layout K) {N : ℕ} (hm : v.m ≤ N) (hn : v.n ≤ N) (hk : v.k ≤ N) :
    loaderCost v + 1 ≤ polyBound 50 4 N := calc
  _ ≤ v.k*(v.k*(v.m*(4*v.n+5)+4*v.n+13)+8)+4+1 := Nat.add_le_add_right (loaderCost_le v) 1
  _ ≤ N*(N*(N*(4*N+5)+4*N+13)+8)+4+1 := by gcongr
  _ ≤ 50*(N+1)^4 := by ring_nf; omega

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem pairLoaderCost_polynomial {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) K)
    (E : Matrix (Fin rE) (Fin n) K) (u : PairMinorIndex rD rE n) (hrows : rD+rE=n) :
    loaderCost (pairLayout D E u) + 1 ≤ polyBound 50 4 n := by
  rcases u with ⟨k,r,c⟩ | ⟨k,r,c⟩
  · exact loaderCost_polynomial _ (show rD ≤ n by omega) le_rfl (show k.val ≤ n by omega)
  · exact loaderCost_polynomial _ (show rE ≤ n by omega) le_rfl (show k.val ≤ n by omega)

/-- Exact execution under `RAM.step`. Each copied scalar is an original value, so any
initial bound on scalar encoding size continues to hold through every step. -/
theorem program_trace {P : K → Prop} {v : Layout K} (m : Memory K) (hi : Input v m) (hs : Good P m) :
    ∃ tr : Fin (loaderCost v + 1 + 1) → State K, Trace program (m.atPC 0) (loaderCost v + 1) tr ∧
      (tr (Fin.last _)).output = some 0 ∧ Frame v m (tr (Fin.last _)).memory ∧
      (∀ i j, (tr (Fin.last _)).data (v.dst+(i.val*v.k+j.val)) = v.matrix (v.row i) (v.col j)) ∧
      ∀ i a, P ((tr i).data a) := by
  obtain ⟨u, hu, hf, hread⟩ := loader_eval m hi hs
  obtain ⟨tr, ht, htag, hend, hall⟩ := hu.halted_trace (tag := 0)
  refine ⟨tr, ht, htag, hend ▸ hf, ?_, hall⟩
  intro i j
  change (tr (Fin.last _)).memory.data _ = _
  rw [hend]; exact hread i j

/-- The loaded scalar registers form precisely the square matrix requested by `u`, so
applying the determinant algorithm to this contiguous table gives `pairMinorValue D E u`. -/
theorem pairProgram_trace {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) K)
    (E : Matrix (Fin rE) (Fin n) K) (u : PairMinorIndex rD rE n) {P : K → Prop}
    (hz : P 0) (hD : ∀ i j, P (D i j)) (hE : ∀ i j, P (E i j)) :
    let v := pairLayout D E u
    ∃ tr : Fin (loaderCost v + 1 + 1) → State K,
      Trace program ((pairMemory D E u).atPC 0) (loaderCost v + 1) tr ∧
      (tr (Fin.last _)).output = some 0 ∧
      (Matrix.of (fun i j : Fin v.k => (tr (Fin.last _)).data (v.dst+(i.val*v.k+j.val)))).det =
        pairMinorValue D E u ∧ (∀ i j, (tr (Fin.last _)).data (v.dst+(i.val*v.k+j.val)) =
          v.matrix (v.row i) (v.col j)) ∧ ∀ i a, P ((tr i).data a) := by
  let v := pairLayout D E u
  obtain ⟨tr, ht, htag, _, hv, hs⟩ := program_trace (pairMemory D E u) (pairMemory_input D E u)
    (pairMemory_safe D E u hz hD hE)
  refine ⟨tr, ht, htag, ?_, hv, hs⟩
  have he : Matrix.of (fun i j : Fin v.k => (tr (Fin.last _)).data (v.dst+(i.val*v.k+j.val))) =
      v.matrix.submatrix v.row v.col := Matrix.ext hv
  rw [he]
  cases u <;> rfl

/-- The online request may select either matrix; one bound in the combined input length
works for the reduced determinant in both branches. -/
theorem pairMinor_bits {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) ℚ)
    (E : Matrix (Fin rE) (Fin n) ℚ) (u : PairMinorIndex rD rE n) :
    let L := matrixEncodingLength D + matrixEncodingLength E
    ratBits (pairMinorValue D E u) ≤ 3 + 2*L^2 + 2*L^4 := by
  dsimp only
  rcases u with ⟨k,r,c⟩ | ⟨k,r,c⟩
  · apply (rational_minor_bits D r.toEmbedding c.toEmbedding).trans
    gcongr <;> omega
  · apply (rational_minor_bits E r.toEmbedding c.toEmbedding).trans
    gcongr <;> omega

theorem pairMinor_abs_log {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) ℚ)
    (E : Matrix (Fin rE) (Fin n) ℚ) (u : NonzeroPairMinor D E) :
    let L := matrixEncodingLength D + matrixEncodingLength E
    abs (Real.logb 2 (abs ((pairMinorValue D E u.val : ℚ) : ℝ))) ≤ ((3+2*L^2+2*L^4 : ℕ) : ℝ) :=
  (abs_logb_rat_le_bits u.property).trans (Nat.cast_le.mpr (pairMinor_bits D E u.val))

/-- Over rationals there is one polynomial in the total input bit length bounding every
scalar register throughout this fixed program, including the empty minor. -/
theorem rational_pairProgram_trace {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) ℚ)
    (E : Matrix (Fin rE) (Fin n) ℚ) (u : PairMinorIndex rD rE n) :
    let v := pairLayout D E u
    let B := 3 + matrixEncodingLength D + matrixEncodingLength E
    ∃ tr : Fin (loaderCost v+1+1) → State ℚ,
      Trace program ((pairMemory D E u).atPC 0) (loaderCost v+1) tr ∧
      (tr (Fin.last _)).output = some 0 ∧
      (Matrix.of (fun i j : Fin v.k => (tr (Fin.last _)).data (v.dst+(i.val*v.k+j.val)))).det =
        pairMinorValue D E u ∧ (∀ i j, (tr (Fin.last _)).data (v.dst+(i.val*v.k+j.val)) =
          v.matrix (v.row i) (v.col j)) ∧ ∀ i, scalarBound B (tr i) := by
  apply pairProgram_trace D E u (P := fun q => ratBits q ≤ 3 + matrixEncodingLength D + matrixEncodingLength E)
  · change 3 ≤ _; omega
  · intro i j
    have h := matrix_entry_bits_le D i j
    omega
  · intro i j
    have h := matrix_entry_bits_le E i j
    omega

end MinorLoad
end Compression
end LinearProgramming
end Optimization
end OAI
