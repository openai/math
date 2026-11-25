import OAI.Optimization.LinearProgramming.RAM.Loops
import OAI.Optimization.LinearProgramming.PrimalDual.Bits
import OAI.Optimization.LinearProgramming.Geometry.Pivot

/-! An instruction-counted scan for the maximizing nonzero pivot. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PivotRAM

open RAM RAM.Block
open scoped BigOperators

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Scan the materialized triples `(signed minor, returned log, price)` in column order.
A zero minor is skipped. The incumbent changes only on a strict improvement. -/
def accept : Block := .straight [.addrCopy 3 1, .copy 5 4]

def choosePositive : Block := .branch (.addrLT 3 0) (.branch (.scalarLT 5 4) accept .skip) accept

def choose : Block := .branch (.scalarLT 1 0) choosePositive
  (.branch (.scalarLT 0 1) choosePositive .skip)

def readTriple : Block := .straight [.load 1 2, .incr 2 2, .load 2 2, .incr 2 2,
  .load 3 2, .incr 2 2, .sub 4 2 3]

def scanBlock : Block := .seq (.straight [.const 0 0, .addrCopy 2 4, .addrCopy 3 0])
  (.forRange 1 0 (.seq readTriple choose))

/-- Address 3 uses the array length as the sentinel; address 1 is this column. -/
private def accepted (m : Memory K) : Memory K := (m.putIndex 3 (m.index 1)).putData 5 (m.data 4)

private abbrev Safe (P : K → Prop) (m : Memory K) := ∀ r, P (m.data r)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem safe_write {P : K → Prop} {m : Memory K} (hm : Safe P m) (d : Nat) {v : K} (hv : P v) :
    Safe P (m.putData d v) := by
  intro r
  by_cases hr : r = d
  · simpa [hr] using hv
  · simpa [hr] using hm r

private theorem accept_eval (m : Memory K) (P : K → Prop) (hm : Safe P m) :
    Eval (Safe P) accept m 2 (accepted m) := by
  let t := m.putIndex 3 (m.index 1)
  have ea : Eval (Safe P) (.op (.addrCopy 3 1)) m 1 t := Eval.op_addrCopy _ _ _ hm hm
  have hs : Safe P (accepted m) := safe_write (m := t) hm _ (hm 4)
  have eb : Eval (Safe P) (.op (.copy 5 4)) t 1 (accepted m) := Eval.op_copy _ _ _ hm hs
  exact ea.seq (eb.seq (.skip hs))

private def chosen (m : Memory K) : Memory K :=
  if m.data 1 ≠ 0 ∧ (m.index 0 ≤ m.index 3 ∨ m.data 5 < m.data 4) then accepted m else m

private theorem choosePositive_eval (m : Memory K) (P : K → Prop) (hm : Safe P m) :
    ∃ k ≤ 6, Eval (Safe P) choosePositive m k (if m.index 0 ≤ m.index 3 ∨ m.data 5 < m.data 4 then accepted m else m) := by
  unfold choosePositive
  by_cases found : m.index 3 < m.index 0
  · by_cases wins : m.data 5 < m.data 4
    · refine ⟨6, by decide, ?_⟩
      simp only [wins, or_true, ↓reduceIte]
      exact Eval.branchTrue (by simp [Cond.test,found]) (Eval.branchTrue (by simp [Cond.test,wins]) (accept_eval m P hm))
    · refine ⟨3, by decide, ?_⟩
      simp only [found.not_ge, wins, or_false, ↓reduceIte]
      exact Eval.branchTrue (by simp [Cond.test,found]) (Eval.branchFalse (by simp [Cond.test,wins]) (.skip hm))
  · refine ⟨3, by decide, ?_⟩
    simp only [le_of_not_gt found, true_or, ↓reduceIte]
    exact Eval.branchFalse (by simp [Cond.test,found]) (accept_eval m P hm)

private theorem choose_eval (m : Memory K) (P : K → Prop) (hm : Safe P m) (h0 : m.data 0 = 0) :
    ∃ k ≤ 9, Eval (Safe P) choose m k (if m.data 1 ≠ 0 ∧ (m.index 0 ≤ m.index 3 ∨ m.data 5 < m.data 4)
      then accepted m else m) := by
  obtain ⟨k,hk,he⟩ := choosePositive_eval m P hm
  unfold choose
  rcases lt_trichotomy (m.data 1) 0 with h | h | h
  · refine ⟨1+k+1, by omega, ?_⟩
    simp only [h.ne, ne_eq, not_false_eq_true, true_and]
    exact Eval.branchTrue (by simp [Cond.test,h0,h]) he
  · refine ⟨2, by decide, ?_⟩
    simp only [h, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
    exact Eval.branchFalse (by simp [Cond.test,h0,h]) (Eval.branchFalse (by simp [Cond.test,h0,h]) (.skip hm))
  · refine ⟨1+(1+k+1), by omega, ?_⟩
    simp only [h.ne', ne_eq, not_false_eq_true, true_and]
    exact Eval.branchFalse (by simp [Cond.test,h0,h.not_gt]) (Eval.branchTrue (by simp [Cond.test,h0,h]) he)

/-- Inputs are contiguous triples in memory, at addresses at least 6. -/
def inputMinor (m : Memory K) (j : ℕ) := m.data (m.index 4 + 3*j)
def inputLog (m : Memory K) (j : ℕ) := m.data (m.index 4 + 3*j+1)
def inputPrice (m : Memory K) (j : ℕ) := m.data (m.index 4 + 3*j+2)
def inputScore (m : Memory K) (j : ℕ) := inputLog m j - inputPrice m j

/-- The same first-maximizer as `List.argmax`, computed on the first `j` input cells. -/
def incumbent (m : Memory K) (j : ℕ) : Option Nat :=
  ((List.range j).filter fun i => inputMinor m i ≠ 0).argmax (inputScore m)

omit [IsStrictOrderedRing K] in
private theorem incumbent_lt {m : Memory K} {j i : ℕ} (h : incumbent m j = some i) : i < j := by
  exact List.mem_range.mp (List.mem_filter.mp (List.argmax_eq_some_iff.mp h).1).1

omit [IsStrictOrderedRing K] in
private theorem incumbent_succ (m : Memory K) (j : ℕ) : incumbent m (j+1) =
    if inputMinor m j = 0 then incumbent m j else
      (incumbent m j).elim (some j) (fun i => if inputScore m i < inputScore m j then some j else some i) := by
  by_cases h : inputMinor m j = 0
  · simp [incumbent, List.range_succ, h]
  · rw [incumbent, List.range_succ, List.filter_append]
    simp only [h, ne_eq, not_false_eq_true, decide_true, List.filter_cons_of_pos, List.filter_nil,
      ↓reduceIte, List.argmax_concat]
    cases hprev : incumbent m j <;> unfold incumbent at hprev <;> rw [hprev] <;> rfl

omit [IsStrictOrderedRing K] in
private theorem chosen_index (s : Memory K) {u : ℕ} (hu : u ≠ 3) : (chosen s).index u = s.index u := by
  unfold chosen; split <;> simp [accepted, hu]

omit [IsStrictOrderedRing K] in
private theorem chosen_data (s : Memory K) {u : ℕ} (hu : u ≠ 5) : (chosen s).data u = s.data u := by
  unfold chosen; split <;> simp [accepted, hu]

omit [IsStrictOrderedRing K] in
private theorem chosen_correct (m s : Memory K) (j : ℕ) (hj : j < m.index 0)
    (hn : s.index 0 = m.index 0) (hc : s.index 1 = j)
    (hw : s.index 3 = (incumbent m j).getD (m.index 0))
    (hval : ∀ i, incumbent m j = some i → s.data 5 = inputScore m i)
    (hx : s.data 1 = inputMinor m j) (hnew : s.data 4 = inputScore m j) :
    (chosen s).index 3 = (incumbent m (j+1)).getD (m.index 0) ∧
      ∀ i, incumbent m (j+1) = some i → (chosen s).data 5 = inputScore m i := by
  by_cases hz : inputMinor m j = 0
  · simpa [chosen, hx, hz, incumbent_succ] using And.intro hw hval
  · cases e : incumbent m j with
    | none =>
      simp [e] at hw
      simp [chosen, hx, hz, hw, hn, accepted, hc, hnew, incumbent_succ, e]
    | some i =>
      have hi : i < m.index 0 := (incumbent_lt e).trans hj
      have h5 := hval _ e
      simp [e] at hw
      by_cases wins : inputScore m i < inputScore m j <;>
        simp [chosen, hx, hz, hn, hw, hi.not_ge, hc, h5, hnew, wins, accepted, incumbent_succ, e]

private structure Inv (P : K → Prop) (m : Memory K) (j : ℕ) (s : Memory K) : Prop where
  safe : Safe P s
  size : s.index 0 = m.index 0
  counter : s.index 1 = j
  ptr : s.index 2 = m.index 4 + 3*j
  winner : s.index 3 = (incumbent m j).getD (m.index 0)
  best : ∀ i, incumbent m j = some i → s.data 5 = inputScore m i
  zero : s.data 0 = 0
  scalarFrame : ∀ u, 6 ≤ u → s.data u = m.data u
  indexFrame : ∀ u, 4 ≤ u → s.index u = m.index u

private theorem body_spec (P : K → Prop) (m s : Memory K) (j : ℕ) (hj : j < m.index 0)
    (hbase : 6 ≤ m.index 4) (h : Inv P m j s) (pnew : P (inputScore m j)) :
    ∃ t k, k ≤ 16 ∧ Eval (Safe P) (.seq readTriple choose) s k t ∧
      Inv P m (j+1) (t.putIndex 1 (t.index 1 + 1)) := by
  let ptr := m.index 4 + 3*j
  have hp : 6 ≤ ptr := by dsimp [ptr]; omega
  have hload1 : s.data (s.index 2) = inputMinor m j := by
    rw [h.ptr,h.scalarFrame _ hp]; rfl
  let s1 := s.putData 1 (inputMinor m j)
  let s2 := s1.putIndex 2 (ptr+1)
  let s3 := s2.putData 2 (inputLog m j)
  let s4 := s3.putIndex 2 (ptr+2)
  let s5 := s4.putData 3 (inputPrice m j)
  let s6 := s5.putIndex 2 (ptr+3)
  let s7 := s6.putData 4 (inputScore m j)
  have hload2 : s2.data (s2.index 2) = inputLog m j := by
    change (s.putData 1 (inputMinor m j)).data (ptr+1) = m.data (ptr+1)
    rw [Memory.putData_ne s (show ptr+1 ≠ 1 by omega), h.scalarFrame _ (by omega)]
  have hload3 : s4.data (s4.index 2) = inputPrice m j := by
    change ((s.putData 1 (inputMinor m j)).putData 2 (inputLog m j)).data (ptr+2) = m.data (ptr+2)
    rw [Memory.putData_ne _ (show ptr+2 ≠ 2 by omega), Memory.putData_ne s (show ptr+2 ≠ 1 by omega),
      h.scalarFrame _ (by omega)]
  have e1 : Eval (Safe P) (.op (.load 1 2)) s 1 s1 := by
    change Eval _ _ _ _ (s.putData 1 (inputMinor m j))
    rw [← hload1]; exact Eval.op_load _ _ _ h.safe (safe_write h.safe _ (h.safe _))
  have e2 : Eval (Safe P) (.op (.incr 2 2)) s1 1 s2 := by
    simpa [s2,s1,h.ptr,ptr] using Eval.op_incr s1 2 2 e1.safe_end e1.safe_end
  have e3 : Eval (Safe P) (.op (.load 2 2)) s2 1 s3 := by
    change Eval _ _ _ _ (s2.putData 2 (inputLog m j))
    rw [← hload2]; exact Eval.op_load _ _ _ e2.safe_end (safe_write e2.safe_end _ (e2.safe_end _))
  have e4 : Eval (Safe P) (.op (.incr 2 2)) s3 1 s4 := by
    simpa [s4,s3,s2,Nat.add_assoc] using Eval.op_incr s3 2 2 e3.safe_end e3.safe_end
  have e5 : Eval (Safe P) (.op (.load 3 2)) s4 1 s5 := by
    change Eval _ _ _ _ (s4.putData 3 (inputPrice m j))
    rw [← hload3]; exact Eval.op_load _ _ _ e4.safe_end (safe_write e4.safe_end _ (e4.safe_end _))
  have e6 : Eval (Safe P) (.op (.incr 2 2)) s5 1 s6 := by
    simpa [s6,s5,s4,Nat.add_assoc] using Eval.op_incr s5 2 2 e5.safe_end e5.safe_end
  have sub : s6.data 2 - s6.data 3 = inputScore m j := by simp [s6,s5,s4,s3,inputScore]
  have e7 : Eval (Safe P) (.op (.sub 4 2 3)) s6 1 s7 := by
    simpa only [s7,sub] using Eval.op_sub s6 4 2 3 e6.safe_end (safe_write e6.safe_end 4 (sub.symm ▸ pnew))
  have read : Eval (Safe P) readTriple s 7 s7 :=
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (.skip e7.safe_end)))))))
  have hzero : s7.data 0 = 0 := by simpa [s7,s6,s5,s4,s3,s2,s1] using h.zero
  obtain ⟨k,hk,hchoose⟩ := choose_eval s7 P e7.safe_end hzero
  change Eval (Safe P) choose s7 k (chosen s7) at hchoose
  have hsz : s7.index 0 = m.index 0 := by simpa [s7,s6,s5,s4,s3,s2,s1] using h.size
  have hco : s7.index 1 = j := by simpa [s7,s6,s5,s4,s3,s2,s1] using h.counter
  have hwin := chosen_correct m s7 j hj hsz hco
    (by simpa [s7,s6,s5,s4,s3,s2,s1] using h.winner)
    (fun i hi => by simpa [s7,s6,s5,s4,s3,s2,s1] using h.best i hi)
    (by simp [s7,s6,s5,s4,s3,s2,s1]) (by simp [s7])
  refine ⟨chosen s7, 7+k, by omega, read.seq hchoose, ⟨hchoose.safe_end, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa [chosen_index] using hsz
  · simp [chosen_index,hco]
  · simp [chosen_index,s7,s6,ptr,Nat.mul_succ,Nat.add_assoc]
  · simpa using hwin.1
  · simpa using hwin.2
  · simpa [chosen_data] using hzero
  · intro u hu
    simp [chosen_data _ (show u ≠ 5 by omega),s7,s6,s5,s4,s3,s2,s1,show u ≠ 4 by omega,
      show u ≠ 3 by omega,show u ≠ 2 by omega,show u ≠ 1 by omega,h.scalarFrame u hu]
  · intro u hu
    simp [show u ≠ 1 by omega,chosen_index _ (show u ≠ 3 by omega),s7,s6,s5,s4,s3,s2,s1,
      show u ≠ 2 by omega,h.indexFrame u hu]

/-- A fixed counted RAM loop scans every input column exactly once. Address register 3
returns the index of the first maximizing nonzero column, or the dimension for an empty
candidate set. Every scalar written is copied input, zero, or a single difference. -/
theorem scanBlock_spec_full (m : Memory K) (P : K → Prop) (hs : ∀ u, P (m.data u)) (h0 : P 0)
    (hbase : 6 ≤ m.index 4) (hscore : ∀ j < m.index 0, P (inputScore m j)) :
    ∃ t k, k ≤ 19 * m.index 0 + 5 ∧ Eval (fun s => ∀ u, P (s.data u)) scanBlock m k t ∧
      t.index 3 = (incumbent m (m.index 0)).getD (m.index 0) ∧
      (∀ i, incumbent m (m.index 0) = some i → t.data 5 = inputScore m i) ∧
      (∀ u, 6 ≤ u → t.data u = m.data u) ∧ (∀ u, 4 ≤ u → t.index u = m.index u) ∧ t.index 0 = m.index 0 := by
  let s1 := m.putData 0 0
  let s2 := s1.putIndex 2 (m.index 4)
  let s3 := s2.putIndex 3 (m.index 0)
  have p1 : Safe P s1 := safe_write hs 0 h0
  have e1 : Eval (Safe P) (.op (.const 0 0)) m 1 s1 := by
    simpa [s1] using Eval.op_const m 0 (0 : ℚ) hs (by simpa [s1] using p1)
  have e2 : Eval (Safe P) (.op (.addrCopy 2 4)) s1 1 s2 := Eval.op_addrCopy s1 2 4 p1 p1
  have e3 : Eval (Safe P) (.op (.addrCopy 3 0)) s2 1 s3 := by
    simpa [s3,s2,s1] using Eval.op_addrCopy s2 3 0 p1 p1
  have init : Inv P m 0 (s3.putIndex 1 0) := by
    refine ⟨p1,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [s3,s2,s1]
    · simp
    · simp [s3,s2]
    · simp [s3,incumbent]
    · simp [incumbent]
    · simp [s3,s2,s1]
    · intro u hu; simp [s3,s2,s1,show u ≠ 0 by omega]
    · intro u hu; simp [s3,s2,s1,show u ≠ 1 by omega,show u ≠ 2 by omega,show u ≠ 3 by omega]
  obtain ⟨t,k,hk,run,ht⟩ := Eval.forRange_invariant (body := .seq readTriple choose)
    1 0 (m.index 0) 16 (Inv P m) s3 p1 init
    (fun j s h => ⟨h.safe,h.counter,h.size⟩)
    (fun j hj s h => body_spec P m s j hj hbase h (hscore j hj))
  have start : Eval (Safe P) (.straight [.const 0 0,.addrCopy 2 4,.addrCopy 3 0]) m 3 s3 :=
    e1.seq (e2.seq (e3.seq (.skip p1)))
  exact ⟨t,3+k,by omega,start.seq run,ht.winner,ht.best,ht.scalarFrame,ht.indexFrame,ht.size⟩

/-- The same scan contract without the preserved dimension register. -/
theorem scanBlock_spec (m : Memory K) (P : K → Prop) (hs : ∀ u, P (m.data u)) (h0 : P 0)
    (hbase : 6 ≤ m.index 4) (hscore : ∀ j < m.index 0, P (inputScore m j)) :
    ∃ t k, k ≤ 19 * m.index 0 + 5 ∧ Eval (fun s => ∀ u, P (s.data u)) scanBlock m k t ∧
      t.index 3 = (incumbent m (m.index 0)).getD (m.index 0) ∧
      (∀ i, incumbent m (m.index 0) = some i → t.data 5 = inputScore m i) ∧
      (∀ u, 6 ≤ u → t.data u = m.data u) ∧ (∀ u, 4 ≤ u → t.index u = m.index u) := by
  obtain ⟨t,k,hk,run,win,best,data,idx,_⟩ := scanBlock_spec_full m P hs h0 hbase hscore
  exact ⟨t,k,hk,run,win,best,data,idx⟩

/-- Real instruction trace with the rational bit-size bound at every intermediate register. -/
theorem scan_trace (m : Memory ℚ) (B : ℕ) (hs : ∀ u, ratBits (m.data u) ≤ B) (hbase : 6 ≤ m.index 4) :
    ∃ k ≤ 19*m.index 0 + 6, ∃ t : Fin (k+1) → State ℚ,
      Trace (scanBlock.compile 0 ++ [.halt 0]) (m.atPC 0) k t ∧
      (t (Fin.last k)).output = some 0 ∧
      (t (Fin.last k)).index 3 = (incumbent m (m.index 0)).getD (m.index 0) ∧
      ∀ j, scalarBound (3+4*B) (t j) := by
  let P := fun q : ℚ => ratBits q ≤ 3+4*B
  obtain ⟨u,cost,hcost,run,hwin,_,_,_⟩ := scanBlock_spec m P (fun u => (hs u).trans (by omega))
    (by change ratBits 0 ≤ _; rw [show ratBits 0 = 3 by decide]; omega) hbase (fun j _ => by
      dsimp [P, inputScore]
      have h := PrimalDual.ratBits_sub_le (inputLog m j) (inputPrice m j)
      have h1 := hs (m.index 4+3*j+1)
      have h2 := hs (m.index 4+3*j+2)
      change ratBits (inputLog m j) ≤ B at h1
      change ratBits (inputPrice m j) ≤ B at h2
      omega)
  obtain ⟨t,ht,ho,hm,hall⟩ := run.halted_trace (tag := 0)
  exact ⟨cost+1,by omega,t,ht,ho,(congrArg (fun z : Memory ℚ => z.index 3) hm).trans hwin,hall⟩

end PivotRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
