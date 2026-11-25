import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.RAM.CallMemory
import Mathlib.Tactic

/-! # Restoring the caller's scalar bank after a binary reply

The result occupies physical scalar 0. Copy live saved caller scalars from
physical 2i+1 into physical i, for i starting at one. The source remains
strictly ahead of the output and is odd, so scalar scratch 6 is harmless.
Only odd address registers 3 and 5 are used as scan pointers. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

private def restoreScalarTick : Block :=
  .seq (.op (.load 6 5)) <| .seq (.op (.store 3 6)) <| .seq (.op (.incr 3 3)) <|
    .seq (.op (.incr 5 5)) (.op (.incr 5 5))

def restoreScalarFrameBlock : Block :=
  .seq (.op (.addrConst 3 1)) (.seq (.op (.addrConst 5 3))
    (.loop (.addrLT 3 1) restoreScalarTick))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem restoreScalarTick_spec (m : Memory K) {P : K → Prop} (hm : m.AllData P) :
    ∃ z, Block.Eval (Memory.AllData P) restoreScalarTick m 5 z ∧
      z.data (m.index 3)=m.data (m.index 5) ∧
      (∀ i, i≠6 → i≠m.index 3 → z.data i=m.data i) ∧
      z.index 3=m.index 3+1 ∧ z.index 5=m.index 5+2 ∧
      ∀ i, i≠3 → i≠5 → z.index i=m.index i := by
  let l := m.putData 6 (m.data (m.index 5))
  let w := l.putData (l.index 3) (l.data 6)
  let d := w.putIndex 3 (w.index 3+1)
  let s := d.putIndex 5 (d.index 5+1)
  let z := s.putIndex 5 (s.index 5+1)
  have el : Block.Eval (Memory.AllData P) (.op (.load 6 5)) m 1 l :=
    Block.Eval.op_load _ _ _ hm (hm.putData _ (hm _))
  have ew : Block.Eval (Memory.AllData P) (.op (.store 3 6)) l 1 w :=
    Block.Eval.op_store _ _ _ el.safe_end (el.safe_end.putData _ (el.safe_end _))
  have ed : Block.Eval (Memory.AllData P) (.op (.incr 3 3)) w 1 d :=
    Block.Eval.op_incr _ _ _ ew.safe_end ew.safe_end
  have es : Block.Eval (Memory.AllData P) (.op (.incr 5 5)) d 1 s :=
    Block.Eval.op_incr _ _ _ ed.safe_end ed.safe_end
  have ez : Block.Eval (Memory.AllData P) (.op (.incr 5 5)) s 1 z :=
    Block.Eval.op_incr _ _ _ es.safe_end es.safe_end
  refine ⟨z, el.seq (ew.seq (ed.seq (es.seq ez))), ?_, ?_, ?_, ?_, ?_⟩
  · exact Memory.putData_same ..
  · intro i h6 hdst
    exact (Memory.putData_ne l hdst _).trans (Memory.putData_ne m h6 _)
  · simp [z,s,d,w,l]
  · simp [z,s,d,w,l,Nat.add_assoc]
  · intro i h3 h5
    simp [z,s,d,w,l,h3,h5]

private structure RestoreScalarInv (P : K → Prop) (m : Memory K) (j : ℕ) (s : Memory K) : Prop where
  safe : s.AllData P
  destination : s.index 3=1+j
  source : s.index 5=3+2*j
  indexFrame (i : ℕ) : i≠3 → i≠5 → s.index i=m.index i
  written (i : ℕ) : 1 ≤ i → i < 1+j → i≠6 → s.data i=m.data (2*i+1)
  dataFrame (i : ℕ) : i≠6 → (i=0 ∨ 1+j ≤ i) → s.data i=m.data i

/-- The complete scalar restore on arbitrary physical memory. The exit at zero
or one live cell is a valid execution and preserves the result in cell zero. -/
theorem restoreScalarFrameBlock_on (m : Memory K) (live : ℕ) {P : K → Prop}
    (hm : m.AllData P) (hlen : m.index 1=live) :
    ∃ z, Block.Eval (Memory.AllData P) restoreScalarFrameBlock m (7*(live-1)+3) z ∧
      z.data 0=m.data 0 ∧ (∀ i, 1 ≤ i → i<live → i≠6 → z.data i=m.data (2*i+1)) ∧
      (∀ i, i≠6 → live ≤ i → z.data i=m.data i) ∧
      (∀ i, i≠3 → i≠5 → z.index i=m.index i) := by
  let u := m.putIndex 3 1
  let v := u.putIndex 5 3
  have eu : Block.Eval (Memory.AllData P) (.op (.addrConst 3 1)) m 1 u :=
    Block.Eval.op_addrConst _ _ _ hm hm
  have ev : Block.Eval (Memory.AllData P) (.op (.addrConst 5 3)) u 1 v :=
    Block.Eval.op_addrConst _ _ _ eu.safe_end eu.safe_end
  have start : RestoreScalarInv P m 0 v := by
    refine ⟨ev.safe_end, by simp [v,u], by simp [v], ?_, fun i hi hlo _ => by omega, fun _ _ _ => rfl⟩
    intro i h3 h5
    simp [v,u,h3,h5]
  obtain ⟨z,loop,fin⟩ := Block.Eval.loop_invariant_exact (safe := Memory.AllData P) (c := .addrLT 3 1)
    (body := restoreScalarTick) (RestoreScalarInv P m) v (live-1) 5 start (by
      intro j hj s hs
      have h1 := (hs.indexFrame 1 (by decide) (by decide)).trans hlen
      have test : (Cond.addrLT 3 1).test s=true := by
        simp only [Cond.test,hs.destination,h1,decide_eq_true_eq]
        omega
      obtain ⟨t, he, cell, frame, hd, hr, fi⟩ := restoreScalarTick_spec s hs.safe
      have rv : s.data (s.index 5)=m.data (2*(1+j)+1) := by
        rw [hs.source]
        have read := hs.dataFrame (3+2*j) (by omega) (Or.inr (by omega))
        simpa only [show 2*(1+j)+1=3+2*j by omega] using read
      refine ⟨test, t, he, he.safe_end, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [hd,hs.destination,Nat.add_assoc]
      · rw [hr,hs.source]; omega
      · intro i h3 h5
        exact (fi i h3 h5).trans (hs.indexFrame i h3 h5)
      · intro i hi hlo h6
        by_cases e : i=1+j
        · subst i
          rw [← hs.destination]
          exact cell.trans (by rw [hs.destination]; exact rv)
        · exact (frame i h6 (by rw [hs.destination]; omega)).trans (hs.written i hi (by omega) h6)
      · intro i h6 hwin
        exact (frame i h6 (by rw [hs.destination]; omega)).trans (hs.dataFrame i h6 (by omega)))
    (by
      intro s hs
      refine ⟨?_,hs.safe⟩
      have h1 := (hs.indexFrame 1 (by decide) (by decide)).trans hlen
      simp only [Cond.test,hs.destination,h1,decide_eq_false_iff_not]
      omega)
  refine ⟨z, ?_, fin.dataFrame 0 (by decide) (Or.inl rfl), ?_, ?_, fin.indexFrame⟩
  · rw [show 7*(live-1)+3 = 1+(1+((live-1)*(5+2)+1)) by omega]
    exact eu.seq (ev.seq loop)
  · intro i hi hlo h6
    exact fin.written i hi (by omega) h6
  · intro i h6 hlo
    exact fin.dataFrame i h6 (by omega)

/-- Restoring `Call.pack` gives the original caller scalars at all live cells
other than result 0 and scratch 6. Every physically even address cell, which
encodes the virtual callee's output address bank, is untouched. -/
theorem restoreScalarFrameBlock_spec (callee frame : Memory ℚ) (live : ℕ) {P : ℚ → Prop}
    (hm : (Call.pack callee frame).AllData P) (hlen : frame.index 0=live) :
    ∃ z, Block.Eval (Memory.AllData P) restoreScalarFrameBlock (Call.pack callee frame)
          (7*(live-1)+3) z ∧
      z.data 0=callee.data 0 ∧ (∀ i, 1 ≤ i → i<live → i≠6 → z.data i=frame.data i) ∧
      (∀ i, z.index (2*i)=(Call.pack callee frame).index (2*i)) ∧
      (∀ i, i≠3 → i≠5 → z.index i=(Call.pack callee frame).index i) := by
  have hi : (Call.pack callee frame).index 1=live := by simpa [Call.pack] using hlen
  obtain ⟨z,run,zero,rows,_,indices⟩ := restoreScalarFrameBlock_on (Call.pack callee frame) live hm hi
  exact ⟨z,run,zero.trans (Call.data_even callee frame 0),
    fun i hp hu hs => (rows i hp hu hs).trans (Call.data_odd callee frame i),
    fun i => indices (2*i) (by omega) (by omega),indices⟩

end Compression
end LinearProgramming
end Optimization
end OAI
