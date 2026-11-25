import OAI.Optimization.LinearProgramming.RAM.Loops

/-! Transfer the winning pivot and array metadata from the selection scan to the rounding pass. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PivotPrepareRAM

open RAM RAM.Block

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Walk along packed triples to the winning column, one address increment per cell. -/
def block : Block :=
  .seq (.straight [.addrCopy 7 4, .addrCopy 9 0, .addrCopy 11 4]) <|
    .seq (.forRange 10 3 (.straight [.incr 11 11, .incr 11 11, .incr 11 11]))
      (.straight [.load 21 11, .copy 22 5])

/-- Only the rounding inputs and two scratch address registers are changed. -/
structure Prepared (m t : Memory K) : Prop where
  source : t.index 7 = m.index 4
  count : t.index 9 = m.index 0
  pivot : t.data 21 = m.data (m.index 4 + 3 * m.index 3)
  winning : t.data 22 = m.data 5
  data (r) : r ≠ 21 → r ≠ 22 → t.data r = m.data r
  index (r) : r ≠ 7 → r ≠ 9 → r ≠ 10 → r ≠ 11 → t.index r = m.index r

private structure WalkInv (m : Memory K) (k : ℕ) (t : Memory K) : Prop where
  data : t.data = m.data
  counter : t.index 10 = k
  ptr : t.index 11 = m.index 11 + 3*k
  frame (r) : r ≠ 10 → r ≠ 11 → t.index r = m.index r

private theorem walk_spec (m : Memory K) (P : K → Prop) (hs : ∀ i, P (m.data i)) :
    ∃ t, Eval (fun s => ∀ r, P (s.data r))
      (.forRange 10 3 (.straight [.incr 11 11, .incr 11 11, .incr 11 11]))
      m (m.index 3 * (3+3) + 2) t ∧ WalkInv m (m.index 3) t := by
  apply Eval.forRange_invariant_exact 10 3 (m.index 3) 3 (WalkInv m) m hs
  · refine ⟨rfl, by simp, by simp, ?_⟩
    intro r hr _
    simp [hr]
  · intro i s h
    exact ⟨fun r => by rw [h.data]; exact hs r, h.counter, h.frame _ (by decide) (by decide)⟩
  · intro j _ s h
    let u := s.putIndex 11 (s.index 11+1)
    let v := u.putIndex 11 (u.index 11+1)
    let w := v.putIndex 11 (v.index 11+1)
    have hsafe : ∀ r, P (s.data r) := by rw [h.data]; exact hs
    have e1 := Eval.op_incr (safe := fun t => ∀ r, P (t.data r)) s 11 11 hsafe hsafe
    have e2 := Eval.op_incr (safe := fun t => ∀ r, P (t.data r)) u 11 11 hsafe hsafe
    have e3 := Eval.op_incr (safe := fun t => ∀ r, P (t.data r)) v 11 11 hsafe hsafe
    refine ⟨w, e1.seq (e2.seq (e3.seq (.skip hsafe))), ?_⟩
    constructor
    · exact h.data
    · simp [w,v,u,h.counter]
    · simp [w,v,u,h.ptr,Nat.mul_succ,Nat.add_assoc]
    · intro r r10 r11
      simp [w,v,u,r10,r11,h.frame _ r10 r11]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem safe_write (m : Memory K) (P : K → Prop) (hs : ∀ i, P (m.data i))
    (d : ℕ) (v : K) (hv : P v) : ∀ i, P ((m.putData d v).data i) := by
  intro i
  by_cases h : i = d
  · simpa [h] using hv
  · simpa [h] using hs i

/-- On any incoming register file the block takes exactly six instructions per preceding
column, plus seven for initialization, the final guard and the two scalar copies. -/
theorem block_spec (m : Memory K) (P : K → Prop) (hs : ∀ i, P (m.data i)) :
    ∃ t, Eval (fun s => ∀ r, P (s.data r)) block m (6 * m.index 3 + 7) t ∧ Prepared m t := by
  let s1 := m.putIndex 7 (m.index 4)
  let s2 := s1.putIndex 9 (m.index 0)
  let s3 := s2.putIndex 11 (m.index 4)
  have e1 := Eval.op_addrCopy (safe := fun s => ∀ r, P (s.data r)) m 7 4 hs hs
  have e2 : Eval (fun s => ∀ r, P (s.data r)) (.op (.addrCopy 9 0)) s1 1 s2 := by
    simpa [s1,s2] using Eval.op_addrCopy (safe := fun s => ∀ r, P (s.data r)) s1 9 0 hs hs
  have e3 : Eval (fun s => ∀ r, P (s.data r)) (.op (.addrCopy 11 4)) s2 1 s3 := by
    simpa [s1,s2,s3] using Eval.op_addrCopy (safe := fun s => ∀ r, P (s.data r)) s2 11 4 hs hs
  obtain ⟨w,walk,hw⟩ := walk_spec s3 P hs
  let u := w.putData 21 (w.data (w.index 11))
  let t := u.putData 22 (u.data 5)
  have sw := walk.safe_end
  have su : ∀ r, P (u.data r) := safe_write _ _ sw _ _ (sw _)
  have st : ∀ r, P (t.data r) := safe_write _ _ su _ _ (su _)
  have load := Eval.op_load (safe := fun s => ∀ r, P (s.data r)) w 21 11 sw su
  have copy := Eval.op_copy (safe := fun s => ∀ r, P (s.data r)) u 22 5 su st
  refine ⟨t, ?_, ?_⟩
  · have h3 : s3.index 3 = m.index 3 := by simp [s1,s2,s3]
    rw [show 6 * m.index 3 + 7 = 3 + ((s3.index 3*(3+3)+2)+2) by rw [h3]; omega]
    exact (e1.seq (e2.seq (e3.seq (.skip hs)))).seq (walk.seq (load.seq (copy.seq (.skip st))))
  · constructor
    · simpa [t,u,s3,s2,s1] using hw.frame 7 (by decide) (by decide)
    · simpa [t,u,s3,s2,s1] using hw.frame 9 (by decide) (by decide)
    · simp [t,u,hw.data,hw.ptr,s3,s2,s1]
    · simp [t,u,hw.data,s3,s2,s1]
    · intro r h21 h22
      simp [t,u,h21,h22,hw.data,s3,s2,s1]
    · intro r h7 h9 h10 h11
      simpa [t,u,s3,s2,s1,h7,h9,h11] using hw.frame r h10 h11

end PivotPrepareRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
