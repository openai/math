import OAI.Optimization.LinearProgramming.RAM.Loops
import OAI.Optimization.LinearProgramming.Geometry.PowerRAM

/-! A row pass over packed minor/log/price triples. The scalar rounding kernel has its
own scratch area; the input, output, outer counters, and chosen pivot persist across cells. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace RowRAM

open RAM RAM.Block

abbrev Within (width : ℕ) (m : Memory ℚ) := ∀ j, ratBits (m.data j) ≤ width

/-- Start addresses for the input triples and output row are in 7 and 8. Address 9 is the
number of columns, 6 is the bit precision, and scalars 21/22 hold pivot and best score. -/
def loadCell : Block := .straight [.load 23 11,.incr 11 11,.load 24 11,.incr 11 11,.load 25 11,.incr 11 11]

def pass (cell : Block) : Block :=
  .seq (.straight [.addrCopy 11 7,.addrCopy 12 8]) <|
    .forRange 10 9 (.seq loadCell (.seq cell (.straight [.store 12 26,.incr 12 12])))

/-- The scalar subroutine is free to reuse its designated working registers. -/
structure CellFrame (old new : Memory ℚ) : Prop where
  data (u) : u = 21 ∨ u = 22 ∨ 26 < u → new.data u = old.data u
  index (u) : 6 ≤ u → new.index u = old.index u

private theorem write {W : ℕ} {m : Memory ℚ} (h : Within W m) (dst : Nat) {v : ℚ}
    (hw : ratBits v ≤ W) : Within W (m.putData dst v) := by
  intro i
  by_cases he : i = dst
  · simpa [he] using hw
  · simpa [he] using h i

private structure Inv (m : Memory ℚ) (value : ℕ → ℚ) (H C j : ℕ) (s : Memory ℚ) : Prop where
  limit : j ≤ m.index 9
  bits : Within (H+j*C) s
  counter : s.index 10 = j
  inputPtr : s.index 11 = m.index 7+3*j
  outputPtr : s.index 12 = m.index 8+j
  addresses (u) : 6 ≤ u → u ≠ 10 → u ≠ 11 → u ≠ 12 → s.index u = m.index u
  pivot : s.data 21 = m.data 21
  winning : s.data 22 = m.data 22
  cells (u) : 27 ≤ u → s.data u = if m.index 8 ≤ u ∧ u < m.index 8+j then value (u-m.index 8) else m.data u

/-- A source address in the input triple range never lies in the output area. -/
private theorem input_unchanged (m : Memory ℚ) {s value H C j} (h : Inv m value H C j s)
    (hbase : 27 ≤ m.index 7) (hsep : m.index 7+3*m.index 9 ≤ m.index 8 ∨ m.index 8+m.index 9 ≤ m.index 7)
    (hj : j < m.index 9) (q : ℕ) (hq : q < 3) :
    s.data (m.index 7+3*j+q) = m.data (m.index 7+3*j+q) := by
  rw [h.cells _ (by omega), ite_eq_right (by omega)]

private theorem loadCell_spec (m : Memory ℚ) {s value H C j} (h : Inv m value H C j s)
    (hbase : 27 ≤ m.index 7) (hsep : m.index 7+3*m.index 9 ≤ m.index 8 ∨ m.index 8+m.index 9 ≤ m.index 7)
    (hj : j < m.index 9) :
    ∃ u, Eval (Within (H+j*C)) loadCell s 6 u ∧
      u.data 23 = m.data (m.index 7+3*j) ∧ u.data 24 = m.data (m.index 7+3*j+1) ∧
      u.data 25 = m.data (m.index 7+3*j+2) ∧ u.index 11 = m.index 7+3*(j+1) ∧
      (∀ i, i ≠ 11 → u.index i = s.index i) ∧
      ∀ i, i ≠ 23 → i ≠ 24 → i ≠ 25 → u.data i = s.data i := by
  let base := m.index 7+3*j
  have hb : 27 ≤ base := by dsimp [base]; omega
  let s1 := s.putData 23 (m.data base)
  let s2 := s1.putIndex 11 (base+1)
  let s3 := s2.putData 24 (m.data (base+1))
  let s4 := s3.putIndex 11 (base+2)
  let s5 := s4.putData 25 (m.data (base+2))
  let s6 := s5.putIndex 11 (base+3)
  have h1 : s.data (s.index 11) = m.data base := by
    rw [h.inputPtr]; exact input_unchanged m h hbase hsep hj 0 (by decide)
  have h2 : s2.data (s2.index 11) = m.data (base+1) := by
    change (s.putData 23 (m.data base)).data (base+1) = m.data (base+1)
    rw [Memory.putData_ne s (show base+1 ≠ 23 by omega)]
    exact input_unchanged m h hbase hsep hj 1 (by decide)
  have h3 : s4.data (s4.index 11) = m.data (base+2) := by
    change ((s.putData 23 (m.data base)).putData 24 (m.data (base+1))).data (base+2) = m.data (base+2)
    rw [Memory.putData_ne _ (show base+2 ≠ 24 by omega), Memory.putData_ne s (show base+2 ≠ 23 by omega)]
    exact input_unchanged m h hbase hsep hj 2 (by decide)
  have e1 : Eval (Within (H+j*C)) (.op (.load 23 11)) s 1 s1 := by
    change Eval _ _ _ _ (s.putData 23 (m.data base)); rw [← h1]
    exact Eval.op_load _ _ _ h.bits (write h.bits _ (h.bits _))
  have e2 : Eval (Within (H+j*C)) (.op (.incr 11 11)) s1 1 s2 := by
    simpa [s2,s1,h.inputPtr,base] using Eval.op_incr s1 11 11 e1.safe_end e1.safe_end
  have e3 : Eval (Within (H+j*C)) (.op (.load 24 11)) s2 1 s3 := by
    change Eval _ _ _ _ (s2.putData 24 (m.data (base+1))); rw [← h2]
    exact Eval.op_load _ _ _ e2.safe_end (write e2.safe_end _ (e2.safe_end _))
  have e4 : Eval (Within (H+j*C)) (.op (.incr 11 11)) s3 1 s4 := by
    simpa [s4,s3,s2,Nat.add_assoc] using Eval.op_incr s3 11 11 e3.safe_end e3.safe_end
  have e5 : Eval (Within (H+j*C)) (.op (.load 25 11)) s4 1 s5 := by
    change Eval _ _ _ _ (s4.putData 25 (m.data (base+2))); rw [← h3]
    exact Eval.op_load _ _ _ e4.safe_end (write e4.safe_end _ (e4.safe_end _))
  have e6 : Eval (Within (H+j*C)) (.op (.incr 11 11)) s5 1 s6 := by
    simpa [s6,s5,s4,Nat.add_assoc] using Eval.op_incr s5 11 11 e5.safe_end e5.safe_end
  refine ⟨s6,e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (.skip e6.safe_end)))))),?_,?_,?_,?_,?_,?_⟩
  · simp [s6,s5,s4,s3,s2,s1,base]
  · simp [s6,s5,s4,s3,base]
  · simp [s6,s5,base]
  · simp [s6,base,Nat.mul_succ,Nat.add_assoc]
  · intro i hi; simp [s6,s5,s4,s3,s2,s1,hi]
  · intro i i23 i24 i25; simp [s6,s5,s4,s3,s2,s1,i23,i24,i25]

/-- The whole array pass. An additive bit-growth estimate for the scalar kernel gives an
additive bound per column, rather than iterating a polynomial on the whole register file. -/
theorem pass_eval (cell : Block) (m : Memory ℚ) (H C steps : ℕ) (value : ℕ → ℚ)
    (hs : Within H m) (hi : 27 ≤ m.index 7) (ho : 27 ≤ m.index 8)
    (hsep : m.index 7+3*m.index 9 ≤ m.index 8 ∨ m.index 8+m.index 9 ≤ m.index 7)
    (kernel : ∀ j < m.index 9, ∀ u : Memory ℚ, Within (H+j*C) u →
      u.index 6 = m.index 6 → u.data 21 = m.data 21 → u.data 22 = m.data 22 →
      u.data 23 = m.data (m.index 7+3*j) → u.data 24 = m.data (m.index 7+3*j+1) →
      u.data 25 = m.data (m.index 7+3*j+2) →
      ∃ v k, k ≤ steps ∧ Eval (Within (H+(j+1)*C)) cell u k v ∧ v.data 26 = value j ∧ CellFrame u v) :
    ∃ t k, k ≤ m.index 9*(steps+11)+4 ∧ Eval (Within (H+m.index 9*C)) (pass cell) m k t ∧
      (∀ j < m.index 9, t.data (m.index 8+j) = value j) ∧
      (∀ i, 27 ≤ i → (i < m.index 8 ∨ m.index 8+m.index 9 ≤ i) → t.data i = m.data i) ∧
      (∀ i, 6 ≤ i → i ≠ 10 → i ≠ 11 → i ≠ 12 → t.index i = m.index i) := by
  let I := Inv m value H C
  have sizeLE (j : ℕ) (hj : j ≤ m.index 9) : H+j*C ≤ H+m.index 9*C :=
    Nat.add_le_add_left (Nat.mul_le_mul_right C hj) H
  have widen (j : ℕ) (hj : j ≤ m.index 9) {b : Block} {s t : Memory ℚ} {k : ℕ}
      (e : Eval (Within (H+j*C)) b s k t) : Eval (Within (H+m.index 9*C)) b s k t :=
    PowerRAM.weaken e (fun _ h i => (h i).trans (sizeLE j hj))
  let s1 := m.putIndex 11 (m.index 7)
  let s2 := s1.putIndex 12 (m.index 8)
  have all0 : Within (H+m.index 9*C) m := fun i => (hs i).trans (Nat.le_add_right _ _)
  have e1 : Eval (Within (H+m.index 9*C)) (.op (.addrCopy 11 7)) m 1 s1 := Eval.op_addrCopy m 11 7 all0 all0
  have e2 : Eval (Within (H+m.index 9*C)) (.op (.addrCopy 12 8)) s1 1 s2 := by
    simpa [s1,s2] using Eval.op_addrCopy s1 12 8 all0 all0
  have init : I 0 (s2.putIndex 10 0) := by
    refine ⟨Nat.zero_le _,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [s2,s1,Within] using hs
    · simp
    · simp [s2,s1]
    · simp [s2]
    · intro u _ hu hv hw; simp [s2,s1,hu,hv,hw]
    · rfl
    · rfl
    · intro u _; simp [s2,s1]
  obtain ⟨t,k,hk,loop,ht⟩ := Eval.forRange_invariant
    (body := .seq loadCell (.seq cell (.straight [.store 12 26,.incr 12 12])))
    10 9 (m.index 9) (steps+8) I s2 all0 init
    (fun _ _ h => ⟨fun u => (h.bits u).trans (sizeLE _ h.limit),h.counter,
      h.addresses 9 (by decide) (by decide) (by decide) (by decide)⟩) (by
      intro j hj s h
      obtain ⟨u,load,h23,h24,h25,hu11,hui,hud⟩ := loadCell_spec m h hi hsep hj
      obtain ⟨v,k,hk,run,out,frame⟩ := kernel j hj u load.safe_end
        ((hui 6 (by decide)).trans (h.addresses 6 (by decide) (by decide) (by decide) (by decide)))
        ((hud 21 (by decide) (by decide) (by decide)).trans h.pivot)
        ((hud 22 (by decide) (by decide) (by decide)).trans h.winning) h23 h24 h25
      have vidx (r : ℕ) (hr : 6 ≤ r) (hne : r ≠ 11) : v.index r = s.index r :=
        (frame.index r hr).trans (hui r hne)
      have vdata (r : ℕ) (hr : r=21 ∨ r=22 ∨ 26<r) : v.data r = s.data r :=
        (frame.data r hr).trans (hud r (by omega) (by omega) (by omega))
      have ptrOut : v.index 12 = m.index 8+j := (vidx 12 (by decide) (by decide)).trans h.outputPtr
      let w := v.putData (m.index 8+j) (value j)
      let dst := w.putIndex 12 (m.index 8+(j+1))
      have hw : Within (H+(j+1)*C) w := write run.safe_end _ (out ▸ run.safe_end 26)
      have save : Eval (Within (H+(j+1)*C)) (.op (.store 12 26)) v 1 w := by
        simpa only [w,ptrOut,out] using Eval.op_store v 12 26 run.safe_end (by simpa [w,ptrOut,out] using hw)
      have inc : Eval (Within (H+(j+1)*C)) (.op (.incr 12 12)) w 1 dst := by
        simpa [w,dst,ptrOut,Nat.add_assoc] using Eval.op_incr w 12 12 hw hw
      have update := save.seq (inc.seq (Eval.skip hw))
      refine ⟨dst,6+(k+2),by omega,(widen j hj.le load).seq (widen (j+1) hj (run.seq update)),?_⟩
      refine ⟨hj,hw,?_,?_,?_,?_,?_,?_,?_⟩
      · simp [dst,w,vidx 10 (by decide) (by decide),h.counter]
      · simp [dst,w,frame.index 11 (by decide),hu11]
      · simp [dst]
      · intro r hr h10 h11 h12; simp [dst,w,h10,h12,vidx r hr h11,h.addresses r hr h10 h11 h12]
      · simp [dst,w,show 21 ≠ m.index 8+j by omega,vdata 21 (Or.inl rfl),h.pivot]
      · simp [dst,w,show 22 ≠ m.index 8+j by omega,vdata 22 (Or.inr (Or.inl rfl)),h.winning]
      · intro r hr
        by_cases eq : r = m.index 8+j
        · subst r; simp [dst,w]
        · have atOld : m.index 8 ≤ r ∧ r < m.index 8+(j+1) ↔ m.index 8 ≤ r ∧ r < m.index 8+j := by omega
          simp [dst,w,eq,vdata r (Or.inr (Or.inr (by omega))),h.cells _ hr,atOld])
  have first : Eval (Within (H+m.index 9*C)) (.straight [.addrCopy 11 7,.addrCopy 12 8]) m 2 s2 :=
    e1.seq (e2.seq (.skip all0))
  rw [show steps+8+3 = steps+11 by omega] at hk
  refine ⟨t,2+k,by omega,first.seq loop,?_,?_,ht.addresses⟩
  · intro j hj; simpa [hj] using ht.cells (m.index 8+j) (by omega)
  · intro r hr outside; simpa [show ¬(m.index 8 ≤ r ∧ r < m.index 8+m.index 9) by omega] using ht.cells r hr

end RowRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
