import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.Lattice.Bisection

/-! Materializing one dyadic sign query in three contiguous scalar arrays. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace DyadicRAM

open RAM OAI.Optimization.LinearProgramming.Lattice

/-- Source/destination cursors occupy address registers 14, 15 and 16. -/
private def queryCell : Block := .straight [
  .load 3 14, .mul 3 3 1, .load 4 15, .mul 4 4 0,
  .sub 5 3 4, .store 16 5, .incr 14 14, .incr 15 15, .incr 16 16]

/-- The base pointers are supplied in address registers 10, 11 and 12;
register 13 holds the common length. Scalar registers 0 and 1 hold the
current numerator and its power-of-two denominator. -/
def queryArrayBlock : Block :=
  .seq (.straight [.addrCopy 14 10, .addrCopy 15 11, .addrCopy 16 12])
    (.forRange 17 13 queryCell)

private theorem queryCell_eval (s : Memory ℚ) (P : ℚ → Prop) (hs : s.AllData P)
    (hr : 5 < s.index 15) (hd : 5 < s.index 16)
    (A B : ℚ) (ha : A = s.data (s.index 14) * s.data 1)
    (hb : B = s.data (s.index 15) * s.data 0) (hA : P A) (hB : P B) (hC : P (A-B)) :
    ∃ t, Block.Eval (Memory.AllData P) queryCell s 9 t ∧ t.data (s.index 16) = A-B ∧
      (∀ r, (r < 3 ∨ 5 < r) → r ≠ s.index 16 → t.data r = s.data r) ∧
      t.index 14 = s.index 14+1 ∧ t.index 15 = s.index 15+1 ∧ t.index 16 = s.index 16+1 ∧
      (∀ r, r < 14 ∨ 16 < r → t.index r = s.index r) := by
  let s₁ := s.putData 3 (s.data (s.index 14))
  let s₂ := s₁.putData 3 A
  let s₃ := s₂.putData 4 (s.data (s.index 15))
  let s₄ := s₃.putData 4 B
  let s₅ := s₄.putData 5 (A-B)
  let s₆ := s₅.putData (s.index 16) (A-B)
  let s₇ := s₆.putIndex 14 (s.index 14+1)
  let s₈ := s₇.putIndex 15 (s.index 15+1)
  let t := s₈.putIndex 16 (s.index 16+1)
  have h₁ : s₁.AllData P := hs.putData _ (hs _)
  have h₂ : s₂.AllData P := h₁.putData _ hA
  have h₃ : s₃.AllData P := h₂.putData _ (hs _)
  have h₄ : s₄.AllData P := h₃.putData _ hB
  have h₅ : s₅.AllData P := h₄.putData _ hC
  have h₆ : s₆.AllData P := h₅.putData _ hC
  have h₇ : s₇.AllData P := h₆
  have h₈ : s₈.AllData P := h₇
  have h₉ : t.AllData P := h₈
  have e₁ : Block.Eval (Memory.AllData P) (.op (.load 3 14)) s 1 s₁ :=
    Block.Eval.op_load _ _ _ hs h₁
  have e₂ : Block.Eval (Memory.AllData P) (.op (.mul 3 3 1)) s₁ 1 s₂ := by
    have v : s₁.data 3 * s₁.data 1 = A := by simpa [s₁] using ha.symm
    simpa only [v] using Block.Eval.op_mul s₁ 3 3 1 h₁ (by simpa only [v] using h₂)
  have e₃ : Block.Eval (Memory.AllData P) (.op (.load 4 15)) s₂ 1 s₃ := by
    have v : s₂.data (s₂.index 15) = s.data (s.index 15) := by
      simp [s₂,s₁, show s.index 15 ≠ 3 by omega]
    simpa only [v] using Block.Eval.op_load s₂ 4 15 h₂ (by simpa only [v] using h₃)
  have e₄ : Block.Eval (Memory.AllData P) (.op (.mul 4 4 0)) s₃ 1 s₄ := by
    have v : s₃.data 4 * s₃.data 0 = B := by simpa [s₃,s₂,s₁] using hb.symm
    simpa only [v] using Block.Eval.op_mul s₃ 4 4 0 h₃ (by simpa only [v] using h₄)
  have e₅ : Block.Eval (Memory.AllData P) (.op (.sub 5 3 4)) s₄ 1 s₅ := by
    have v : s₄.data 3 - s₄.data 4 = A-B := by simp [s₄,s₃,s₂]
    simpa only [v] using Block.Eval.op_sub s₄ 5 3 4 h₄ (by simpa only [v] using h₅)
  have e₆ : Block.Eval (Memory.AllData P) (.op (.store 16 5)) s₅ 1 s₆ := by
    have v : s₅.data 5 = A-B := by simp [s₅]
    have ptr : s₅.index 16 = s.index 16 := rfl
    simpa only [v,ptr] using Block.Eval.op_store s₅ 16 5 h₅ (by simpa only [v,ptr] using h₆)
  have e₇ : Block.Eval (Memory.AllData P) (.op (.incr 14 14)) s₆ 1 s₇ :=
    Block.Eval.op_incr _ _ _ h₆ h₇
  have e₈ : Block.Eval (Memory.AllData P) (.op (.incr 15 15)) s₇ 1 s₈ := by
    have v : s₇.index 15 = s.index 15 := by simp [s₇,s₆,s₅,s₄,s₃,s₂,s₁]
    simpa only [v] using Block.Eval.op_incr s₇ 15 15 h₇ (by simpa only [v] using h₈)
  have e₉ : Block.Eval (Memory.AllData P) (.op (.incr 16 16)) s₈ 1 t := by
    have v : s₈.index 16 = s.index 16 := by simp [s₈,s₇,s₆,s₅,s₄,s₃,s₂,s₁]
    simpa only [v] using Block.Eval.op_incr s₈ 16 16 h₈ (by simpa only [v] using h₉)
  refine ⟨t, e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq (e₆.seq (e₇.seq (e₈.seq (e₉.seq (.skip h₉))))))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t,s₈,s₇,s₆]
  · intro r hs' hdst
    have h3 : r ≠ 3 := by omega
    have h4 : r ≠ 4 := by omega
    have h5 : r ≠ 5 := by omega
    simp [t,s₈,s₇,s₆,s₅,s₄,s₃,s₂,s₁,hdst,h3,h4,h5]
  · simp [t,s₈,s₇]
  · simp [t,s₈]
  · simp [t]
  · intro r h
    have h14 : r ≠ 14 := by omega
    have h15 : r ≠ 15 := by omega
    have h16 : r ≠ 16 := by omega
    simp [t,s₈,s₇,s₆,s₅,s₄,s₃,s₂,s₁,h14,h15,h16]

/-- Data modified by the block outside its scratch registers are precisely the
already visited cells of the output array. -/
structure QueryPrefix {p : ℕ} (a b : Fin p → ℤ) (j : ℕ) (numer : ℤ)
    (orig : Memory ℚ) (left right out n : ℕ) (m : Memory ℚ) : Prop where
  cursor : m.index 17 = n
  leftPtr : m.index 14 = left+n
  rightPtr : m.index 15 = right+n
  outPtr : m.index 16 = out+n
  result : ∀ i : Fin p, i.val < n → m.data (out+i.val) = (dyadicQuery a b j numer i : ℚ)
  dataFrame : ∀ r, (r < 3 ∨ 5 < r) → (r < out ∨ out+n ≤ r) → m.data r = orig.data r
  indexFrame : ∀ r, r < 14 ∨ 17 < r → m.index r = orig.index r

/-- With ordered, disjoint input and output buffers, fill every integer coefficient in
linear many RAM instructions. All scalar transformations are checked against P. -/
theorem queryArrayBlock_spec {p : ℕ} (a b : Fin p → ℤ) (j : ℕ) (numer : ℤ) (P : ℚ → Prop)
    (m : Memory ℚ) (hm : m.AllData P) (left right out : ℕ)
    (hL : 5 < left) (hLR : left+p ≤ right) (hRO : right+p ≤ out)
    (hpL : m.index 10 = left) (hpR : m.index 11 = right) (hpO : m.index 12 = out)
    (hp : m.index 13 = p) (hn : m.data 0 = (numer : ℚ)) (hs : m.data 1 = ((2:ℤ)^j : ℚ))
    (ha : ∀ i : Fin p, m.data (left+i.val) = (a i : ℚ))
    (hb : ∀ i : Fin p, m.data (right+i.val) = (b i : ℚ))
    (hA : ∀ i, P (((2:ℤ)^j * a i : ℤ) : ℚ)) (hB : ∀ i, P ((numer * b i : ℤ) : ℚ))
    (hC : ∀ i, P (dyadicQuery a b j numer i : ℚ)) :
    ∃ t, Block.Eval (Memory.AllData P) queryArrayBlock m (12*p+5) t ∧
      QueryPrefix a b j numer m left right out p t := by
  let s₁ := m.putIndex 14 left
  let s₂ := s₁.putIndex 15 right
  let s₃ := s₂.putIndex 16 out
  have h₁ : s₁.AllData P := hm
  have h₂ : s₂.AllData P := hm
  have h₃ : s₃.AllData P := hm
  let I (n : ℕ) (s : Memory ℚ) := s.AllData P ∧ QueryPrefix a b j numer m left right out n s
  have hi : I 0 (s₃.putIndex 17 0) := by
    refine ⟨hm, ?_⟩
    constructor
    · simp
    · simp [s₃,s₂,s₁]
    · simp [s₃,s₂]
    · simp [s₃]
    · intro i h; omega
    · intro r _ _; rfl
    · intro r h
      have h14 : r ≠ 14 := by omega
      have h15 : r ≠ 15 := by omega
      have h16 : r ≠ 16 := by omega
      have h17 : r ≠ 17 := by omega
      simp [s₁,s₂,s₃,h14,h15,h16,h17]
  obtain ⟨t,loop,_,hfinal⟩ := Block.Eval.forRange_invariant_exact
    (safe := Memory.AllData P) (body := queryCell) 17 13 p 9 I s₃ h₃ hi
    (fun _ _ h => ⟨h.1,h.2.cursor,(h.2.indexFrame 13 (by omega)).trans hp⟩) (fun n hl s h => by
      let i : Fin p := ⟨n,hl⟩
      obtain ⟨hsafe,hprefix⟩ := h
      have hleft : s.data (s.index 14) = (a i : ℚ) := by
        rw [hprefix.leftPtr,hprefix.dataFrame _ (by omega) (by omega)]
        exact ha i
      have hright : s.data (s.index 15) = (b i : ℚ) := by
        rw [hprefix.rightPtr,hprefix.dataFrame _ (by omega) (by omega)]
        exact hb i
      have hnum := (hprefix.dataFrame 0 (by omega) (by omega)).trans hn
      have hscale := (hprefix.dataFrame 1 (by omega) (by omega)).trans hs
      obtain ⟨z,ez,hval,hdf,hleftPtr,hrightPtr,houtPtr,hif⟩ := queryCell_eval s P hsafe
        (by rw [hprefix.rightPtr]; omega) (by rw [hprefix.outPtr]; omega)
        (((2:ℤ)^j * a i : ℤ) : ℚ) ((numer * b i : ℤ) : ℚ)
        (by rw [hleft,hscale]; push_cast; ring)
        (by rw [hright,hnum]; push_cast; ring) (hA i) (hB i)
        (by simpa [dyadicQuery] using hC i)
      refine ⟨z, ez, ez.safe_end, ?_⟩
      constructor
      · simp [hif 17 (by omega),hprefix.cursor]
      · simp [hleftPtr,hprefix.leftPtr,Nat.add_assoc]
      · simp [hrightPtr,hprefix.rightPtr,Nat.add_assoc]
      · simp [houtPtr,hprefix.outPtr,Nat.add_assoc]
      · intro q hq
        change z.data (out+q.val) = _
        by_cases heq : q.val = n
        · have he : q = i := Fin.ext heq
          subst q
          simpa [hprefix.outPtr, i, dyadicQuery] using hval
        · calc
            _ = s.data (out+q.val) := hdf _ (by omega) (by rw [hprefix.outPtr]; omega)
            _ = _ := hprefix.result q (by omega)
      · intro r htemp hreg
        change z.data r = _
        exact (hdf r htemp (by rw [hprefix.outPtr]; omega)).trans (hprefix.dataFrame r htemp (by omega))
      · intro r hreg
        have hne : r ≠ 17 := by omega
        simpa [hne] using (hif r (by omega)).trans (hprefix.indexFrame r hreg))
  have e₁ : Block.Eval (Memory.AllData P) (.op (.addrCopy 14 10)) m 1 s₁ := by
    simpa only [hpL] using Block.Eval.op_addrCopy m 14 10 hm (by simpa only [hpL] using h₁)
  have e₂ : Block.Eval (Memory.AllData P) (.op (.addrCopy 15 11)) s₁ 1 s₂ := by
    have h : s₁.index 11 = right := by simpa [s₁] using hpR
    simpa only [h] using Block.Eval.op_addrCopy s₁ 15 11 h₁ (by simpa only [h] using h₂)
  have e₃ : Block.Eval (Memory.AllData P) (.op (.addrCopy 16 12)) s₂ 1 s₃ := by
    have h : s₂.index 12 = out := by simpa [s₂,s₁] using hpO
    simpa only [h] using Block.Eval.op_addrCopy s₂ 16 12 h₂ (by simpa only [h] using h₃)
  have ev := (e₁.seq (e₂.seq (e₃.seq (.skip h₃)))).seq loop
  refine ⟨t, ?_, hfinal⟩
  change Block.Eval (Memory.AllData P)
    (.seq (.straight [.addrCopy 14 10,.addrCopy 15 11,.addrCopy 16 12])
      (.forRange 17 13 queryCell)) m _ t
  rw [show 12*p+5 = (1+(1+(1+0))) + (p*(9+3)+2) by ring]
  exact ev

end DyadicRAM
end Compression
end LinearProgramming
end Optimization
end OAI
