import OAI.Optimization.LinearProgramming.RAM.Array

/-! Stable positions of nonzero requests and the RAM instructions for compacting
their absolute values alongside the original request ordinals. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorProxyInputs
open RAM

/-- Number of nonzero input words strictly before the given ordinal. -/
def nonzeroRank {K : Type*} [Zero K] [DecidableEq K] (value : ℕ → K) : ℕ → ℕ
  | 0 => 0
  | j+1 => nonzeroRank value j + (if value j = 0 then 0 else 1)

section Rank
variable {K : Type*} [Zero K] [DecidableEq K] (value : ℕ → K)

theorem nonzeroRank_mono : Monotone (nonzeroRank value) := monotone_nat_of_le_succ fun _ => Nat.le_add_right _ _

theorem nonzeroRank_le (k : ℕ) : nonzeroRank value k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [nonzeroRank]; split <;> omega

theorem nonzeroRank_strict {i k : ℕ} (hi : i < k) (hn : value i ≠ 0) :
    nonzeroRank value i < nonzeroRank value k := by
  have h := nonzeroRank_mono value (show i+1 ≤ k from hi)
  have successor_le : nonzeroRank value i + 1 ≤ nonzeroRank value k := by
    simpa [nonzeroRank,hn] using h
  exact Nat.lt_of_succ_le successor_le

/-- Every position in the compacted stream corresponds to exactly one nonzero
source ordinal; in particular, repeated equal magnitudes retain distinct ordinals. -/
theorem nonzeroRank_lookup {q r : ℕ} (hr : r < nonzeroRank value q) :
    ∃! i : ℕ, i < q ∧ value i ≠ 0 ∧ nonzeroRank value i = r := by
  have existsOrdinal (n : ℕ) (h : r < nonzeroRank value n) :
      ∃ i, i < n ∧ value i ≠ 0 ∧ nonzeroRank value i = r := by
    induction n with
    | zero => exact (Nat.not_lt_zero _ h).elim
    | succ n ih =>
      by_cases hprev : r < nonzeroRank value n
      · obtain ⟨i,hi,hn,he⟩ := ih hprev
        exact ⟨i,by omega,hn,he⟩
      · by_cases hn : value n = 0
        · simp [nonzeroRank,hn] at h; omega
        · rw [nonzeroRank,ite_eq_right hn] at h
          exact ⟨n,by omega,hn,by omega⟩
  obtain ⟨i,hi,hv,hpos⟩ := existsOrdinal q hr
  refine ⟨i,⟨hi,hv,hpos⟩,?_⟩
  rintro j ⟨_,hj,he⟩
  rcases lt_trichotomy i j with h | h | h
  · have := nonzeroRank_strict value h hv; omega
  · exact h.symm
  · have := nonzeroRank_strict value h hj; omega

end Rank

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def readMagnitude : Block := .seq (.op (.load 0 5))
  (.branch (.scalarLT 0 1) (.op (.sub 0 1 0)) .skip)

/-- Scalar 1 holds zero. Reading and taking the magnitude changes only scalar 0. -/
theorem readMagnitude_eval (P : K → Prop) (s : Memory K) (hs : s.AllData P)
    (zero : s.data 1 = 0) (habs : P |s.data (s.index 5)|) :
    ∃ k ≤ 4, Block.Eval (Memory.AllData P) readMagnitude s k
      (s.putData 0 |s.data (s.index 5)|) := by
  let x := s.data (s.index 5)
  let t := s.putData 0 x
  have ht : t.AllData P := hs.putData 0 (hs _)
  have read : Block.Eval (Memory.AllData P) (.op (.load 0 5)) s 1 t := Block.Eval.op_load _ _ _ hs ht
  by_cases neg : x < 0
  · have guard : (Cond.scalarLT 0 1).test t = true := by simp [Cond.test,t,zero,neg]
    have eq : t.putData 0 (t.data 1 - t.data 0) = s.putData 0 |x| := by
      simp [t,Memory.putData,zero,abs_of_neg neg,Function.update_idem]
    have sub : Block.Eval (Memory.AllData P) (.op (.sub 0 1 0)) t 1 (s.putData 0 |x|) := by
      simpa only [eq] using Block.Eval.op_sub t 0 1 0 ht (by rw [eq]; exact hs.putData 0 habs)
    exact ⟨4,by decide,read.seq (.branchTrue guard sub)⟩
  · have guard : (Cond.scalarLT 0 1).test t = false := by simp [Cond.test,t,zero,neg]
    have h := read.seq (Block.Eval.branchFalse (a := .op (.sub 0 1 0)) guard (Block.Eval.skip ht))
    refine ⟨2,by decide,?_⟩
    change Block.Eval _ readMagnitude s 2 (s.putData 0 |x|)
    rw [abs_of_nonneg (le_of_not_gt neg)]
    exact h

def emitMagnitude : Block :=
  .seq (.op (.store 6 0)) (.seq (.op (.addrStore 8 4)) (.seq (.op (.incr 6 6))
    (.seq (.op (.incr 8 8)) (.op (.incr 7 7)))))

def emitted (s : Memory K) : Memory K :=
  let t := (s.putData (s.index 6) (s.data 0)).putIndex (s.index 8) (s.index 4)
  ((t.putIndex 6 (s.index 6+1)).putIndex 8 (s.index 8+1)).putIndex 7 (s.index 7+1)

theorem emitMagnitude_eval (P : K → Prop) (s : Memory K) (hs : s.AllData P) (high : 12 ≤ s.index 8) :
    Block.Eval (Memory.AllData P) emitMagnitude s 5 (emitted s) := by
  let u := s.putData (s.index 6) (s.data 0)
  let v := u.putIndex (s.index 8) (s.index 4)
  let w := v.putIndex 6 (s.index 6+1)
  let r := w.putIndex 8 (s.index 8+1)
  have hu : u.AllData P := hs.putData _ (hs 0)
  have e1 : Block.Eval (Memory.AllData P) (.op (.store 6 0)) s 1 u := Block.Eval.op_store _ _ _ hs hu
  have e2 : Block.Eval (Memory.AllData P) (.op (.addrStore 8 4)) u 1 v := Block.Eval.op_addrStore _ _ _ hu hu
  have h6 : v.index 6 = s.index 6 := by simp [v,u,show 6 ≠ s.index 8 by omega]
  have h8 : w.index 8 = s.index 8 := by simp [w,v,u,show 8 ≠ s.index 8 by omega]
  have h7 : r.index 7 = s.index 7 := by simp [r,w,v,u,show 7 ≠ s.index 8 by omega]
  exact e1.seq (e2.seq ((by simpa only [h6] using Block.Eval.op_incr (safe := Memory.AllData P) v 6 6 hu hu :
    Block.Eval (Memory.AllData P) (.op (.incr 6 6)) v 1 w).seq
    ((by simpa only [h8] using Block.Eval.op_incr (safe := Memory.AllData P) w 8 8 hu hu :
      Block.Eval (Memory.AllData P) (.op (.incr 8 8)) w 1 r).seq
      (by simpa only [h7] using Block.Eval.op_incr (safe := Memory.AllData P) r 7 7 hu hu))))

def advance (s : Memory K) : Memory K :=
  (s.putIndex 5 (s.index 5+1)).putIndex 4 (s.index 4+1)

def afterWord (s : Memory K) : Memory K :=
  let v := s.data (s.index 5)
  let t := s.putData 0 |v|
  advance (if v = 0 then t else emitted t)

def magnitudeBody : Block := .seq readMagnitude
  (.seq (.branch (.scalarLT 1 0) emitMagnitude .skip)
    (.seq (.op (.incr 5 5)) (.op (.incr 4 4))))

theorem magnitudeBody_eval (P : K → Prop) (s : Memory K) (hs : s.AllData P)
    (zero : s.data 1 = 0) (high : 12 ≤ s.index 8) (habs : P |s.data (s.index 5)|) :
    ∃ k ≤ 13, Block.Eval (Memory.AllData P) magnitudeBody s k (afterWord s) := by
  let x := s.data (s.index 5)
  let t := s.putData 0 |x|
  obtain ⟨k,hk,hread⟩ := readMagnitude_eval P s hs zero habs
  change Block.Eval _ _ s k t at hread
  let out := if x = 0 then t else emitted t
  have branch : ∃ l ≤ 7, Block.Eval (Memory.AllData P)
      (.branch (.scalarLT 1 0) emitMagnitude .skip) t l out := by
    by_cases hx : x = 0
    · have test : (Cond.scalarLT 1 0).test t = false := by simp [Cond.test,t,zero,hx]
      exact ⟨1,by decide,by simpa [out,hx] using Block.Eval.branchFalse (a := emitMagnitude) test (Block.Eval.skip hread.safe_end)⟩
    · have test : (Cond.scalarLT 1 0).test t = true := by simp [Cond.test,t,zero,abs_pos.mpr hx]
      exact ⟨7,by decide,by simpa [out,hx] using Block.Eval.branchTrue (b := .skip) test (emitMagnitude_eval P t hread.safe_end high)⟩
  obtain ⟨l,hl,ed⟩ := branch
  let mid := out.putIndex 5 (out.index 5+1)
  have e5 : Block.Eval (Memory.AllData P) (.op (.incr 5 5)) out 1 mid :=
    Block.Eval.op_incr _ _ _ ed.safe_end ed.safe_end
  have h4 : mid.index 4 = out.index 4 := by simp [mid]
  have e4 : Block.Eval (Memory.AllData P) (.op (.incr 4 4)) mid 1 (advance out) := by
    change Block.Eval _ _ mid 1 (mid.putIndex 4 (out.index 4+1))
    simpa only [h4] using Block.Eval.op_incr (safe := Memory.AllData P) mid 4 4 ed.safe_end ed.safe_end
  exact ⟨_,by omega,hread.seq (ed.seq (e5.seq e4))⟩

end MinorProxyInputs
end Compression
end LinearProgramming
end Optimization
end OAI
