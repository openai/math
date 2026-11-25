import OAI.Optimization.LinearProgramming.RAM.Loops
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
/-! Fixed RAM programs for contiguous dense scalar arrays. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM

open scoped BigOperators

/-- The scalar-memory invariant used while assembling numerical subroutines. -/
def Memory.AllData {K : Type*} (P : K → Prop) (m : Memory K) : Prop := ∀ j, P (m.data j)

theorem Memory.AllData.putData {K : Type*} {P : K → Prop} {m : Memory K}
    (hm : m.AllData P) (j : ℕ) {x : K} (hx : P x) : (m.putData j x).AllData P := by
  intro k
  by_cases h : k=j
  · simpa [Memory.putData,h] using hx
  · simpa [Memory.putData,Function.update_of_ne h] using hm k

theorem Memory.AllData.putIndex {K : Type*} {P : K → Prop} {m : Memory K}
    (hm : m.AllData P) (j v : ℕ) : (m.putIndex j v).AllData P := hm

namespace Dense

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A scan advances both non-aliasing input pointers and the loop index on every step.
Scalar registers 20–23 are temporary. The two array ranges may overlap each other. -/
def dotBody : Block := Block.straight
  [.load 21 20, .load 22 21, .mul 23 21 22, .add 20 20 23,
   .incr 20 20, .incr 21 21, .incr 22 22]

/-- Entry protocol: address registers 20 and 21 point at the first elements of the
two arrays and 23 gives their common length. Scalar register 20 receives the result. -/
def dotBlock : Block :=
  .seq (.op (.const 20 0)) (.seq (.op (.addrConst 22 0)) (.loop (.addrLT 22 23) dotBody))

def dotTerm (m : Memory K) (j : ℕ) : K :=
  m.data (m.index 20 + j) * m.data (m.index 21 + j)

def dotPrefix (m : Memory K) (p : ℕ) : K := ∑ j ∈ Finset.range p, dotTerm m j

/-- Complete visible effects of processing a prefix of the arrays. -/
structure DotAt (m : Memory K) (p : ℕ) (s : Memory K) : Prop where
  sum : s.data 20 = dotPrefix m p
  left : s.index 20 = m.index 20 + p
  right : s.index 21 = m.index 21 + p
  cursor : s.index 22 = p
  dataFrame : ∀ j, j < 20 ∨ 23 < j → s.data j = m.data j
  indexFrame : ∀ j, j < 20 ∨ 22 < j → s.index j = m.index j

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem dot_start (m : Memory K) :
    DotAt m 0 ((m.putData 20 0).putIndex 22 0) := by
  constructor
  · simp [Memory.putData, Memory.putIndex, dotPrefix]
  · simp [Memory.putData, Memory.putIndex]
  · simp [Memory.putData, Memory.putIndex]
  · simp [Memory.putData, Memory.putIndex]
  · intro j hj
    simp [Memory.putData, Memory.putIndex, Function.update_of_ne (by omega : j ≠ 20)]
  · intro j hj
    simp [Memory.putData, Memory.putIndex, Function.update_of_ne (by omega : j ≠ 22)]

private theorem dot_step {P : K → Prop} {m s : Memory K} {j : ℕ} (h : DotAt m j s)
    (hs : s.AllData P) (hl : 23 < m.index 20) (hr : 23 < m.index 21)
    (ht : P (dotTerm m j)) (ha : P (dotPrefix m (j+1))) :
    ∃ t, Block.Eval (Memory.AllData P) dotBody s 7 t ∧ DotAt m (j+1) t := by
  let a := s.data (s.index 20)
  let b := s.data (s.index 21)
  have hL : 23 < s.index 20 := by rw [h.left]; omega
  have hR : 23 < s.index 21 := by rw [h.right]; omega
  have hab : a*b = dotTerm m j := by
    dsimp [a,b,dotTerm]
    rw [h.dataFrame _ (Or.inr hL), h.dataFrame _ (Or.inr hR), h.left, h.right]
  have hadd : s.data 20 + a*b = dotPrefix m (j+1) := by
    rw [h.sum, hab, dotPrefix, dotPrefix, Finset.sum_range_succ]
  let s1 := s.putData 21 a
  let s2 := s1.putData 22 b
  let s3 := s2.putData 23 (a*b)
  let s4 := s3.putData 20 (s.data 20 + a*b)
  let s5 := s4.putIndex 20 (s.index 20+1)
  let s6 := s5.putIndex 21 (s.index 21+1)
  let t := s6.putIndex 22 (s.index 22+1)
  have h1 : s1.AllData P := hs.putData 21 (hs _)
  have h2 : s2.AllData P := h1.putData 22 (hs _)
  have h3 : s3.AllData P := h2.putData 23 (by rwa [hab])
  have h4 : s4.AllData P := h3.putData 20 (by rwa [hadd])
  have h5 : s5.AllData P := h4
  have h6 : s6.AllData P := h5
  have h7 : t.AllData P := h6
  have e1 : Block.Eval (Memory.AllData P) (.op (.load 21 20)) s 1 s1 :=
    Block.Eval.op_load _ _ _ hs h1
  have e2 : Block.Eval (Memory.AllData P) (.op (.load 22 21)) s1 1 s2 := by
    have heq : s1.data (s1.index 21) = b := by
      simp [s1, b, Memory.putData, Function.update_of_ne (by omega : s.index 21 ≠ 21)]
    simpa only [heq] using Block.Eval.op_load s1 22 21 h1 (by simpa only [heq] using h2)
  have e3 : Block.Eval (Memory.AllData P) (.op (.mul 23 21 22)) s2 1 s3 := by
    have eq : s2.data 21 * s2.data 22 = a*b := by simp [s2,s1,Memory.putData]
    simpa only [eq] using Block.Eval.op_mul s2 23 21 22 h2 (by simpa only [eq] using h3)
  have e4 : Block.Eval (Memory.AllData P) (.op (.add 20 20 23)) s3 1 s4 := by
    have eq : s3.data 20 + s3.data 23 = s.data 20 + a*b := by simp [s3,s2,s1,Memory.putData]
    simpa only [eq] using Block.Eval.op_add s3 20 20 23 h3 (by simpa only [eq] using h4)
  have e5 : Block.Eval (Memory.AllData P) (.op (.incr 20 20)) s4 1 s5 :=
    Block.Eval.op_incr _ _ _ h4 h5
  have e6 : Block.Eval (Memory.AllData P) (.op (.incr 21 21)) s5 1 s6 := by
    have eq : s5.index 21 = s.index 21 := by simp [s5,s4,s3,s2,s1,Memory.putIndex,Memory.putData]
    simpa only [eq] using Block.Eval.op_incr s5 21 21 h5 (by simpa only [eq] using h6)
  have e7 : Block.Eval (Memory.AllData P) (.op (.incr 22 22)) s6 1 t := by
    have eq : s6.index 22 = s.index 22 := by simp [s6,s5,s4,s3,s2,s1,Memory.putIndex,Memory.putData]
    simpa only [eq] using Block.Eval.op_incr s6 22 22 h6 (by simpa only [eq] using h7)
  refine ⟨t, .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 (.seq e7 (.skip h7))))))), ?_⟩
  constructor
  · simpa [t,s6,s5,s4,Memory.putIndex,Memory.putData] using hadd
  · simp [t,s6,s5,Memory.putIndex,h.left,Nat.add_assoc]
  · simp [t,s6,s5,Memory.putIndex,h.right,Nat.add_assoc]
  · simp [t,Memory.putIndex,h.cursor]
  · intro k hk
    have h20 : k ≠ 20 := by omega
    have h21 : k ≠ 21 := by omega
    have h22 : k ≠ 22 := by omega
    have h23 : k ≠ 23 := by omega
    simpa [t,s6,s5,s4,s3,s2,s1,Memory.putIndex,Memory.putData,Function.update_of_ne,
      h20,h21,h22,h23] using h.dataFrame k hk
  · intro k hk
    have h20 : k ≠ 20 := by omega
    have h21 : k ≠ 21 := by omega
    have h22 : k ≠ 22 := by omega
    simpa [t,s6,s5,s4,s3,s2,s1,Memory.putIndex,Memory.putData,Function.update_of_ne,
      h20,h21,h22] using h.indexFrame k hk

/-- Exact instructions, working scalar invariant and frame of the fixed dot-product program.
To obtain a bit bound it suffices to check each product and partial sum of the original inputs. -/
theorem dotBlock_correct (P : K → Prop) (m : Memory K) (n : ℕ)
    (hm : m.AllData P) (hl : 23 < m.index 20) (hr : 23 < m.index 21) (hn : m.index 23=n)
    (hterm : ∀ j<n, P (dotTerm m j)) (hsums : ∀ j≤n, P (dotPrefix m j)) :
    ∃ t, Block.Eval (Memory.AllData P) dotBlock m (9*n+3) t ∧ DotAt m n t := by
  let m1 := m.putData 20 0
  let m2 := m1.putIndex 22 0
  have h₀ : P 0 := by simpa [dotPrefix] using hsums 0 (Nat.zero_le _)
  have h1 : m1.AllData P := hm.putData _ h₀
  have h2 : m2.AllData P := h1
  obtain ⟨t, et, ht⟩ := Block.Eval.loop_invariant_exact
    (c := .addrLT 22 23) (body := dotBody) (safe := Memory.AllData P)
    (fun j s => s.AllData P ∧ DotAt m j s) m2 n 7 ⟨h2,dot_start m⟩
    (fun j hj s ⟨hs,h⟩ => by
      obtain ⟨z,ez,hz⟩ := dot_step h hs hl hr (hterm j hj) (hsums (j+1) hj)
      exact ⟨by simpa [Cond.test,h.cursor,h.indexFrame 23 (by omega),hn] using hj,
        z,ez,ez.safe_end,hz⟩)
    (fun s ⟨hs,h⟩ => ⟨by simp [Cond.test,h.cursor,h.indexFrame 23 (by omega),hn],hs⟩)
  refine ⟨t, ?_, ht.2⟩
  have e0 : Block.Eval (Memory.AllData P) (.op (.const 20 0)) m 1 m1 := by
    simpa using Block.Eval.op_const m 20 0 hm (by simpa using h1)
  have einit := e0.seq ((Block.Eval.op_addrConst m1 22 0 h1 h2).seq et)
  rw [show 9*n+3 = 1+(1+(n*(7+2)+1)) by ring]
  exact einit

end Dense
end RAM
end LinearProgramming
end Optimization
end OAI
