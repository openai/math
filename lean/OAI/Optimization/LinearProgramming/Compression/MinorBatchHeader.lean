import OAI.Optimization.LinearProgramming.Compression.MinorLoadData
import OAI.Optimization.LinearProgramming.RAM.Loops

/-! Fixed-size loading of a minor-request descriptor from the address bank. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorLoad

open RAM

/-- Each request has six address words, in the same order as input registers 0 through 5. -/
def descriptorWord {K : Type*} (v : Layout K) : ℕ → ℕ
  | 0 => v.src
  | 1 => v.n
  | 2 => v.k
  | 3 => v.rowArray
  | 4 => v.colArray
  | _ => v.dst

/-- Read `count` words via pointer 17 and place them in consecutive direct address registers.
Only `loadDescriptor 6 0` is emitted by the batch program, independently of input size. -/
def loadDescriptor : ℕ → ℕ → Block
  | 0, _ => .skip
  | k+1, dst => .seq (.op (.addrLoad dst 17)) (.seq (.op (.incr 17 17)) (loadDescriptor k (dst+1)))

theorem loadDescriptor_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (count dst : ℕ) (hle : dst+count≤6) (m : Memory K)
    (hh : 20 ≤ m.index 17) (hm : ∀ a, P (m.data a)) :
    ∃ t, Block.Eval (fun z => ∀ a, P (z.data a)) (loadDescriptor count dst) m (2*count) t ∧
      t.data=m.data ∧ t.index 17=m.index 17+count ∧
      (∀ j<count, t.index (dst+j)=m.index (m.index 17+j)) ∧
      (∀ p, p≠17 → (p<dst ∨ dst+count≤p) → t.index p=m.index p) := by
  induction count generalizing dst m with
  | zero =>
    refine ⟨m, by simpa [loadDescriptor] using Block.Eval.skip (safe := fun z => ∀ a, P (z.data a)) hm,
      rfl, by simp, ?_, fun _ _ _ => rfl⟩
    omega
  | succ k ih =>
    let a := m.putIndex dst (m.index (m.index 17))
    let b := a.putIndex 17 (a.index 17+1)
    have hdst : dst ≠ 17 := by omega
    have head : b.index 17=m.index 17+1 := by simp [b,a,Memory.putIndex,Ne.symm hdst]
    have keep (p : ℕ) (h : p≠17) (h' : p≠dst) : b.index p=m.index p := by
      simp [b,a,Memory.putIndex,Function.update_of_ne h,Function.update_of_ne h']
    obtain ⟨t,hrun,hdata,hptr,hreads,hrest⟩ := ih (dst+1) (by omega) b (head ▸ by omega) hm
    have read : Block.Eval (fun z => ∀ x, P (z.data x)) (.op (.addrLoad dst 17)) m 1 a :=
      Block.Eval.op_addrLoad _ _ _ hm hm
    have bump : Block.Eval (fun z => ∀ x, P (z.data x)) (.op (.incr 17 17)) a 1 b :=
      Block.Eval.op_incr _ _ _ hm hm
    refine ⟨t, ?_, hdata, by rw [hptr,head]; omega, ?_, ?_⟩
    · rw [show 2*(k+1) = 1+(1+2*k) by omega]
      exact read.seq (bump.seq hrun)
    · intro j hj
      cases j with
      | zero =>
        simp only [Nat.add_zero]
        rw [hrest dst hdst (.inl (Nat.lt_succ_self _))]
        simp [b,a,Memory.putIndex,hdst]
      | succ j =>
        have hv := hreads j (by omega)
        rw [head, keep _ (by omega) (by omega)] at hv
        simpa only [show dst+1+j=dst+j.succ by omega, show m.index 17+1+j=m.index 17+j.succ by omega] using hv
    · intro p hp hrange
      exact (hrest p hp (by omega)).trans (keep p hp (by omega))

/-- Immutable runtime queue data. Descriptors and their selector arrays live at addresses ≥20.
Input matrices precede the answer tape, which precedes every minor workspace. -/
structure BatchLayout (K : Type) (q : ℕ) where
  query : Fin q → Layout K
  headerBase : ℕ
  answerBase : ℕ
  header_ge : 20 ≤ headerBase
  answer_ge : 7 ≤ answerBase
  row_ge : ∀ a, 20 ≤ (query a).rowArray
  col_ge : ∀ a, 20 ≤ (query a).colArray
  source_ge : ∀ a, 7 ≤ (query a).src
  source_end : ∀ a, (query a).src + (query a).m*(query a).n ≤ answerBase
  answers_end : ∀ a, answerBase+q ≤ (query a).dst

structure BatchInput {K : Type} {q : ℕ} (v : BatchLayout K q) (m : Memory K) : Prop where
  count : m.index 16=q
  header : m.index 17=v.headerBase
  answer : m.index 18=v.answerBase
  words : ∀ a : Fin q, ∀ j<6, m.index (v.headerBase+6*a.val+j)=descriptorWord (v.query a) j
  rows : ∀ (a : Fin q) (i : Fin (v.query a).k), m.index ((v.query a).rowArray+i.val)=((v.query a).row i).val
  cols : ∀ (a : Fin q) (i : Fin (v.query a).k), m.index ((v.query a).colArray+i.val)=((v.query a).col i).val
  source : ∀ (a : Fin q) i j, m.data ((v.query a).src+i.val*(v.query a).n+j.val)=(v.query a).matrix i j

end MinorLoad
end Compression
end LinearProgramming
end Optimization
end OAI
