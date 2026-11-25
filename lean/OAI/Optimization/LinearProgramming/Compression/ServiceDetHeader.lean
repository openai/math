import OAI.Optimization.LinearProgramming.Compression.ServiceDetHeaderTransfer

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Read scalar 6 and write its absolute value to 5 while preserving the non-scratch scalars. -/
def storeMagnitude : Block := .seq (.op (.const 0 0))
  (.branch (.scalarLT 6 0) (.op (.sub 5 0 6)) (.op (.copy 5 6)))

theorem storeMagnitude_spec (P : K→Prop) (s : Memory K) (hs : s.AllData P)
    (hz : P 0) (neg : ∀ x,P x → P (-x)) :
    ∃t l,l ≤ 4 ∧ Block.Eval (Memory.AllData P) storeMagnitude s l t ∧ t.data 5=|s.data 6| ∧
      t.index = s.index ∧ ∀ j,j ≠ 0 → j ≠ 5 → t.data j = s.data j := by
  let a := s.putData 0 ((0:ℚ):K)
  have sa : a.AllData P := by
    intro j
    by_cases h : j = 0
    · simpa [a,h] using hz
    · simpa [a,h] using hs j
  have ea : Block.Eval (Memory.AllData P) (.op (.const 0 0)) s 1 a := Block.Eval.op_const _ _ _ hs sa
  by_cases h : s.data 6 < 0
  · let t := a.putData 5 (a.data 0-a.data 6)
    have st : t.AllData P := by
      intro j
      by_cases he : j = 5
      · simpa [t,a,he] using neg (s.data 6) (hs 6)
      · simpa [t,he] using sa j
    have et : Block.Eval (Memory.AllData P) (.op (.sub 5 0 6)) a 1 t := Block.Eval.op_sub _ _ _ _ sa st
    exact ⟨t,4,by decide,ea.seq (.branchTrue (by simp [Cond.test,a,h]) et),
      by simp [t,a,abs_of_neg h],rfl,fun j h0 h5 => by simp [t,a,h0,h5]⟩
  · let t := a.putData 5 (a.data 6)
    have st : t.AllData P := by
      intro j
      by_cases he : j = 5
      · simpa [t,a,he] using hs 6
      · simpa [t,he] using sa j
    have et : Block.Eval (Memory.AllData P) (.op (.copy 5 6)) a 1 t := Block.Eval.op_copy _ _ _ sa st
    exact ⟨t,3,by decide,ea.seq (.branchFalse (by simp [Cond.test,a,h]) et),
      by simp [t,a,abs_of_nonneg (le_of_not_gt h)],rfl,fun j h0 h5 => by simp [t,a,h0,h5]⟩

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
