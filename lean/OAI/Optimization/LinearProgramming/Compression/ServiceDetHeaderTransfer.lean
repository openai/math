import OAI.Optimization.LinearProgramming.Compression.ServiceAddressPlan
import OAI.Optimization.LinearProgramming.RAM.StrideCopy

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

private def headerPointers (save : Bool) : List AddressSet := if save then
  [.fix 8 1,.read 9 30,.fix 11 4] else [.read 8 30,.fix 9 1,.fix 11 4]

/-- Save or restore the four persistent service scalars around the native determinant kernel. -/
def moveHeader (save : Bool) : Block := .seq (addressPlan (headerPointers save))
  (StrideCopy.block false 8 9 10 11 0 1 1)

theorem moveHeader_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (save : Bool) (P : K → Prop) (s : Memory K) (base : ℕ)
    (hb : 7 ≤ base) (h30 : s.index 30 = base) (hs : s.AllData P) :
    let src := if save then 1 else base
    let dst := if save then base else 1
    ∃t,Block.Eval (Memory.AllData P) (moveHeader save) s 33 t ∧
      (∀ j < 4,t.data (dst+j) = s.data (src+j)) ∧
      (∀ b,b ≠ 0 → (b < dst ∨ dst+4 ≤ b) → t.data b = s.data b) ∧
      ∀ j,j < 8 ∨ 12 ≤ j → t.index j = s.index j := by
  let src := if save then 1 else base
  let dst := if save then base else 1
  let a := applyPlan (headerPointers save) s
  have ha : Block.Eval (Memory.AllData P) (addressPlan (headerPointers save)) s 3 a := by
    cases save <;> exact addressPlan_spec (fun f => ∀ j,P (f j)) _ _ hs
  have h8 : a.index 8 = src := by cases save <;> simp [a,src,headerPointers,applyPlan,AddressSet.apply,h30]
  have h9 : a.index 9 = dst := by cases save <;> simp [a,dst,headerPointers,applyPlan,AddressSet.apply,h30]
  have h11 : a.index 11 = 4 := by cases save <;> simp [a,headerPointers,applyPlan,AddressSet.apply]
  have hsrc : 0 < src := by
    cases save <;> simp [src]
    omega
  have hdst : 0 < dst := by
    cases save <;> simp [dst]
    omega
  have sep : src+4 ≤ dst ∨ dst+4 ≤ src := by cases save <;> simp [src,dst] <;> omega
  obtain ⟨t,et,cp,fr,_,_,_,ix⟩ := StrideCopy.block_correct P a false 8 9 10 11 0 1 1 4 ha.safe_end h11
    (by decide) (by decide) (by simp)
    (by intro j _; simp [StrideCopy.address,StrideCopy.move,h8]; omega)
    (by intro j _; simp [StrideCopy.address,StrideCopy.move,h9]; omega)
    (by intro i j hi hj; simp [StrideCopy.address,StrideCopy.move,h8,h9]; omega)
  refine ⟨t,ha.seq et,?_,?_,?_⟩
  · intro j hj
    simpa [StrideCopy.address,StrideCopy.move,h8,h9,a] using cp j hj
  · intro b h0 outside
    have f := fr b h0 (by intro j hj; simp [StrideCopy.address,StrideCopy.move,h9]; omega)
    simpa [a] using f
  · intro j hj
    have h := ix j (by omega) (by omega) (by omega)
    cases save <;> simpa [a,headerPointers,applyPlan,AddressSet.apply,show j ≠ 8 by omega,show j ≠ 9 by omega,show j ≠ 11 by omega] using h


end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
