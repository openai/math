import OAI.Optimization.LinearProgramming.RAM.CallableOddBase
import OAI.Optimization.LinearProgramming.RAM.CallableScopedRun

/-! Install a finite inner register bank underneath the outer bit-machine frame. Only
callee addresses are trimmed; all scalar values and the caller's odd cells are retained. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NormalSubspace

variable {K : Type*}

open RAM RAM.Callable

theorem innerTrim_data (inner vm : Memory K) (cap : Nat) :
    (Odd.memory (trimMemory cap inner) vm).data=(Odd.memory inner vm).data := rfl

theorem innerTrim_index (inner vm : Memory K) (cap j : Nat) (hj : j ≤ cap) :
    (Odd.memory (trimMemory cap inner) vm).index j=(Odd.memory inner vm).index j := by
  simp only [Odd.memory,Call.pack,trimMemory,ite_eq_left (show j/2 ≤ cap by omega)]

private theorem memory_eq {a b : Memory K} (hd : a.data=b.data) (hi : a.index=b.index) : a=b := by
  cases a; cases b; simp_all

theorem innerTrim_window (inner vm : Memory K) (cap : Nat) :
    windowMemory cap (Odd.memory (trimMemory cap inner) vm) (Odd.memory inner vm) =
      Odd.memory (trimMemory cap inner) vm := by
  apply memory_eq
  · funext j
    by_cases hj : j ≤ cap
    · exact (ite_eq_left hj).trans rfl
    · exact ite_eq_right hj
  · funext j
    by_cases hj : j ≤ cap
    · exact (ite_eq_left hj).trans (innerTrim_index inner vm cap j hj).symm
    · exact ite_eq_right hj

theorem guard_of_low {K : Type*} [LT K] [DecidableLT K] (c : Cond) (a b : Memory K) {cap : Nat}
    (localGuard : c.accessBudget ≤ cap)
    (low : ∀ j, j ≤ cap → a.data j=b.data j ∧ a.index j=b.index j) : c.test a=c.test b := by
  cases c with
  | scalarLT x y =>
    change x+y ≤ cap at localGuard
    simp only [Cond.test,(low x (by omega)).1,(low y (by omega)).1]
  | addrLT x y =>
    change x+y ≤ cap at localGuard
    simp only [Cond.test,(low x (by omega)).2,(low y (by omega)).2]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The actual physical output agrees with the ideal run on all observable low cells.
The high part equals the concrete starting heap, and the scalar invariant holds globally. -/
theorem innerTrim_run_framed {f : Fragment} {P : K → Prop} {inner vm out : Memory K} {T b cap : Nat}
    (run : f.Run P (Odd.memory inner vm) T out) (scope : f.Scoped b)
    (indexBound : ∀ j,(Odd.memory inner vm).index j ≤ b) (room : b+T ≤ cap) :
    ∃ t, f.Run P (Odd.memory (trimMemory cap inner) vm) T t ∧
      (∀ j, j ≤ cap → t.data j=out.data j ∧ t.index j=out.index j) ∧
      (∀ j, cap<j → t.data j=(Odd.memory inner vm).data j ∧ t.index j=(Odd.memory (trimMemory cap inner) vm).index j) ∧
      ∀ j, P (t.data j) := by
  let actual := Odd.memory (trimMemory cap inner) vm
  have tailSafe (j : Nat) (_ : cap<j) : P (actual.data j) := run.safe_start j
  have checked := run.run_window scope indexBound room actual tailSafe
  have startEq : windowMemory cap actual (Odd.memory inner vm)=actual := innerTrim_window inner vm cap
  rw [startEq] at checked
  refine ⟨windowMemory cap actual out,checked,?_,?_,checked.safe_end⟩
  · intro j hj; exact ⟨ite_eq_left hj,ite_eq_left hj⟩
  · intro j hj; exact ⟨ite_eq_right (by omega),ite_eq_right (by omega)⟩

theorem innerTrim_run {f : Fragment} {P : K → Prop} {inner vm out : Memory K} {T b cap : Nat}
    (run : f.Run P (Odd.memory inner vm) T out) (scope : f.Scoped b)
    (indexBound : ∀ j,(Odd.memory inner vm).index j ≤ b) (room : b+T ≤ cap) :
    ∃ t, f.Run P (Odd.memory (trimMemory cap inner) vm) T t ∧
      ∀ j, j ≤ cap → t.data j=out.data j ∧ t.index j=out.index j := by
  obtain ⟨t,h,lo,_,_⟩ := innerTrim_run_framed run scope indexBound room
  exact ⟨t,h,lo⟩

theorem innerTrim_fixed_run {f : Fragment} [Fragment.FixedAccess f] {P : K → Prop}
    {inner vm out : Memory K} {T b cap : Nat} (run : f.Run P (Odd.memory inner vm) T out)
    (indexBound : ∀ j,(Odd.memory inner vm).index j ≤ b) (room : max f.localBudget b+T ≤ cap) :
    ∃ t, f.Run P (Odd.memory (trimMemory cap inner) vm) T t ∧
      ∀ j, j ≤ cap → t.data j=out.data j ∧ t.index j=out.index j :=
  innerTrim_run run ((Fragment.scoped_localBudget f).mono (le_max_left ..))
    (fun j => (indexBound j).trans (le_max_right ..)) room

end NormalSubspace
end LinearProgramming
end Optimization
end OAI
