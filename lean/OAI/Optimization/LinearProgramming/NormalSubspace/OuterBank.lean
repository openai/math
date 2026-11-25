import OAI.Optimization.LinearProgramming.NormalSubspace.OuterHeader
import OAI.Optimization.LinearProgramming.RAM.CallableOddBase

/-! Dimension-only bounds for the two nested RAM address banks. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NormalSubspace

variable {K : Type*}

open RAM RAM.Callable Polynomial

structure OuterVM (r c : ℕ) (raw vm : Memory K) : Prop where
  data : vm.data=raw.data
  node : vm.index 43=3
  first : vm.index 45=0
  dimension : vm.index 50=r+c
  offset : vm.index 51=0
  root : vm.index 52=3
  addresses : ∀ j,vm.index j≤outerVMAddresses.eval (r+c)

noncomputable def innerRoom (work : Polynomial ℕ) : Polynomial ℕ :=
  4*X+2*outerVMAddresses+3+work

private theorem index_bound (callee caller : Memory K) (a b : Nat)
    (ca : ∀ i,callee.index i ≤ a) (cb : ∀ i,caller.index i ≤ b) (j : Nat) :
    (Odd.memory callee caller).index j ≤ 2*a+2*b+1 := by
  by_cases h : j%2=0
  · calc (Odd.memory callee caller).index j = (Odd.memory callee caller).index (2*(j/2)) :=
           congrArg _ (by omega)
         _ = 2*callee.index (j/2) := Odd.index_even ..
         _ ≤ _ := by have := ca (j/2);omega
  · calc (Odd.memory callee caller).index j = (Odd.memory callee caller).index (Odd.slot (j/2)) :=
           congrArg _ (by unfold Odd.slot;omega)
         _ = Odd.slot (caller.index (j/2)) := Odd.index_slot ..
         _ ≤ _ := by have := cb (j/2);unfold Odd.slot;omega

theorem nested_index {K : Type*} [Zero K] (r c : ℕ) (xs : List K) (vm : Memory K)
    (addresses : ∀ i,vm.index i ≤ outerVMAddresses.eval (r+c)) :
    let inner := Odd.memory (start [] ([]:List K)).memory (start [r,c] xs).memory
    ∀ j,(Odd.memory inner vm).index j ≤ 4*(r+c)+2*outerVMAddresses.eval (r+c)+3 := by
  intro inner j
  have zero : ∀ i,(start [] ([]:List K)).index i ≤ 0 := fun i => by simp [start]
  have low (i : Nat) : inner.index i ≤ 2*(r+c)+1 := by
    simpa only [Nat.mul_zero,Nat.zero_add] using index_bound _ _ 0 (r+c) zero
      (ordinaryHeader_index_le r c xs) i
  have both := index_bound inner vm (2*(r+c)+1) (outerVMAddresses.eval (r+c)) low addresses j
  omega

end NormalSubspace
end LinearProgramming
end Optimization
end OAI
