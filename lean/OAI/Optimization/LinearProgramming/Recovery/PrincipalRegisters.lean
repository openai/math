import OAI.Optimization.LinearProgramming.RAM.CallableScopedRun
import OAI.Optimization.LinearProgramming.RAM.CallableScopedAccess
import OAI.Optimization.LinearProgramming.RAM.CallableOddBase
import OAI.Optimization.LinearProgramming.RAM.Footprint

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace Principal

open RAM RAM.Callable

/-- The odd caller's address bound after a relocatable worker. Each physical address
is represented by a pair whose low bit selects the bank. -/
def nextLimit (f : Fragment) (cap callerLimit work : ℕ) := max f.localBudget (2*max cap callerLimit+1)+work

theorem packed_index {K : Type*} (native caller : Memory K) {c l : ℕ}
    (left : ∀j,native.index j ≤ c) (right : ∀j,caller.index j ≤ l) :
    ∀j,(Odd.memory native caller).index j ≤ 2*max c l+1 := by
  intro j
  have hd:=Nat.mod_add_div j 2
  have evenBound:=left (j/2)
  have oddBound:=right (j/2)
  by_cases even : j%2=0
  · rw [show j=2*(j/2) by omega,Odd.index_even];omega
  · rw [show j=Odd.slot (j/2) by unfold Odd.slot;omega,Odd.index_slot];unfold Odd.slot;omega

theorem final_caller_index {f : Fragment} [Fragment.FixedAccess f] {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {native caller n' c' : Memory K} {cap limit work : ℕ} {P : K→Prop}
    (run : f.Run P (Odd.memory native caller) work (Odd.memory n' c')) (nb : ∀j,native.index j ≤ cap) (cb : ∀j,caller.index j ≤ limit) :
    ∀j,c'.index j ≤ nextLimit f cap limit work := by
  let b:=max f.localBudget (2*max cap limit+1)
  have start (j) : (Odd.memory native caller).index j ≤ b:=(packed_index native caller nb cb j).trans (le_max_right ..)
  have done:=run.final_index_bound ((Fragment.scoped_localBudget f).mono (le_max_left ..)) start
  intro j
  have last:=done (Odd.slot j)
  rw [Odd.index_slot] at last
  unfold Odd.slot at last
  change c'.index j ≤ b+work
  omega

end Principal
end Recovery
end LinearProgramming
end Optimization
end OAI
