import OAI.Optimization.LinearProgramming.RAM.CallableResume

/-! Evaluate a complete numerical fragment on its persistent native memory. The
odd VM caller retains its whole heap; only logical scratch address 1 receives tag 0. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG

open RAM RAM.Callable

def numericCall (f : Fragment) : Fragment := .invoke (f.program 0) 1 (Odd.sink (.index 1))

theorem numericCall_run {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : K→Prop} {f : Fragment} {a b : Memory K} {cost : ℕ} (number : f.Run P a cost b)
    (vm : Memory K) (safe : vm.AllData P) :
    (numericCall f).Run P (Odd.memory a vm) (2*(cost+1)+2) (Odd.memory b (vm.putIndex 1 0)) := by
  obtain ⟨k,hk,tr,trace,halt,mem,bounds⟩:=Fragment.run_halt number 0
  have call:=Odd.invoke_memory 1 (.index 1) P a vm tr (show 0 < 1 by decide) safe trace bounds halt
    (show (vm.putIndex 1 0).AllData P from safe)
  rw [mem] at call
  exact call.mono (by omega)

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI
