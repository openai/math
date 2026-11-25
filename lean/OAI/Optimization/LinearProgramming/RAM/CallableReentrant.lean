import OAI.Optimization.LinearProgramming.RAM.CallablePrepare
import OAI.Optimization.LinearProgramming.RAM.CallableControl

/-! Load fresh input tapes before each native call, including calls from a loop. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Fragment

/-- The fixed preprocessing block first clears the previous invocation's finite memory. -/
def stage (f : Fragment) : Fragment := seq (ofBlock prepareInputs) f

theorem stage_of_run {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : K → Prop} {f : Fragment} {out : Memory K} {bound : ℕ}
    (old : State K) (caller : Memory K) (sb ab C B : ℕ) (xs : List K) (dims : List ℕ)
    (raw : RawTapes caller sb ab B xs dims) (hc : caller.AllData P) (ho : old.memory.AllData P)
    (hz : P 0) (foot : Footprint C old) (hCB : C<B) (hxs : xs.length≤B) (hdims : dims.length≤B)
    (work : f.Run P (Odd.memory (start dims xs).memory caller) bound out) :
    (stage f).Run P (Odd.memory old.memory caller) (19*B+225+bound) out := by
  obtain ⟨k,hk,h⟩ := prepareInputs_native old caller sb ab C B xs dims raw hc ho hz foot hCB hxs hdims
  exact ((Run.ofBlock h).seq work).mono (Nat.add_le_add_right hk bound)

end Fragment
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
