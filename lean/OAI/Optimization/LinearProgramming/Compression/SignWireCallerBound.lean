import OAI.Optimization.LinearProgramming.Compression.SignWireAddressEnvelope
import OAI.Optimization.LinearProgramming.Compression.SignWireTagProgram
import OAI.Optimization.LinearProgramming.RAM.CallableLocal

/-! The numerical comparator's native address bound grows additively under
repeated calls, including when the caller bank has no finite-support bound. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM RAM.Callable

/-- The literal tag-returning RAM run bounds the translated value of every
logical caller address. Its two final even flag registers leave those values
available at their odd addresses. -/
theorem tagReturning_callerBound {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {f : Fragment} {P : K → Prop} {cost C R : ℕ} {old caller last result : Memory K}
    (inner : f.Run P (Odd.memory old caller) cost (Odd.memory last result)) (o : Ordering)
    (htag : (Odd.memory last result).index 29 = 2*comparisonTag o+1)
    (foot : Footprint C (old.atPC 0)) (hc : ∀ j, caller.index j ≤ R) (i : ℕ) :
    result.index i ≤ max (max C R) (addressBudget (tagReturningProgram f)) + cost + 5 := by
  let W := max (max C R) (addressBudget (tagReturningProgram f))
  have hcW : C ≤ W := (le_max_left _ _).trans (le_max_left _ _)
  have hrW : R ≤ W := (le_max_right _ _).trans (le_max_left _ _)
  have hpW : addressBudget (tagReturningProgram f) ≤ W := le_max_right _ _
  have initial (j : ℕ) : ((Odd.memory old caller).atPC 0).index j ≤ 2*W+1 :=
    (cacheImage_address foot hc j).trans (max_le (by omega) (by omega))
  obtain ⟨k,hk,tr,ht,_,final,_⟩ := tagReturningProgram_trace_memory inner o htag
  have he := trace_indexBound (b := 2*W+1) (by omega : addressBudget (tagReturningProgram f) ≤ 2*W+1)
    initial ht (Fin.last k) (Odd.slot i)
  have h0 : Odd.slot i ≠ 0 := (Odd.even_ne_slot 0 i).symm
  have h2 : Odd.slot i ≠ 2 := (Odd.even_ne_slot 1 i).symm
  have read : (tr (Fin.last k)).index (Odd.slot i) = Odd.slot (result.index i) := by
    change (tr (Fin.last k)).memory.index (Odd.slot i) = _
    rw [final,Memory.putIndex_ne _ h2 _,Memory.putIndex_ne _ h0 _,Odd.index_slot]
  rw [read] at he
  change 2*result.index i+1 ≤ 2*W+1+k at he
  change result.index i ≤ W+cost+5
  omega

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
