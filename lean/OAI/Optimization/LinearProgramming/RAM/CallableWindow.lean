import OAI.Optimization.LinearProgramming.RAM.Footprint
import OAI.Optimization.LinearProgramming.RAM.Code

/-! A finite reset window for the native part of a reentrant RAM call. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

/-- A sufficient starting window, determined by the program and its ordinary tape. -/
def nativeWindow {K : Type*} (p : Program) (dims : List ℕ) (xs : List K) : ℕ :=
  max (addressBudget p) (max xs.length (max dims.length dims.sum))

/-- A caller may reuse every register outside this finite window without clearing it.
Both arrays vanish there and every indirect address inside the callee is bounded. -/
theorem nativeWindow_trace {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {p : Program} {dims : List ℕ} {xs : List K} {k limit : ℕ} {tr : Fin (k+1) → State K}
    (h : Trace p (start dims xs) k tr) (hk : k≤limit) :
    Footprint (nativeWindow p dims xs + limit) ((tr (Fin.last k)).memory.atPC 0) := by
  let w := nativeWindow p dims xs
  have hp : addressBudget p ≤ w := le_max_left ..
  have hx : xs.length ≤ w := (le_max_left ..).trans (le_max_right ..)
  have hd : dims.length ≤ w := (le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))
  have hm : dims.sum ≤ w := (le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))
  have hi : Footprint w (start dims xs) := Footprint.initial dims xs hx hd
    (fun _ ha => (List.le_sum_of_mem ha).trans hm)
  have he := (trace_footprint hp hi h (Fin.last k)).mono (Nat.add_le_add_left hk w)
  exact ⟨he.address, he.data_zero, he.index_zero⟩

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
