import OAI.Optimization.LinearProgramming.RAM.CallableInvoke
import OAI.Optimization.LinearProgramming.RAM.CallableOddBase

/-! Native return tags can be delivered into an ordinary logical caller register while
leaving all its other logical registers in the persistent odd bank. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Odd

/-- Addresses written into a logical address register also use the odd representation. -/
def sink : TagSink → TagSink
  | .index d => .indexMapped (slot d) slot
  | .indexMapped d f => .indexMapped (slot d) (fun tag => slot (f tag))
  | .scalar d f => .scalar (slot d) f

theorem sink_store {K : Type*} [RatCast K] (dest : TagSink) (tag : ℕ) (callee caller : Memory K) :
    (sink dest).store tag (memory callee caller) = memory callee (dest.store tag caller) := by
  cases dest with
  | index d => exact putIndex ..
  | indexMapped d f => exact putIndex ..
  | scalar d f => exact putData ..

/-- The physical input includes the native canonical input and the logical caller. The
final physical register file includes the callee's exact output as well as the logical
caller with its one return register updated. -/
theorem invoke_packed {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {p : Program} (count : ℕ) (dest : TagSink) (P : K → Prop) (caller : Memory K)
    (dims : List ℕ) (input : List K) {k tag : ℕ} (trace : Fin (k+1) → State K)
    (htag : tag<count) (hc : caller.AllData P)
    (hrun : Trace p (start dims input) k trace) (hs : ∀ i j, P ((trace i).data j))
    (hdone : (trace (Fin.last k)).output=some tag) (hreturn : (dest.store tag caller).AllData P) :
    (Fragment.invoke p count (sink dest)).Run P (memory (start dims input).memory caller) (2*k+2)
      (memory (trace (Fin.last k)).memory (dest.store tag caller)) := by
  let before := (start dims input).memory
  let after := (trace (Fin.last k)).memory
  have hbefore : before.AllData P := by
    intro j
    change P ((start dims input).data j)
    rw [← hrun.1]
    exact hs 0 j
  have hw : Fragment.returnMemory (sink dest) tag (memory before caller) (trace (Fin.last k)) =
      memory after (dest.store tag caller) := by
    unfold Fragment.returnMemory
    rw [show Call.savedOddFrame (memory before caller) = frame caller from savedOddFrame_pack ..]
    exact sink_store ..
  rw [← hw]
  apply Fragment.invoke_prepared count (sink dest) P (memory before caller) dims input trace htag
    (data_even before caller) (index_even before caller) (allData before caller hbefore hc) hrun hs hdone
  rw [hw]
  exact allData _ _ (hs _) hreturn

end Odd
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
