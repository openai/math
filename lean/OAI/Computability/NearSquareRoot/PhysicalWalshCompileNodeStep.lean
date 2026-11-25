import OAI.Computability.NearSquareRoot.PhysicalWalshCompileFrames
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileDispatchPlans

/-! # The named successor of the recursive Walsh program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.Node

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode KernelPass

variable {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)
  (scan arena : Shape → ℕ) (cost : ∀ s, arena s ≤ scan s)

/-- The command opens the bank, evaluates the selected template and restores
the original record order. Frame scans do not add to the recursive call count. -/
theorem successor {d : ℕ} (prep body restore : Cmd) (frames : Framing a W d prep restore)
    (capacity : ∀ s, allowance (a+1) d s ≤ arena s)
    (runBody : Dispatch.Body hw p scan arena cost body) :
    let vm := spec hw p scan arena cost
    PhysicalWalsh.Runs ((prep.join body).join restore) vm.meter p.calls
      (fun t : vm.Step => t.val.shape) (fun t => vm.payload t.val) (fun t => vm.reply t.val) := by
  intro vm
  let u := fun t : vm.Step => t.val.shape
  let x := fun t : vm.Step => t.val.row
  let src := fun t : vm.Step => lane (a+1) W (u t) (x t)
  let dst := fun t : vm.Step => (nodeOps hw p).applyPlan p (u t) (src t)
  obtain ⟨down,up⟩ := frames hw vm.Step u (fun t => t.property) (fun t => t.val.batches)
  have ar (t : vm.Step) := capacity (u t)
  have tm (t : vm.Step) := (ar t).trans (cost (u t))
  have begin' := PhysicalWalsh.Runs.closed (m := vm.meter) (u := u) ((down x).mono tm ar)
  have end' := PhysicalWalsh.Runs.closed (m := vm.meter) (u := u) ((up dst).mono tm ar)
  have h := (begin'.seq runBody).seq end'
  change PhysicalWalsh.Runs _ vm.meter p.calls u (fun t => buffer (a+1) (u t) (x t))
    (fun t => buffer (a+1) (u t) (run hw p (u t) (x t)))
  have answer (t : vm.Step) := run_step hw p (u t) t.property (x t)
  simpa only [Nat.zero_add,Nat.add_zero,answer,src,dst] using h

end PhysicalWalshCompile.Node

end NearSquareRoot
end Computability
end OAI
