import OAI.Computability.NearSquareRoot.PhysicalWalshChecked
import OAI.Computability.NearSquareRoot.PhysicalWalshRecursion

/-! # Recursive execution of a rounded normalized Walsh template

The template is fixed in the finite control. A prepared child request runs
that same template through a lexical jump. Any data needed when it returns
stays on the parent stack and is included in the peak-space recurrence.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh

open IntegerMultiplication Code Space KernelPass

variable {X U Y H R : Type} (d : RecSpec X U)

/-- Pack a child request, park the parent frame, invoke the interpreter at the
smaller width, and restore the parent layout. The time of the child has
coefficient exactly one regardless of the two layout commands. -/
theorem childWithFrame (u : Y → U) (child : Y → X) (frame input output : Y → Tree)
    (smaller : ∀ y, d.child (u y) (d.world (child y))) (D : ℕ)
    (resident : ∀ y, (frame y).count ≤ D*(d.arena (u y)+1))
    (down : BoundedTask (d.scan ∘ u) (d.arena ∘ u) input (fun y => .fork (d.query (child y)) (frame y)))
    (up : BoundedTask (d.scan ∘ u) (d.arena ∘ u) (fun y => .fork (d.reply (child y)) (frame y)) output) :
    OpenRun d.meter 1 u input output := by
  have call := (d.call u child smaller).left frame D resident
  have h := (OpenRun.closed (m := d.meter) down).seq (call.seq (.closed up))
  simpa only [Nat.zero_add, Nat.add_zero] using h

variable [Codec H] [Codec R] {A W : ℕ} {l : Layout U H R}

/-- The successor entry point. Layout adapters, all plan operations, and output
restoration run on the physical stack. Guards mention actual reached rows. -/
theorem successor (p : Plan A W W) (f : Ops A l) (G : Guards A l) (shape : FitsLayout d.meter l)
    (rows : ∀ t : d.Step, Rows l (d.world t.val) W)
    (leaves : LeafRuns d.meter f G d.Step (fun t => d.world t.val))
    (ready : ∀ t : d.Step, Ready f G p (d.world t.val) (rows t))
    (prepare : BoundedTask (fun t : d.Step => d.scan (d.world t.val)) (fun t => d.arena (d.world t.val))
      (fun t => d.payload t.val) (fun t => send (packet l (d.world t.val) (rows t))))
    (restore : BoundedTask (fun t : d.Step => d.scan (d.world t.val)) (fun t => d.arena (d.world t.val))
      (fun t => send (packet l (d.world t.val) (f.applyPlan p (d.world t.val) (rows t))))
      (fun t => d.reply t.val)) :
    OpenRun d.meter p.calls (fun t : d.Step => d.world t.val) (fun t => d.payload t.val) (fun t => d.reply t.val) := by
  have compiled := compileOn f G shape _ leaves p rows ready
  have entry : OpenRun d.meter 0 (fun t : d.Step => d.world t.val) _ _ := .closed prepare
  have exit : OpenRun d.meter 0 (fun t : d.Step => d.world t.val) _ _ := .closed restore
  simpa only [Nat.zero_add, Nat.add_zero] using entry.seq (compiled.seq exit)

/-- Main physical interface at fixed template. The tape machine and its local
constant are chosen before the recurrence bounds. The returned word is copied
to the output tape and every visited cell belongs to the stated arena. -/
theorem recursiveMachine (p : Plan A W W) (f : Ops A l) (G : Guards A l) (shape : FitsLayout d.meter l)
    (rows : ∀ t : d.Step, Rows l (d.world t.val) W)
    (leaves : LeafRuns d.meter f G d.Step (fun t => d.world t.val))
    (ready : ∀ t : d.Step, Ready f G p (d.world t.val) (rows t))
    (prepare : BoundedTask (fun t : d.Step => d.scan (d.world t.val)) (fun t => d.arena (d.world t.val))
      (fun t => d.payload t.val) (fun t => send (packet l (d.world t.val) (rows t))))
    (restore : BoundedTask (fun t : d.Step => d.scan (d.world t.val)) (fun t => d.arena (d.world t.val))
      (fun t => send (packet l (d.world t.val) (f.applyPlan p (d.world t.val) (rows t)))) (fun t => d.reply t.val))
    (base : BoundedTask (fun t : d.Base => d.scan (d.world t.val)) (fun t => d.arena (d.world t.val))
      (fun t => d.payload t.val) (fun t => d.reply t.val)) :
    ∃ C : ℕ, ∀ time space : U → ℕ, d.Recurrence p.calls C time space →
      TapeTask (time ∘ d.world) (space ∘ d.world) d.query d.reply :=
  d.physical base (successor d p f G shape rows leaves ready prepare restore)

end PhysicalWalsh

end NearSquareRoot
end Computability
end OAI
