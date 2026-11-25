import OAI.Computability.NearSquareRoot.PhysicalWalshPlan

/-! # Compiling only the inputs reached by a rounded Walsh pass

A fixed-point primitive may need a range bound for its accumulator. A serial
composition checks that bound on the rounded output of its first command.
This permits the available headroom to change between instructions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh

open IntegerMultiplication Code KernelPass

variable {U H R : Type} {A i o : ℕ} {l : Layout U H R}

abbrev Guards (A : ℕ) (l : Layout U H R) := ∀ {i o}, Plan A i o → ∀ u, Rows l u i → Prop

def isLeaf : ∀ {i o}, Plan A i o → Bool
  | _, _, .seq _ _ | _, _, .parallel _ _ => false
  | _, _, _ => true

/-- Each guard is checked on the actual row bank reaching the instruction. -/
def Ready (f : Ops A l) (G : Guards A l) : ∀ {i o}, Plan A i o → ∀ u, Rows l u i → Prop
  | _, _, .seq p q, u, x => Ready f G q u x ∧ Ready f G p u (f.applyPlan q u x)
  | _, _, @Plan.parallel _ i j _ _ p q, u, x =>
    Ready f G p u (fun a => x (a.castAdd j)) ∧ Ready f G q u (fun b => x (b.natAdd i))
  | _, _, p, u, x => G p u x

variable [Codec H] [Codec R] {X : Type} {m : Meter U}

/-- A primitive command works uniformly on every family of admissible inputs.
The families chosen by the compiler contain the actual intermediate results. -/
def LeafRuns (m : Meter U) (f : Ops A l) (G : Guards A l) (X : Type) (u : X → U) : Prop :=
  ∀ {i o} (p : Plan A i o), isLeaf p = true → ∀ x : ∀ t, Rows l (u t) i,
    (∀ t, G p (u t) (x t)) → OpenRun m p.calls u (fun t => send (packet l (u t) (x t)))
      (fun t => send (packet l (u t) (f.applyPlan p (u t) (x t))))

/-- The same physical compiler and exact recursive-call coefficient are valid
when operator correctness is supplied only inside its proven numeric range. -/
theorem compileOn (f : Ops A l) (G : Guards A l) (fit : FitsLayout m l) (u : X → U)
    (leaves : LeafRuns m f G X u) (p : Plan A i o) (x : ∀ t, Rows l (u t) i)
    (ready : ∀ t, Ready f G p (u t) (x t)) :
    OpenRun m p.calls u (fun t => send (packet l (u t) (x t)))
      (fun t => send (packet l (u t) (f.applyPlan p (u t) (x t)))) := by
  induction p with
  | mix c => exact leaves _ rfl x ready
  | xor g => exact leaves _ rfl x ready
  | scale q t c => exact leaves _ rfl x ready
  | child a => exact leaves _ rfl x ready
  | seq p q hp hq =>
    have first := hq x (fun t => (ready t).1)
    have second := hp (fun t => f.applyPlan q _ (x t)) (fun t => (ready t).2)
    simpa only [Ops.applyPlan, Plan.calls, Nat.add_comm p.calls q.calls] using first.seq second
  | @parallel i j o b p q hp hq =>
    exact parallelAt fit u x _ _ (hp _ (fun t => (ready t).1)) (hq _ (fun t => (ready t).2))

end PhysicalWalsh

end NearSquareRoot
end Computability
end OAI
