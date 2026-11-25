import OAI.Computability.NearSquareRoot.PhysicalWalshNodeCall
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeFrames
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeBase
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeEntry
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeFuel

/-! # A compiled recursive Walsh piece on the actual ordered records

The only external array operation is an ordinal same-column XOR permutation.
The template's dyadic arithmetic, scan order, batch split and merge, terminal
four-point transform, compact child geometry, and recursive calls are realized
by fixed stack commands. The child-time coefficient is exactly `p.calls`.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open IntegerMultiplication Code Space KernelPass PhysicalWalsh PhysicalWalshContext

/-- One address bank on which a nonterminal template can execute an XOR. -/
structure XorInput (W : ℕ) where
  shape : Shape
  positive : 0 < shape.level
  batches : W^shape.level ∣ shape.pref
  row : Data shape

/-- The exact source address required for each target record is `xorIndex`.
The same compact parent and grid headers are returned by the permutation. -/
def XorRuns (a W : ℕ) (scan arena : Shape → ℕ) : Prop := ∀ g : Fin (a+1) × Fin (a+1),
  BoundedTask (fun t : XorInput W => scan t.shape) (fun t => arena t.shape)
    (fun t => send (packet (work a W) t.shape (fun _ : Fin 1 => t.row)))
    (fun t => send (packet (work a W) t.shape (fun _ : Fin 1 => xor a g t.shape t.row)))

/-- Peak local workspace, including the compact descriptor carried by an
arithmetic or permutation leaf. -/
def nodeArena (a W d : ℕ) (s : Shape) := max (allowance (a+1) d s)
  (routeArena (coords a W) Shape.w (Header.wire (a+1)) s)

/-- A packed interchange can take more steps than its visited workspace. -/
def nodeScan (a W d : ℕ) (extra : Shape → ℕ) (s : Shape) := nodeArena a W d s + extra s

variable {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)

/-- Concrete terminal and successor commands, before tying the recursion.
Numerical representability is part of the semantic invocation and contributes
no tape input. -/
theorem localPrograms : ∃ D : ℕ, 1 ≤ D ∧ ∀ (scan arena : Shape → ℕ) (cost : ∀ s, arena s ≤ scan s),
    (∀ s, allowance (a+1) D s ≤ arena s) →
    (∀ s, routeArena (coords a W) Shape.w (Header.wire (a+1)) s ≤ arena s) →
    XorRuns a W scan arena →
    let vm := spec hw p scan arena cost
    BoundedTask (fun t : vm.Base => scan t.val.shape) (fun t => arena t.val.shape)
      (fun t => vm.payload t.val) (fun t => vm.reply t.val) ∧
    OpenRun vm.meter p.calls (fun t : vm.Step => t.val.shape) (fun t => vm.payload t.val) (fun t => vm.reply t.val) := by
  let Terminal := {v : Invocation hw p // v.shape.level = 0}
  obtain ⟨b,terminal⟩ := invocationBaseBounded hw p (fun t : Terminal => t.val) (fun t => t.property)
  obtain ⟨f,frames⟩ := nodeFrames a W hw
  obtain ⟨c,calls⟩ := childCalls hw p
  let D := max 1 (max b (max f c))
  refine ⟨D, le_max_left .., fun scan arena cost capacity fits router => ?_⟩
  intro vm
  have caps {d : ℕ} (hd : d ≤ D) (s : Shape) : allowance (a+1) d s ≤ arena s :=
    (allowance_mono hd s).trans (capacity s)
  have hb : b ≤ D := (le_max_left ..).trans (le_max_right ..)
  have hf : f ≤ D := (le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))
  have hc : c ≤ D := (le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))
  refine ⟨terminal.mono (fun t => (caps hb t.val.shape).trans (cost _)) (fun t => caps hb t.val.shape), ?_⟩
  let u := fun t : vm.Step => t.val.shape
  let x := fun t : vm.Step => t.val.row
  let src := fun t : vm.Step => lane (a+1) W (u t) (x t)
  let dst := fun t : vm.Step => (nodeOps hw p).applyPlan p (u t) (src t)
  obtain ⟨prepare, restore⟩ := frames vm.Step u (fun t => t.property) (fun t => t.val.batches)
  have crun := calls scan arena cost (caps hc)
  let down := OpenRun.closed (m := vm.meter) (u := u) ((prepare x).mono
    (fun t => (caps hf (u t)).trans (cost _)) (fun t => caps hf (u t)))
  have up := OpenRun.closed (m := vm.meter) (u := u) ((restore dst).mono
    (fun t => (caps hf (u t)).trans (cost _)) (fun t => caps hf (u t)))
  have body := PhysicalWalshContext.runOn (coords a W) Shape.w (Header.wire (a+1)) (xor a)
    (fun axis s => run hw p (descend (a+1) W axis s)) (fun _ _ _ => True)
    (fun axis s => Good hw p (descend (a+1) W axis s)) (m := vm.meter) fits u
    (fun g y _ => OpenRun.closed (by
      let pack := fun t : vm.Step => (⟨u t,t.property,t.val.batches,y t 0⟩ : XorInput W)
      have op := (router g).on pack
      have single t : (fun _ : Fin 1 => y t 0) = y t := funext fun i => congrArg (y t) (Subsingleton.elim 0 i)
      change BoundedTask (fun i => scan (u i)) (fun i => arena (u i)) _ _
      simpa only [pack,single,work] using op)) crun p src
    (fun t => good_step hw p t.property t.val.representable)
  have complete := (down.seq body).seq up
  change OpenRun vm.meter p.calls u (fun t => buffer (a+1) (u t) (x t))
    (fun t => buffer (a+1) (u t) (run hw p (u t) (x t)))
  have answer (t : vm.Step) := run_step hw p (u t) t.property (x t)
  simpa only [Nat.zero_add, Nat.add_zero, answer, dst, src] using complete

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
