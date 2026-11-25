import OAI.Computability.NearSquareRoot.PhysicalWalshCompileChildAdapter
import OAI.Computability.NearSquareRoot.KernelComputableTemplateSearch
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSound
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileRegisters
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeCall

/-! # One emitted recursive child call with its parent frame restored -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileChild

open IntegerMultiplication Code Space KernelPass KernelPass.ComputableSyntax PhysicalWalsh PhysicalWalshNode
open CommonRegisters GeneratorSyntax

/-- Prepare the recursive packet, call the scoped program on its left field
while the parent frame is parked, and restore the parent layout. -/
def command (down : Control → Cmd) (up : Cmd) (k : Control) : Cmd :=
  (down k).join ((PhysicalWalshCompile.left (.again 0)).join up)

theorem effective_command {down : Control → Cmd} (he : Effective ltr down) (up : Cmd) :
    Effective ltr (command down up) := he.join (effective_const ltr _)

theorem within_command {R : ℕ} {down : Control → Cmd} {up : Cmd}
    (hr : 0 < R) (hd : ∀ k, Within R (down k)) (hu : Within R up) (k : Control) :
    Within R (command down up k) :=
  ⟨hd k, RegisterWitness.splitRoot_within.mpr ⟨hr,trivial,trivial,trivial,hr⟩, hu⟩

private theorem closed_output {X U : Type} (m : Meter U) (u : X → U) {c : Cmd}
    {q r : X → Tree} {h : X → ℕ} (D : ℕ) (bound : ∀ x, h x ≤ D*(m.arena (u x)+1))
    (clock : ∀ x env park, Fits env c (pile 0 (q x) park) (pile 0 (r x) park) (h x))
    (inputSize : ∀ x, (q x).count ≤ h x) :
    Runs c m 0 u q r := by
  apply Runs.closed
  refine ⟨2*D,fun x env park b hp => ?_⟩
  have he := bound x
  have hs := inputSize x
  have ht : D*(m.arena (u x)+1) ≤ D*(m.scan (u x)+1) := Nat.mul_le_mul_left D (Nat.succ_le_succ (m.arena_le (u x)))
  have hc := BoundedFits.of_fits (clock x env park) (cap := b+(2*D)*(m.arena (u x)+1))
    (depth := (2*D)*(m.arena (u x)+1)) (fun j => ?_) (by rw [Nat.mul_assoc, Nat.two_mul]; omega)
  · exact hc.mono (by dsimp only [Function.comp_apply]; rw [Nat.mul_assoc,Nat.two_mul]; omega) le_rfl le_rfl
  · rw [Nat.mul_assoc,Nat.two_mul]
    by_cases hj : j=0
    · subst j
      rw [letters_here,List.length_append,Tree.spell_length]
      have := hp 0
      omega
    · rw [pile_far _ _ (Ne.symm hj)]
      have := hp j
      omega

open private flat_child row_budget from OAI.Computability.NearSquareRoot.PhysicalWalshNodeCall

/-- The actual child command has one unit of recursive time, independently
of its descriptor and the extent of the restored parent frame. -/
theorem runs {a W d : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)
    (down : Control → Cmd) (up : Cmd) (frame : Adapter d down up)
    (scan arena : PhysicalWalshNode.Shape → ℕ) (cost : ∀ s, arena s ≤ scan s)
    (cap : ∀ s, allowance (a+1) d s ≤ arena s) (axis : Fin (a+1)) :
    let vm := spec hw p scan arena cost
    let u := fun t : vm.Step => t.val.shape
    ∀ x : ∀ t, Rows (work a W) (u t) 1,
    (∀ t, Good hw p (descend (a+1) W axis (u t)) (x t 0)) →
    Runs (command down up (a+1,W,axis.val)) vm.meter 1 u
      (fun t => send (packet (work a W) (u t) (x t)))
      (fun t => send (packet (work a W) (u t) (fun _ : Fin 1 => run hw p (descend (a+1) W axis (u t)) (x t 0)))) := by
  intro vm u x ready
  obtain ⟨C,hframe⟩ := frame a W axis
  let shape t := descend (a+1) W axis (u t)
  let y (t : vm.Step) := childInvocation hw p t.val t.property axis (x t 0) (ready t)
  let parent t := ChildAdapter.saved a W (u t)
  let input t := (work a W).store (u t) (x t 0)
  let output t := (work a W).store (u t) (run hw p (shape t) (x t 0))
  let localTime (t : vm.Step) (row : Stream) :=
    C*((Header.scale (a+1) (u t)+1)^d + ChildAdapter.volume (a+1) (u t) + size row +1)
  have pos (t : vm.Step) : 0 < (u t).level := t.property
  have fits (t : vm.Step) (v : Data (u t)) :
      localTime t ((work a W).store (u t) v) ≤ (C*9)*(arena (u t)+1) := by
    have bound := cap (u t)
    change (count (a+1) (u t)+1)*(grow (a+1) (u t).level+(u t).w+1)+(Header.scale (a+1) (u t)+1)^d ≤ arena (u t) at bound
    rw [Nat.add_comm (grow _ _) (u t).w] at bound
    change ChildAdapter.volume (a+1) (u t)+(Header.scale (a+1) (u t)+1)^d ≤ arena (u t) at bound
    have vol := row_budget (W := W) axis (u t) (pos t) v
    dsimp only [localTime]
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left C
    omega
  have call : Runs (.again 0) vm.meter 1 u (vm.query ∘ y) (vm.reply ∘ y) := by
    refine ⟨0,fun t env clock space permit park base hp => ?_⟩
    simpa using permit (y t) ⟨pos t,t.val.batches,axis,rfl⟩ park base hp
  have useFrame := call.left (fun t => send (parent t)) (C*9)
    (fun t => (hframe (u t) (pos t) (input t)).2.2.2.2.trans (fits t (x t 0)))
  have eqIn (t) : input t = flat (a+1) (shape t) (x t 0) := flat_child axis _ (pos t) _
  have eqOut (t) : output t = flat (a+1) (shape t) (run hw p (shape t) (x t 0)) := flat_child axis _ (pos t) _
  have pre : Runs (down (a+1,W,axis.val)) vm.meter 0 u
      (fun t => send (parent t,[input t])) (fun t => .fork (vm.query (y t)) (send (parent t))) := by
    apply closed_output vm.meter u (h := fun t => localTime t (input t))
      (C*9) (fun t => fits t (x t 0)) _ (fun t => (hframe (u t) (pos t) (input t)).2.2.1)
    intro t env park
    have h := (hframe (u t) (pos t) (input t)).1 env park
    change Fits env _ _ (pile 0 (.fork (.fork (.atom _) (send (_, flat (a+1) (shape t) (x t 0)))) _) _) _
    rw [← eqIn t]
    exact h
  have post : Runs up vm.meter 0 u (fun t => .fork (vm.reply (y t)) (send (parent t)))
      (fun t => send (parent t,[output t])) := by
    apply closed_output vm.meter u (h := fun t => localTime t (output t))
      (C*9) (fun t => fits t (run hw p (shape t) (x t 0))) ?_ ?_
    · intro t env park
      change Fits env _ (pile 0 (.fork (send (_,flat (a+1) (shape t) (run hw p (shape t) (x t 0)))) _) _) _ _
      rw [← eqOut t]
      exact (hframe (u t) (pos t) (output t)).2.1 env park
    · intro t
      change (Tree.fork (send (_,flat (a+1) (shape t) (run hw p (shape t) (x t 0)))) _).count ≤ _
      rw [← eqOut t]
      exact (hframe (u t) (pos t) (output t)).2.2.2.1
  exact pre.seq (useFrame.seq post)

/-- The reached child-leaf obligation at a physical recursive node. -/
def LeafRuns {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)
    (scan arena : PhysicalWalshNode.Shape → ℕ) (cost : ∀ s, arena s ≤ scan s)
    (op : Op) (cmd : Cmd) : Prop :=
    let vm := spec hw p scan arena cost
    let L := coords a W
    let desc := Header.wire (a+1)
    let f := PhysicalWalshContext.routeOps L PhysicalWalshNode.Shape.w desc (xor a)
      (fun axis s => run hw p (descend (a+1) W axis s))
    let G : Guards (a+1) (work a W) := PhysicalWalshContext.routeGuards L PhysicalWalshNode.Shape.w desc (fun _ _ _ => True)
      (fun axis s => Good hw p (descend (a+1) W axis s))
    PhysicalWalshCompile.Implements f G vm.meter (fun t : vm.Step => t.val.shape)
      (Packed.leaf (a+1) op) cmd

/-- A well-formed opcode invokes exactly the indicated shorter slot with the
parent plan and the guard for its reached input lane. -/
theorem implements {a W d : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)
    (down : Control → Cmd) (up : Cmd) (frame : Adapter d down up)
    (scan arena : PhysicalWalshNode.Shape → ℕ) (cost : ∀ s, arena s ≤ scan s)
    (cap : ∀ s, allowance (a+1) d s ≤ arena s) (op : Op)
    (hop : op.1 = 3) (valid : arg op 0 < a+1) :
    LeafRuns hw p scan arena cost op (command down up (a+1,W,arg op 0)) := by
  dsimp only [LeafRuns]
  rw [show Packed.leaf (a+1) op = ⟨1,1,Plan.child ⟨arg op 0,valid⟩⟩ by simp [Packed.leaf,hop,valid]]
  exact runs hw p down up frame scan arena cost cap ⟨arg op 0,valid⟩

/-- One code generator and register cutoff serve every recursively called
node. The local polynomial degree is selected together with the emitter. -/
theorem compile : ∃ (c : Control → Cmd) (R d : ℕ),
    Effective ltr c ∧ 1 ≤ d ∧ (∀ k, Within R (c k)) ∧
    ∀ (a W : ℕ) (hw : 0 < W) (p : Plan (a+1) W W)
      (scan arena : PhysicalWalshNode.Shape → ℕ) (cost : ∀ s, arena s ≤ scan s),
      (∀ s, allowance (a+1) d s ≤ arena s) → ∀ (op : Op), op.1 = 3 → arg op 0 < a+1 →
        LeafRuns hw p scan arena cost op (c (a+1,W,arg op 0)) := by
  obtain ⟨R,d,down,up,hd,he,hr,hu,frame⟩ := compiledFrames
  refine ⟨command down up,R+1,d,effective_command he up,hd,fun k => within_command (by omega)
    (fun k => RegisterSelect.within_mono (Nat.le_succ R) _ (hr k))
    (RegisterSelect.within_mono (Nat.le_succ R) _ hu) k,?_⟩
  intro a W hw p scan arena cost cap op tag valid
  exact implements hw p down up frame scan arena cost cap op tag valid

/-- The physical control constants are read directly from the parameter
record used by the template compiler, including its decoded row width. -/
def rawControl (e : Raw × Op) : Control :=
  (e.1.1, ((ComputableSyntax.Shape.algebra e.1.1).parse e.1.2).1.1, arg e.2 0)

theorem primrec_rawControl : Primrec rawControl := by
  have pa : Primrec (fun e : Raw × Op => (ComputableSyntax.Shape.algebra e.1.1).parse e.1.2) := ComputableSyntax.Shape.primrec_algebra.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst)
  exact (Primrec.fst.comp Primrec.fst).pair (((Primrec.fst.comp Primrec.fst).comp pa).pair
    (primrec_arg.comp Primrec.snd (.const 0)))

/-- A child opcode participates directly in the prefix compiler interface.
The arity and actual square width may vary across selected templates. -/
theorem compileRaw : ∃ (c : Raw → Op → Cmd) (R d : ℕ), Effective ltr (Function.uncurry c) ∧
    1 ≤ d ∧ (∀ raw op, Within R (c raw op)) ∧
    ∀ (a W : ℕ) (ops : List Op) (_ : (Packed.decode (a+1) ops).i = W)
      (hw : 0 < W) (p : Plan (a+1) W W) (scan arena : PhysicalWalshNode.Shape → ℕ)
      (cost : ∀ s, arena s ≤ scan s), (∀ s, allowance (a+1) d s ≤ arena s) →
      ∀ (op : Op), op.1 = 3 → arg op 0 < a+1 →
        LeafRuns hw p scan arena cost op (c (a+1,ops) op) := by
  obtain ⟨c,R,d,he,hd,hr,run⟩ := compile
  refine ⟨fun raw op => c (rawControl (raw,op)), R,d,he.comp primrec_rawControl.to_comp,hd,
    fun raw op => hr _,?_⟩
  intro a W ops eqn hw p scan arena cost cap op tag valid
  dsimp only [rawControl]
  rw [← Packed.decode_shape, show (Packed.decode (a+1) ops).shape.1.1 = W from eqn]
  exact run a W hw p scan arena cost cap op tag valid

end PhysicalWalshCompileChild

end NearSquareRoot
end Computability
end OAI
