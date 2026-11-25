import OAI.Computability.QuantumFactoring.BooleanNetwork

/-! # Local equations for a Boolean circuit trace

Each gate gives one ternary constraint on the final wire assignment. A
constant gate may have no earlier wires, so its unused arguments refer to its
own output. The solutions are exactly the evaluations on the input wires.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace BooleanChoice

open ExactQuantumFactoring

structure TraceRule (w : ℕ) where
  out : Fin w
  left : Fin w
  right : Fin w
  op : Bool → Bool → Bool

private def liftRule {w : ℕ} (g : TraceRule w) : TraceRule (w+1) :=
  ⟨g.out.castSucc, g.left.castSucc, g.right.castSucc, g.op⟩

private def finalRule {w : ℕ} : BoolNode w → TraceRule (w+1)
  | .constant b => ⟨Fin.last w, Fin.last w, Fin.last w, fun _ _ => b⟩
  | .copy i => ⟨Fin.last w, i.castSucc, Fin.last w, fun x _ => x⟩
  | .neg i => ⟨Fin.last w, i.castSucc, Fin.last w, fun x _ => !x⟩
  | .conj i j => ⟨Fin.last w, i.castSucc, j.castSucc, fun x y => x && y⟩

/-- The local gate equations in the order in which the network creates its wires. -/
def rules {n w : ℕ} (net : BoolNet n w) : Fin net.count → TraceRule w :=
  match net with
  | .input => Fin.elim0
  | .add p o => Fin.snoc (fun i => liftRule (rules p i)) (finalRule o)

private def agrees {w : ℕ} (v : Fin w → Bool) (g : TraceRule w) : Prop :=
  v g.out = g.op (v g.left) (v g.right)

private theorem agrees_final {w : ℕ} (v : Fin (w+1) → Bool) (o : BoolNode w) :
    agrees v (finalRule o) ↔ v (Fin.last w) = o.eval (fun i => v i.castSucc) := by
  cases o <;> rfl

/-- Checking every gate equation is equivalent to evaluating the network on the
restriction of the proposed trace to its input wires. -/
theorem trace_iff {n w : ℕ} (net : BoolNet n w) (v : Fin w → Bool) :
    (∀ i, let g := rules net i; v g.out = g.op (v g.left) (v g.right)) ↔
      v = net.eval (fun i => v (i.castLE net.input_le)) := by
  change (∀ i, agrees v (rules net i)) ↔ _
  induction net with
  | input => exact ⟨fun _ => rfl, fun _ i => Fin.elim0 i⟩
  | @add k p o ih =>
    let old : Fin k → Bool := fun i => v i.castSucc
    let x : Fin n → Bool := fun i => v (i.castLE (p.add o).input_le)
    change (∀ i : Fin (p.count + 1), agrees v (Fin.snoc (α := fun _ => TraceRule (k+1)) (fun j => liftRule (rules p j)) (finalRule o) i)) ↔
      v = (p.add o).eval x
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, agrees_final]
    change (∀ i, agrees old (rules p i)) ∧ v (Fin.last k) = o.eval old ↔ _
    rw [ih]
    change old = p.eval x ∧ v (Fin.last k) = o.eval old ↔ v = (p.add o).eval x
    constructor
    · rintro ⟨ho, hl⟩
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [BoolNet.eval_add_last, ← ho] using hl
      · simpa only [BoolNet.eval_add_castSucc] using congrFun ho j
    · intro h
      have ho : old = p.eval x := by
        funext j
        simpa only [BoolNet.eval_add_castSucc] using congrFun h j.castSucc
      refine ⟨ho, ?_⟩
      simpa only [ho, BoolNet.eval_add_last] using congrFun h (Fin.last k)

end BooleanChoice

end SpectralBooks
end LinearAlgebra
end OAI
