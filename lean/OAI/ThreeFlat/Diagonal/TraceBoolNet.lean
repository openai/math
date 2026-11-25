import OAI.Computability.QuantumFactoring.BooleanNetworkFurther
import OAI.Computability.VPVNP.BooleanTranscript

namespace OAI
/-! # Addressed Boolean transcripts of native word-arithmetic networks

The compiler appends one AND or NOT gate for each bounded-fan-in node. A
single transcript retains every output of a multi-output word operation.
-/

namespace ThreeFlat.Diagonal.TraceBoolNet

open ExactQuantumFactoring
open Computability.VPVNP (Ref)
open Computability.VPVNP.BooleanTranscript

variable {σ : Type*} {n m k : ℕ}

/-- Retain the reference to a previously computed wire after appending a gate. -/
def extend : Ref Bool σ k → Ref Bool σ (k + 1)
  | .var a => .var a
  | .const b => .const b
  | .gate i => .gate i.castSucc

@[simp] theorem read_extend (x : σ → Bool) (v : Fin k → Bool) (b : Bool)
    (r : Ref Bool σ k) :
    (extend r).read id x (Fin.snoc v b) = r.read id x v := by
  cases r <;> simp [extend, Ref.read]

def gate (wires : Fin k → Ref Bool σ m) : BoolNode k → Gate σ m
  | .constant b => .and (.const b) (.const true)
  | .copy i => .and (wires i) (.const true)
  | .neg i => .not (wires i)
  | .conj i j => .and (wires i) (wires j)

private theorem gate_eval (o : BoolNode k) (wires : Fin k → Ref Bool σ m)
    (x : σ → Bool) (v : Fin m → Bool) :
    (gate wires o).eval x v = o.eval (fun i ↦ (wires i).read id x v) := by
  cases o <;> simp [gate, Gate.eval, BoolNode.eval, Ref.read]

def wire (input : Fin n → σ ⊕ Bool) : {k : ℕ} → (p : BoolNet n k) →
    Fin k → Ref Bool σ p.count
  | _, .input, i => (input i).elim Ref.var Ref.const
  | _, .add p _, i => Fin.snoc (α := fun _ => Ref Bool σ (p.count + 1)) (extend ∘ wire input p) (Ref.gate (Fin.last p.count)) i

/-- The number of transcript gates is exactly the number of native gates. -/
def program (input : Fin n → σ ⊕ Bool) : {k : ℕ} → (p : BoolNet n k) → Program σ p.count
  | _, .input => .nil
  | _, .add p o => (program input p).snoc (gate (wire input p) o)

theorem wire_eval (input : Fin n → σ ⊕ Bool) (p : BoolNet n k) (x : σ → Bool) (i : Fin k) :
    (wire input p i).read id x ((program input p).run x) =
      p.eval (fun j ↦ (input j).elim x id) i := by
  induction p with
  | input =>
    change ((input i).elim Ref.var Ref.const).read id x _ = (input i).elim x id
    cases input i <;> rfl
  | @add k p o ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [wire, program, Program.run, Fin.snoc_last, Ref.read, BoolNet.eval_add_last]
      rw [gate_eval]
      exact congrArg o.eval (funext ih)
    · simp only [wire, program, Program.run, Fin.snoc_castSucc, Function.comp_apply,
        BoolNet.eval_add_castSucc]
      exact (read_extend x ((program input p).run x) _ (wire input p j)).trans (ih j)

/-- Select one output of a native multi-output circuit; all choices share
one compiled program. -/
def outputCircuit (input : Fin n → σ ⊕ Bool) (N : BooleanNetwork n m) (j : Fin m) :
    Circuit σ N.net.count := ⟨program input N.net, wire input N.net (N.output j)⟩

@[simp] theorem outputCircuit_eval (input : Fin n → σ ⊕ Bool) (N : BooleanNetwork n m)
    (j : Fin m) (x : σ → Bool) :
    (outputCircuit input N j).eval x = N.eval (fun i ↦ (input i).elim x id) j :=
  wire_eval input N.net x (N.output j)

end ThreeFlat.Diagonal.TraceBoolNet

end OAI
