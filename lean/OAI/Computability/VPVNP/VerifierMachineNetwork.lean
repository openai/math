import OAI.Computability.BinPacking.CookLevin.OutputOrder
import OAI.Computability.VPVNP.VerifierMachineCook

/-!
# Compiling finite arrays of local Boolean formulas

The coefficient verifier in §1.1 parses a table and then simulates one chosen transition
per clock tick. This interface indexes the existing Cook–Levin circuit compiler by named
finite types, so that table fields, tape cells, and input bits can be used directly as wire
indices. A layer preserves sharing between all previous gates.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace VerifierNetwork

open BinPackingGames.Foundations.Complexity.CookLevin

/-- Boolean expressions over the live wires of a verifier circuit. -/
abbrev Expr := StatementCircuit.Expr

/-- An array of live wire references in a circuit whose free inputs are indexed by `σ`. -/
structure Frame (σ τ : Type*) [Fintype σ] [Fintype τ] where
  /-- The gate fragment and its live wire references, with the input and output index types
  enumerated by finite ordinals. -/
  core : CircuitBatch.Frame (Fintype.card σ) (Fintype.card τ)

namespace Frame

variable {σ τ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ]

/-- Read the value of a chosen live wire under an assignment to the free inputs. -/
noncomputable def eval (f : Frame σ τ) (x : σ → Bool) (i : τ) : Bool :=
  f.core.eval (x ∘ (Fintype.equivFin σ).symm) (Fintype.equivFin τ i)

/-- Number of gates already emitted into the frame's circuit fragment. -/
def size (f : Frame σ τ) : ℕ := f.core.fragment.gates.length

/-- The gate-free frame that selects its live wires directly from the inputs. -/
noncomputable def initial (wire : τ → σ) : Frame σ τ :=
  ⟨CircuitBatch.Frame.initial (Fintype.equivFin σ ∘ wire ∘ (Fintype.equivFin τ).symm)⟩

@[simp] theorem initial_eval (wire : τ → σ) (x : σ → Bool) (i : τ) :
    (initial wire).eval x i = x (wire i) := by simp [initial, eval]

@[simp] theorem initial_size (wire : τ → σ) : (initial wire).size = 0 := rfl

/-- Append a batch of Boolean expressions over the current live wires and expose their outputs
as the next frame. -/
noncomputable def step (f : Frame σ τ) (es : ρ → Expr τ) : Frame σ ρ :=
  ⟨f.core.step (fun i => (es ((Fintype.equivFin ρ).symm i)).rename (Fintype.equivFin τ))⟩

@[simp] theorem step_eval (f : Frame σ τ) (es : ρ → Expr τ) (x : σ → Bool) (i : ρ) :
    (f.step es).eval x i = (es i).eval (f.eval x) := by
  simp [step, eval, CircuitBatch.Frame.step_eval]
  rfl

theorem step_size_le (f : Frame σ τ) (es : ρ → Expr τ) (D : ℕ)
    (h : ∀ i, (es i).size ≤ D) :
    (f.step es).size ≤ f.size + Fintype.card ρ * D := by
  apply f.core.step_gate_count_le
  intro i
  simpa using h ((Fintype.equivFin ρ).symm i)

/-- Perform a sequence of indexed expression batches, retaining all previously emitted gates. -/
noncomputable def steps (f : Frame σ τ) (es : ℕ → τ → Expr τ) : ℕ → Frame σ τ
  | 0 => f
  | t + 1 => (steps f es t).step (es t)

@[simp] theorem steps_zero (f : Frame σ τ) (es : ℕ → τ → Expr τ) : f.steps es 0 = f := rfl

theorem steps_succ (f : Frame σ τ) (es : ℕ → τ → Expr τ) (t : ℕ) :
    f.steps es (t + 1) = (f.steps es t).step (es t) := rfl

theorem steps_size_le (f : Frame σ τ) (es : ℕ → τ → Expr τ) (T D : ℕ)
    (h : ∀ t < T, ∀ i, (es t i).size ≤ D) :
    (f.steps es T).size ≤ f.size + T * (Fintype.card τ * D) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [steps_succ, Nat.succ_mul]
    have hp := ih fun t ht => h t (by omega)
    have hs := step_size_le (f.steps es T) (es T) D (h T (by omega))
    omega

/-- Select live outputs without emitting any gates. -/
noncomputable def select (f : Frame σ τ) (wire : ρ → τ) : Frame σ ρ :=
  ⟨⟨f.core.fragment, f.core.wires ∘ Fintype.equivFin τ ∘ wire ∘ (Fintype.equivFin ρ).symm⟩⟩

@[simp] theorem select_size (f : Frame σ τ) (wire : ρ → τ) : (f.select wire).size = f.size := rfl

@[simp] theorem select_eval (f : Frame σ τ) (wire : ρ → τ) (x : σ → Bool) (i : ρ) :
    (f.select wire).eval x i = f.eval x (wire i) := by
  simp [select, eval, CircuitBatch.Frame.eval]

/-- Retain free inputs alongside a block's outputs for later layers. -/
noncomputable def withInput (f : Frame σ τ) : Frame σ (σ ⊕ τ) :=
  ⟨⟨f.core.fragment, fun j => ((Fintype.equivFin (σ ⊕ τ)).symm j).elim
    (fun i => Fin.castLE (Nat.le_add_right _ _) (Fintype.equivFin σ i))
    (fun i => f.core.wires (Fintype.equivFin τ i))⟩⟩

@[simp] theorem withInput_size (f : Frame σ τ) : f.withInput.size = f.size := rfl

@[simp] theorem withInput_eval_inl (f : Frame σ τ) (x : σ → Bool) (i : σ) :
    f.withInput.eval x (.inl i) = x i := by
  simp [withInput, eval, CircuitBatch.Frame.eval, CircuitBatch.Fragment.evalWires_input]

@[simp] theorem withInput_eval_inr (f : Frame σ τ) (x : σ → Bool) (i : τ) :
    f.withInput.eval x (.inr i) = f.eval x i := by
  simp [withInput, eval, CircuitBatch.Frame.eval]

/-- Designate a live wire as the output of the AND/NOT transcript circuit. -/
noncomputable def circuitSize (f : Frame σ τ) (out : τ) : ℕ :=
  CookCircuit.transcriptSize (f.core.toCircuit (Fintype.equivFin τ out))

/-- Compile one selected output of the gate fragment as a single-output Boolean transcript
circuit. -/
noncomputable def circuit (f : Frame σ τ) (out : τ) :
    BooleanTranscript.Circuit σ (f.circuitSize out) :=
  CookCircuit.toTranscriptWith (f.core.toCircuit (Fintype.equivFin τ out))
    (Sum.inl ∘ (Fintype.equivFin σ).symm)

@[simp] theorem circuit_eval (f : Frame σ τ) (out : τ) (x : σ → Bool) :
    (f.circuit out).eval x = f.eval x out :=
  CookCircuit.toTranscriptWith_eval _ _ _

theorem circuitSize_le (f : Frame σ τ) (out : τ) : f.circuitSize out ≤ 4 * f.size :=
  CookCircuit.toTranscript_size_le _

end Frame
end VerifierNetwork

end VPVNP
end Computability
end OAI
