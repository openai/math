import OAI.Computability.VPVNP.BooleanTranscript
import OAI.Computability.VPVNP.CircuitComposition
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin

namespace OAI
/-! # Substitution into a Boolean gate transcript

The input circuits are laid out consecutively and each runs once. The outer
circuit then refers to their designated outputs anywhere it uses those inputs.
-/

namespace ThreeFlat.Diagonal.TraceCompose

open Computability.VPVNP (Ref)
open Computability.VPVNP.BooleanTranscript

abbrev Packet (σ : Type*) := (n : ℕ) × Circuit σ n

variable {σ τ : Type*} {n m k : ℕ}

private theorem read_reindex (f : Fin n → Fin m) (r : Ref Bool σ n)
    (x : σ → Bool) (w : Fin m → Bool) :
    (r.reindex f).read id x w = r.read id x (w ∘ f) := by cases r <;> rfl

private def relocate (v : τ → Ref Bool σ n) : Ref Bool τ m → Ref Bool σ (n+m)
  | .const b => .const b
  | .var i => (v i).reindex (Fin.castAdd m)
  | .gate j => .gate (Fin.natAdd n j)

private theorem read_relocate (v : τ → Ref Bool σ n) (r : Ref Bool τ m)
    (x : σ → Bool) (w : Fin (n+m) → Bool) :
    (relocate v r).read id x w =
      r.read id (fun i => (v i).read id x (w ∘ Fin.castAdd m)) (w ∘ Fin.natAdd n) := by
  cases r with
  | const | gate => rfl
  | var i => exact read_reindex _ _ _ _

private def gate (v : τ → Ref Bool σ n) : Gate τ m → Gate σ (n+m)
  | .and a b => .and (relocate v a) (relocate v b)
  | .not a => .not (relocate v a)

private theorem gate_eval (v : τ → Ref Bool σ n) (g : Gate τ m) (x : σ → Bool)
    (w : Fin (n+m) → Bool) :
    (gate v g).eval x w = g.eval (fun i => (v i).read id x (w ∘ Fin.castAdd m))
      (w ∘ Fin.natAdd n) := by
  cases g <;> simp [gate, Gate.eval, read_relocate]

private def splice (p : Program σ n) (v : τ → Ref Bool σ n) :
    {m : ℕ} → Program τ m → Program σ (n + m)
  | _, .nil => p
  | _, .snoc q g => .snoc (splice p v q) (gate v g)

private theorem run_left (p : Program σ n) (v : τ → Ref Bool σ n)
    (q : Program τ m) (x : σ → Bool) :
    (splice p v q).run x ∘ Fin.castAdd m = p.run x := by
  funext i
  induction q with
  | nil => rfl
  | snoc q g ih =>
    simp only [Function.comp_apply, splice, Program.run, ← Fin.castSucc_castAdd,
      Fin.snoc_castSucc]
    exact ih

private theorem run_right (p : Program σ n) (v : τ → Ref Bool σ n)
    (q : Program τ m) (x : σ → Bool) :
    (splice p v q).run x ∘ Fin.natAdd n = q.run (fun i => (v i).read id x (p.run x)) := by
  induction q with
  | nil => funext i; exact i.elim0
  | snoc q g ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Function.comp_apply, splice, Program.run, Fin.natAdd_last, Fin.snoc_last,
        gate_eval, run_left, ih]
      exact Fin.snoc_last ..
    · simpa only [Function.comp_apply, splice, Program.run, Fin.natAdd_castSucc,
        Fin.snoc_castSucc] using congrFun ih j

structure Batch (σ ι : Type*) where
  size : ℕ
  program : Program σ size
  port : ι → Ref Bool σ size

def Batch.eval {ι : Type*} (b : Batch σ ι) (x : σ → Bool) (i : ι) : Bool :=
  (b.port i).read id x (b.program.run x)

private def plug {ι : Type*} (b : Batch σ ι) (v : τ → ι) (c : Circuit τ m) :
    Circuit σ (b.size+m) where
  program := splice b.program (b.port ∘ v) c.program
  output := relocate (b.port ∘ v) c.output

private theorem plug_eval {ι : Type*} (b : Batch σ ι) (v : τ → ι) (c : Circuit τ m)
    (x : σ → Bool) :
    (plug b v c).eval x = c.eval (b.eval x ∘ v) := by
  simp only [plug, Circuit.eval, read_relocate, run_left, run_right]
  rfl

private def append (b : Batch σ (Fin k)) (c : Packet σ) : Batch σ (Fin (k + 1)) where
  size := b.size + c.1
  program := splice b.program Ref.var c.2.program
  port := Fin.snoc (fun i => (b.port i).reindex (Fin.castAdd c.1)) (relocate Ref.var c.2.output)

private theorem append_eval (b : Batch σ (Fin k)) (c : Packet σ) (x : σ → Bool) :
    (append b c).eval x = Fin.snoc (b.eval x) (c.2.eval x) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Batch.eval, append, Fin.snoc_last, read_relocate, run_left, run_right]
    rfl
  · simp only [Batch.eval, append, Fin.snoc_castSucc, read_reindex, run_left]

def gather : {k : ℕ} → (Fin k → Packet σ) → Batch σ (Fin k)
  | 0, _ => ⟨0, .nil, Fin.elim0⟩
  | k+1, f => append (gather (fun i => f i.castSucc)) (f (Fin.last k))

theorem gather_size (f : Fin k → Packet σ) :
    (gather f).size = ∑ i, (f i).1 := by
  induction k with
  | zero => simp [gather]
  | succ k ih => simp only [gather, append, ih, Fin.sum_univ_castSucc]

theorem gather_eval (f : Fin k → Packet σ) (x : σ → Bool) (i : Fin k) :
    (gather f).eval x i = (f i).2.eval x := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    rw [gather, append_eval]
    exact Fin.lastCases (by simp) (fun j => by simp [ih]) i

/-- Emit each input subcircuit and then the outer gates, substituting every
named input by its corresponding wire in the common transcript. -/
noncomputable def substituteFintype [Fintype τ] (input : τ → Packet σ) (outer : Circuit τ n) :
    Packet σ :=
  let e := Fintype.equivFin τ
  let b := gather (input ∘ e.symm)
  ⟨b.size+n, plug b e outer⟩

@[simp] theorem substituteFintype_eval [Fintype τ] (input : τ → Packet σ)
    (outer : Circuit τ n) (x : σ → Bool) :
    (substituteFintype input outer).2.eval x = outer.eval (fun i => (input i).2.eval x) := by
  simp only [substituteFintype, plug_eval, Function.comp_def, gather_eval]
  apply congrArg outer.eval
  funext i
  exact congrArg (fun t => (input t).2.eval x) ((Fintype.equivFin τ).symm_apply_apply i)

@[simp] theorem substituteFintype_size [Fintype τ] (input : τ → Packet σ)
    (outer : Circuit τ n) :
    (substituteFintype input outer).1 = (∑ i, (input i).1) + n := by
  change (gather (input ∘ (Fintype.equivFin τ).symm)).size + n = _
  rw [gather_size]
  congr 1
  exact Equiv.sum_comp (Fintype.equivFin τ).symm (fun i => (input i).1)

end ThreeFlat.Diagonal.TraceCompose

end OAI
