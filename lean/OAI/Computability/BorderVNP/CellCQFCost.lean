import OAI.Computability.BorderVNP.CellPrivateProcedure
import OAI.Computability.QuantumFactoring.BitStackFrames
import OAI.Computability.QuantumFactoring.BitStackComposition

/-! # Input-specific execution time of private Boolean-stack subroutines

The polynomial bundled with a procedure bounds every input of the specified length.
For the cell compiler, composition is charged at the actual intermediate words and only
the selected branch is executed. These bounds refer to runs of the installed program.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackProcedure

open _root_.OAI.ExactQuantumFactoring _root_.OAI.ExactQuantumFactoring.BitStackProgram
open _root_.OAI.ExactQuantumFactoring.BitStackProgram.Procedure

variable {A B : Type} {ea : A → List Bool} {eb : B → List Bool} {f g : A → B}

/-- A clean execution of a procedure on one particular encoded input. -/
abbrev Ticks (p : Procedure ea eb f) (a : A) (t : ℕ) : Prop :=
  Runs p.program (singletonStore p.input (ea a)) (singletonStore p.output (eb (f a))) t

private theorem exists_ticks (p : Procedure ea eb f) (a : A) : ∃ t, Ticks p a t := by
  obtain ⟨t,_,ht⟩ := p.runs a
  exact ⟨t,ht⟩

/-- Actual number of finite-program transitions on this specific input. -/
noncomputable def cost (p : Procedure ea eb f) (a : A) : ℕ := by
  classical
  exact Nat.find (exists_ticks p a)

/-- The input-specific clock always comes with a clean operational derivation. -/
theorem ticks_cost (p : Procedure ea eb f) (a : A) : Ticks p a (cost p a) := by
  classical
  exact Nat.find_spec (exists_ticks p a)

/-- Any derived operational run is an upper bound for the input-specific clock. -/
theorem cost_le_of_ticks (p : Procedure ea eb f) {a : A} {t : ℕ} (h : Ticks p a t) : cost p a ≤ t := by
  classical
  exact Nat.find_min' (exists_ticks p a) h

/-- The declared worst-case polynomial remains available for genuinely small primitive inputs. -/
theorem cost_le_bound (p : Procedure ea eb f) (a : A) : cost p a ≤ p.bound.eval (ea a).length := by
  obtain ⟨t,ht,run⟩ := p.runs a
  exact (cost_le_of_ticks p run).trans ht

/-- Reuse the identical finite program on a single specified argument. The polynomial
certificate is the constant true time of this input. This permits reusing checked wrapper
bounds locally while charging the actual length of every intermediate word. -/
noncomputable def atInput (p : Procedure ea eb f) (a : A) :
    Procedure (fun _ : Unit => ea a) (fun _ : Unit => eb (f a)) (id : Unit → Unit) where
  K := p.K
  finiteK := p.finiteK
  decideK := p.decideK
  input := p.input
  output := p.output
  program := p.program
  bound := Polynomial.C (cost p a)
  runs _ := ⟨cost p a, by simp, ticks_cost p a⟩

/-- Rewriting the denotation leaves the installed procedure and exact clock untouched. -/
@[simp] theorem cost_congrFun (p : Procedure ea eb f) (h : ∀ a, f a = g a) (a : A) :
    cost (p.congrFun h) a = cost p a := by
  apply le_antisymm
  · apply cost_le_of_ticks
    change Runs p.program _ (singletonStore p.output (eb (g a))) _
    rw [← h a]
    exact ticks_cost p a
  · apply cost_le_of_ticks
    have ht := ticks_cost (p.congrFun h) a
    change Runs p.program _ (singletonStore p.output (eb (g a))) _ at ht
    rwa [← h a] at ht

/-- The actual word produced by the first procedure is what the composition copies.
All other transition counts add. -/
theorem cost_comp {C : Type} {ec : C → List Bool} {g : B → C} (q : Procedure eb ec g)
    (p : Procedure ea eb f) (a : A) :
    cost (q.comp p) a ≤ cost q (f a) + (4*(eb (f a)).length+2) + cost p a := by
  have hp := (ticks_cost p a).relabel (joinLeft p.K q.K) (fun _ => [])
  have hq := (ticks_cost q (f a)).relabel (joinRight p.K q.K) (fun _ => [])
  simp only [overlay_singleton] at hp hq
  have move := moveWord_runs (K := p.K ⊕ (q.K ⊕ Unit)) (Sum.inl p.output) (Sum.inr (Sum.inl q.input))
    (Sum.inr (Sum.inr ())) (by simp) (by simp) (by simp) (eb (f a))
  exact cost_le_of_ticks (q.comp p) (Runs.seq hp (Runs.seq move hq))

end StackProcedure

end BorderVNP
end Computability

namespace ExactQuantumFactoring.BitStackProgram.Procedure

export OAI.Computability.BorderVNP.StackProcedure (
  Ticks
  cost
  ticks_cost
  cost_le_of_ticks
  cost_le_bound
  atInput
  cost_congrFun
  cost_comp)

end ExactQuantumFactoring.BitStackProgram.Procedure
end OAI
