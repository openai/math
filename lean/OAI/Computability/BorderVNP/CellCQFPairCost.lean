import OAI.Computability.BorderVNP.CellCQFCost
import OAI.Computability.QuantumFactoring.BitStackChoice
import OAI.Computability.QuantumFactoring.BitStackWords
import OAI.Computability.QuantumFactoring.BitStackBasicProcedures

/-! # Actual costs of fixed Boolean-stack pairing and projections

Repricing a subprocedure on one input leaves its finite program identical. The installed
pair compiler consequently has an affine bound in the input length and the two real
subroutine times. Composition copies only the actual intermediate word.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackProcedure

open _root_.OAI.ExactQuantumFactoring _root_.OAI.ExactQuantumFactoring.BitStackProgram
open _root_.OAI.ExactQuantumFactoring.BitStackProgram.Procedure

variable {A B C : Type} {ea : A → List Bool} {eb : B → List Bool} {ec : C → List Bool}
  {f : A → B} {g : A → C}

/-- An actual clean execution bounds the number of bits appearing on its output port. -/
theorem output_length_le_cost (p : Procedure ea eb f) (a : A) :
    (eb (f a)).length ≤ (ea a).length + p.cost a := by
  have h := (p.ticks_cost a).length_le p.output
  simp only [singletonStore,Function.update_self] at h
  by_cases same : p.output = p.input
  · simpa only [same,Function.update_self] using h
  · simp only [Function.update_of_ne same,List.length_nil,Nat.zero_add] at h
    omega

/-- Calling the first component of a pair while the second word is retained in place
charges the original runtime, the decoded input and the returned word. -/
theorem cost_left (p : Procedure ea eb f) (ec : C → List Bool) (x : A × C) :
    (p.left ec).cost x ≤ 14*(prodCode ea ec x).length+8*p.cost x.1+11 := by
  obtain ⟨t,ht,run⟩ := ((p.atInput x.1).left (fun _ : Unit => ec x.2)).runs ((),())
  apply ((p.left ec).cost_le_of_ticks run).trans
  change t ≤ (Polynomial.C 14*Polynomial.X + Polynomial.C 8*Polynomial.C (p.cost x.1)+Polynomial.C 11).eval
    (prodCode ea ec x).length at ht
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using ht

private theorem cost_swap (ea : A → List Bool) (eb : B → List Bool) (x : A × B) :
    (swap ea eb).cost x ≤ 7*(prodCode ea eb x).length+11 := by
  apply ((swap ea eb).cost_le_bound x).trans
  change (Polynomial.C 7*Polynomial.X+Polynomial.C 11).eval _ ≤ _
  simp

/-- Acting separately on two words by the native split, swap, and join routines pays an
affine amount in the original word lengths and the two particular executions. -/
theorem cost_parallel {D : Type} {ed : D → List Bool} {h : C → D}
    (p : Procedure ea eb f) (q : Procedure ec ed h) (a : A) (c : C) :
    (p.parallel q).cost (a,c) ≤ 1000*((ea a).length+(ec c).length+p.cost a+q.cost c+1) := by
  unfold parallel
  rw [cost_congrFun]
  have hl := cost_left p ec (a,c)
  have hm := cost_comp (swap eb ec) (p.left ec) (a,c)
  have hr := cost_comp (q.left eb) ((swap eb ec).comp (p.left ec)) (a,c)
  have hs := cost_comp (swap ed eb) ((q.left eb).comp ((swap eb ec).comp (p.left ec))) (a,c)
  have hsl := cost_swap eb ec (f a,c)
  have hsr := cost_swap ed eb (h c,f a)
  have hrl := cost_left q eb (c,f a)
  have ha := output_length_le_cost p a
  have hc := output_length_le_cost q c
  simp only [prodCode,pairBits_length,Function.comp_apply,Prod.swap_prod_mk] at *
  omega

/-- The two real invocations plus the finite pairing wrapper have linear total cost. -/
theorem cost_pair (p : Procedure ea eb f) (q : Procedure ea ec g) (a : A) :
    (p.pair q).cost a ≤ 10^9*(p.cost a+q.cost a+(ea a).length+1) := by
  unfold pair
  apply (cost_comp _ _ a).trans
  have hp := cost_parallel p q a a
  have hd := (duplicate ea).cost_le_bound a
  change _ ≤ (Polynomial.C 14*Polynomial.X+Polynomial.C 8).eval _ at hd
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] at hd
  simp only [prodCode,pairBits_length]
  omega

/-- Identity returns its input immediately. -/
theorem cost_identity (ea : A → List Bool) (a : A) : (identity ea).cost a ≤ 1 := by
  simpa [identity] using (identity ea).cost_le_bound a

/-- Copying out the first component and clearing the second costs linearly many transitions. -/
theorem cost_first (ea : A → List Bool) (eb : B → List Bool) (x : A × B) :
    (first ea eb).cost x ≤ 16*((prodCode ea eb x).length+1) := by
  apply ( (first ea eb).cost_le_bound x).trans
  simp only [first,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  omega

/-- A second-component projection swaps the actual pair and copies its actual swapped encoding. -/
theorem cost_second (ea : A → List Bool) (eb : B → List Bool) (x : A × B) :
    (second ea eb).cost x ≤ 64*((prodCode ea eb x).length+1) := by
  unfold second
  rw [cost_congrFun]
  apply (cost_comp _ _ x).trans
  have hf := cost_first eb ea x.swap
  have hs := (swap ea eb).cost_le_bound x
  simp only [swap,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    prodCode,pairBits_length,Prod.fst_swap,Prod.snd_swap] at *
  omega

/-- A constant word is printed after clearing the actual argument word. -/
theorem cost_constant (ea : A → List Bool) (eb : B → List Bool) (b : B) (a : A) :
    (constant ea eb b).cost a ≤ 16*((ea a).length+(eb b).length+1) := by
  apply ( (constant ea eb b).cost_le_bound a).trans
  simp only [constant,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  omega

/-- Concatenating the two encoded words costs linearly many transitions. -/
theorem cost_append (x : List Bool × List Bool) :
    append.cost x ≤ 16*((prodCode id id x).length+1) := by
  apply ( append.cost_le_bound x).trans
  simp only [append,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  omega

/-- Reinterpreting the domain of a procedure preserves each individual running time. -/
@[simp] theorem cost_precompose (p : Procedure ea eb f) (h : C → A) (c : C) :
    (p.precompose h).cost c = p.cost (h c) := by
  apply le_antisymm
  · exact cost_le_of_ticks _ (p.ticks_cost (h c))
  · exact cost_le_of_ticks _ ((p.precompose h).ticks_cost c)

/-- Changing only the proof of the input and output encodings has no operational charge. -/
@[simp] theorem cost_congrEncoding (p : Procedure ea eb f) {ea' : A → List Bool} {eb' : B → List Bool}
    (ha : ∀ a, ea a = ea' a) (hb : ∀ b, eb b = eb' b) (a : A) :
    (p.congrEncoding ha hb).cost a = p.cost a := by
  have iff (t : ℕ) : (p.congrEncoding ha hb).Ticks a t ↔ p.Ticks a t := by
    change Runs p.program (singletonStore p.input (ea' a)) (singletonStore p.output (eb' (f a))) t ↔ _
    rw [← ha a,← hb (f a)]
  exact le_antisymm (cost_le_of_ticks _ ((iff _).mpr (p.ticks_cost a)))
    (cost_le_of_ticks _ ((iff _).mp ((p.congrEncoding ha hb).ticks_cost a)))

/-- Reinterpreting a mathematical result with the same exact output word costs nothing. -/
@[simp] theorem cost_result (p : Procedure ea eb f) (h : ∀ a, eb (f a) = ec (g a)) (a : A) :
    (p.result h).cost a = p.cost a := by
  have iff (t : ℕ) : (p.result h).Ticks a t ↔ p.Ticks a t := by
    change Runs p.program _ (singletonStore p.output (ec (g a))) t ↔ _
    rw [← h a]
    rfl
  exact le_antisymm (cost_le_of_ticks _ ((iff _).mpr (p.ticks_cost a)))
    (cost_le_of_ticks _ ((iff _).mp ((p.result h).ticks_cost a)))

end StackProcedure

end BorderVNP
end Computability

namespace ExactQuantumFactoring.BitStackProgram.Procedure

export OAI.Computability.BorderVNP.StackProcedure (
  output_length_le_cost
  cost_left
  cost_parallel
  cost_pair
  cost_identity
  cost_first
  cost_second
  cost_constant
  cost_append
  cost_precompose
  cost_congrEncoding
  cost_result)

end ExactQuantumFactoring.BitStackProgram.Procedure
end OAI
