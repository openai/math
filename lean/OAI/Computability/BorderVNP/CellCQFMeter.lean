import OAI.Computability.BorderVNP.CellCQFCost
import OAI.Computability.QuantumFactoring.BitStackWords
import OAI.Computability.QuantumFactoring.BitStackBasicProcedures

/-! # Actual input, output, and running costs of a cell compiler subroutine

A composition only moves the intermediate word produced on this input. Charging
its length beside the operational time lets fixed command constructors add these
quantities without evaluating a worst-case clock at another worst-case clock.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackProcedure

open _root_.OAI.ExactQuantumFactoring _root_.OAI.ExactQuantumFactoring.BitStackProgram
open _root_.OAI.ExactQuantumFactoring.BitStackProgram.Procedure

variable {A B C : Type} {ea : A → List Bool} {eb : B → List Bool} {ec : C → List Bool}
variable {f f' : A → B} {g : B → C}

/-- Input-specific operational cost together with the lengths of the two words
physically handled by the caller. -/
noncomputable def meter (p : Procedure ea eb f) (a : A) :=
  p.cost a + (ea a).length + (eb (f a)).length + 1

/-- The measured clean run fits in the charge for the procedure on that input. -/
theorem cost_le_meter (p : Procedure ea eb f) (a : A) : p.cost a ≤ meter p a := by
  unfold meter; omega

/-- The input and output words, with one separator, fit in the charge. -/
theorem words_le_meter (p : Procedure ea eb f) (a : A) :
    (ea a).length + (eb (f a)).length + 1 ≤ meter p a := by unfold meter; omega

/-- Changing the mathematical presentation of the same output changes no cost. -/
@[simp] theorem meter_congrFun (p : Procedure ea eb f) (h : ∀ a, f a = f' a) (a : A) :
    meter (p.congrFun h) a = meter p a := by
  simp only [meter,cost_congrFun,h]

/-- A sequential call pays the two actual child charges and a linear copy of the
particular intermediate word. -/
theorem meter_comp (q : Procedure eb ec g) (p : Procedure ea eb f) (a : A) :
    meter (q.comp p) a ≤ 6*(meter p a + meter q (f a)) := by
  have h := cost_comp q p a
  simp only [meter,Function.comp_apply]
  omega

/-- The identity program already has a single native step. -/
theorem meter_identity (ea : A → List Bool) (a : A) :
    meter (identity ea) a ≤ 2*((ea a).length+1) := by
  have h := (identity ea).cost_le_bound a
  change _ ≤ (1 : Polynomial ℕ).eval _ at h
  simp only [Polynomial.eval_one] at h
  simp only [meter,id_eq]
  omega

/-- Printing a constant clears the actual input and writes its fixed output. -/
theorem meter_constant (ea : A → List Bool) (eb : B → List Bool) (b : B) (a : A) :
    meter (constant ea eb b) a ≤ 3*((ea a).length+(eb b).length+1) := by
  have h := (constant ea eb b).cost_le_bound a
  change _ ≤ (Polynomial.C 2*Polynomial.X+Polynomial.C ((eb b).length+2)).eval _ at h
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] at h
  simp only [meter]; omega

/-- Projection parses the first quoted field and clears the trailing field. -/
theorem meter_first (ea : A → List Bool) (eb : B → List Bool) (x : A × B) :
    meter (first ea eb) x ≤ 10*((prodCode ea eb x).length+1) := by
  have h := (first ea eb).cost_le_bound x
  change _ ≤ (Polynomial.C 7*Polynomial.X+Polynomial.C 7).eval _ at h
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    prodCode,pairBits_length] at h
  simp only [meter,prodCode,pairBits_length]
  omega

/-- Swapping a pair only parses and requotes its component words. -/
theorem meter_swap (ea : A → List Bool) (eb : B → List Bool) (x : A × B) :
    meter (swap ea eb) x ≤ 20*((prodCode ea eb x).length+1) := by
  have h := (swap ea eb).cost_le_bound x
  change _ ≤ (Polynomial.C 7*Polynomial.X+Polynomial.C 11).eval _ at h
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    prodCode,pairBits_length] at h
  simp only [meter,prodCode,pairBits_length,Prod.fst_swap,Prod.snd_swap]
  omega

/-- The second projection is the installed swap followed by the first projection. -/
theorem meter_second (ea : A → List Bool) (eb : B → List Bool) (x : A × B) :
    meter (second ea eb) x ≤ 300*((prodCode ea eb x).length+1) := by
  unfold second
  rw [meter_congrFun]
  apply (meter_comp _ _ x).trans
  have h := meter_first eb ea x.swap
  have s := meter_swap ea eb x
  simp only [prodCode,pairBits_length,Prod.fst_swap,Prod.snd_swap] at h s ⊢
  omega

/-- Concatenating two raw words has linear operational and framing cost. -/
theorem meter_append (x : List Bool × List Bool) :
    meter append x ≤ 16*((prodCode id id x).length+1) := by
  have h := append.cost_le_bound x
  change _ ≤ (Polynomial.C 11*Polynomial.X+Polynomial.C 8).eval _ at h
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    prodCode,pairBits_length,id_eq] at h
  simp only [meter,prodCode,pairBits_length,id_eq,List.length_append]
  omega

/-- Viewing the source through a fixed function preserves the original bit-level program. -/
@[simp] theorem meter_precompose {D : Type} (p : Procedure ea eb f) (q : D → A) (a : D) :
    meter (p.precompose q) a = meter p (q a) := by
  have h : (p.precompose q).cost a = p.cost (q a) := by
    exact le_antisymm ((p.precompose q).cost_le_of_ticks (p.ticks_cost (q a)))
      (p.cost_le_of_ticks ((p.precompose q).ticks_cost a))
  simp only [meter,h]

/-- Changing the mathematical result while retaining the exact same encoded word
preserves the actual charge. -/
@[simp] theorem meter_result {u : A → C} (p : Procedure ea eb f)
    (h : ∀ a, eb (f a) = ec (u a)) (a : A) :
    meter (p.result h) a = meter p a := by
  have hk : (p.result h).cost a = p.cost a := by
    apply le_antisymm
    · apply cost_le_of_ticks
      change Runs p.program _ (singletonStore p.output (ec (u a))) _
      rw [← h a]
      exact p.ticks_cost a
    · apply cost_le_of_ticks
      have hp := (p.result h).ticks_cost a
      change Runs p.program _ (singletonStore p.output (ec (u a))) _ at hp
      rwa [← h a] at hp
  simp only [meter,hk,h]

end StackProcedure

end BorderVNP
end Computability

namespace ExactQuantumFactoring.BitStackProgram.Procedure

export OAI.Computability.BorderVNP.StackProcedure (
  meter
  cost_le_meter
  words_le_meter
  meter_congrFun
  meter_comp
  meter_identity
  meter_constant
  meter_first
  meter_swap
  meter_second
  meter_append
  meter_precompose
  meter_result)

end ExactQuantumFactoring.BitStackProgram.Procedure
end OAI
