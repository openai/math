import OAI.ThreeFlat.Diagonal.ShrinkLayout

namespace OAI
/-! # Choosing the less expensive layout with integer comparisons

After multiplying the six-party reciprocal masses by 80/31 their eight
integer coefficients are 10, 10, 20, 20, 6, 6, 5, 5. One uniform pass over
the motif records can therefore choose the physical layout exactly.
-/

namespace ThreeFlat.Diagonal.ShrinkMotif

open scoped BigOperators

def multiplier : Fin 8 → ℕ := ![10,10,20,20,6,6,5,5]

variable {M : Type*} [Fintype M]

def layoutCost (width : M → Fin 8 → ℕ) (b : Bool) : ℕ :=
  ∑ m, ∑ j : Fin 4, multiplier (survivor b j) * width m (survivor b j)^2

def chooseWidths (width : M → Fin 8 → ℕ) : Bool :=
  if layoutCost width false ≤ layoutCost width true then false else true

theorem layoutCost_eq (width : M → Fin 8 → ℕ) (b : Bool) :
    (layoutCost width b : ℝ) = (80/31)*retainedEnergy (fun m e => (width m e:ℝ)^2/supplyMass e) b := by
  unfold layoutCost retainedEnergy
  simp only [Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro j _
  generalize survivor b j = e
  fin_cases e <;> norm_num [multiplier,supplyMass] <;> ring

theorem chooseWidths_eq (width : M → Fin 8 → ℕ) :
    chooseWidths width = chooseLayout (fun m e => (width m e:ℝ)^2/supplyMass e) := by
  have eqv : layoutCost width false ≤ layoutCost width true ↔
      retainedEnergy (fun m e => (width m e:ℝ)^2/supplyMass e) false ≤
        retainedEnergy (fun m e => (width m e:ℝ)^2/supplyMass e) true := by
    rw [← Nat.cast_le (α := ℝ), layoutCost_eq, layoutCost_eq]
    exact mul_le_mul_iff_right₀ (by norm_num)
  simp only [chooseWidths,chooseLayout,eqv]

end ThreeFlat.Diagonal.ShrinkMotif

end OAI
