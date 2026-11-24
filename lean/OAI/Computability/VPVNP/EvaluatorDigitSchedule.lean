import OAI.Computability.VPVNP.Evaluator
import OAI.Computability.VPVNP.EvaluatorDigitRepeat
import Mathlib.Data.List.FinRange

/-! # The compact digit schedule of the finite-algebra evaluator

After radix conversion, each column contains one base-`Q` digit for every
label. Processing the columns most significant first produces the same list of
linear maps as the paper's monomial program. Each column starts with a
Frobenius step, then repeats label multiplication according to the binary
counter on that label.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorDigitSchedule

variable {t : ℕ}

/-- The two types of matrix queries made by the monomial evaluator. -/
inductive Action (t : ℕ) where
  | frobenius
  | label (i : Fin t)
  deriving DecidableEq, Fintype

/-- Actions emitted by the digit counters at one position. -/
def emit (d : Fin t → ℕ) : List (Action t) :=
  .frobenius :: (List.finRange t).flatMap fun i => List.replicate (d i) (.label i)

/-- A compact schedule of digit columns, before expanding any multiplicities. -/
def columns (Q : ℕ) : ℕ → (Fin t → ℕ) → List (Fin t → ℕ)
  | 0, _ => []
  | w+1, e => columns Q w (fun i => e i / Q) ++ [fun i => e i % Q]

theorem columns_length (Q w : ℕ) (e : Fin t → ℕ) : (columns Q w e).length = w := by
  induction w generalizing e <;> simp [columns, *]

/-- The radix conversion may also compute each column by its position,
using one fixed order for the input labels. -/
theorem columns_eq (Q w : ℕ) (e : Fin t → ℕ) :
    columns Q w e = (List.range w).reverse.map (fun j i => e i / Q^j % Q) := by
  induction w generalizing e with
  | zero => rfl
  | succ w ih =>
    rw [columns, ih]
    have h := List.range_succ_eq_map (n := w)
    rw [h, List.reverse_cons, List.map_append]
    simp only [List.map_cons, List.map_nil, pow_zero, Nat.div_one, ← List.map_reverse, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j _
    funext i
    simp [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

/-- Every digit lies below the cardinality of the base field. -/
theorem columns_digit_lt {Q : ℕ} (hQ : 0 < Q) (w : ℕ) (e : Fin t → ℕ)
    {d : Fin t → ℕ} (hd : d ∈ columns Q w e) (i : Fin t) : d i < Q := by
  rw [columns_eq] at hd
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hd
  exact Nat.mod_lt _ hQ

variable (K : Type*) [Field K] [Fintype K] {A : Type*} [CommRing A] [Algebra K A]

/-- Interpret the streamed query identifier as a linear operator. -/
def actionMap (X : Fin t → A) : Action t → A →ₗ[K] A
  | .frobenius => (FiniteField.frobeniusAlgHom K A).toLinearMap
  | .label i => LinearMap.mulLeft K (X i)

theorem map_emit (X : Fin t → A) (d : Fin t → ℕ) :
    (emit d).map (actionMap K X) = Evaluator.digitSteps K X d := by
  simp [emit, actionMap, Evaluator.digitSteps, List.map_flatMap]

/-- A column-by-column streaming traversal produces the precise chronological
sequence of Frobenius and multiplication queries in equation (8.2). -/
theorem actions_eq_digitProgram (X : Fin t → A) (w : ℕ) (e : Fin t → ℕ) :
    ((columns (Fintype.card K) w e).flatMap emit).map (actionMap K X) =
      Evaluator.digitProgram K X w e := by
  induction w generalizing e with
  | zero => rfl
  | succ w ih =>
    simp only [columns, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_append, ih, map_emit, Evaluator.digitProgram]

/-- A compact schedule uses `w*t` digits, and executes at most one Frobenius
and `t*(Q-1)` label multiplications per column. -/
theorem action_count_le (w : ℕ) (e : Fin t → ℕ) :
    ((columns (Fintype.card K) w e).flatMap emit).length ≤ w * (1+t*(Fintype.card K-1)) := by
  let X : Fin t → K := fun _ => 0
  simpa only [← actions_eq_digitProgram K X w e, List.length_map] using
    Evaluator.digitProgram_length_le K X w e

end EvaluatorDigitSchedule

end VPVNP
end Computability
end OAI
