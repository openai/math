import OAI.Optimization.LinearProgramming.Recovery.WitnessProgramData
import OAI.Optimization.LinearProgramming.Recovery.ConstraintBits
import OAI.Optimization.LinearProgramming.Recovery.WitnessSolveSize
import OAI.Optimization.LinearProgramming.Geometry.GramEncoding
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring

/-! The anchor row, the right-hand side, and all rows produced by support masking
have the same entry-height bound as the original rectangular system. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessSolve

open RAM Polynomial
open OAI.Optimization.LinearProgramming.Geometry

theorem inputBits_le {r s : ℕ} (T : Matrix (Fin r) (Fin s) ℚ) (e : ℕ)
    (entries : ∀ i j, ratBits (T i j) ≤ e) :
    totalBits (encodedGramInput T) ≤ (r*s)*e := by
  let xs := (encodedGramInput T).map ratBits
  have hv (x : ℕ) (hx : x ∈ xs) : x ≤ e := by
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    rw [encodedGramInput] at hq
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    exact entries _ _
  have h := List.sum_le_length_nsmul xs e hv
  simpa [totalBits,xs,nsmul_eq_mul] using h

theorem augmented_entries {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (e : ℕ) (ha : ∀ i j, ratBits (A i j) ≤ e) (hb : ∀ i, ratBits (b i) ≤ e) :
    ∀ i j, ratBits (Elimination.augmentedRows A b i j) ≤ e := by
  intro i j
  refine Fin.cases (motive := fun row => ratBits (Elimination.augmentedRows A b row j) ≤ e)
    ?_ (fun k => ?_) i
  · exact hb j
  · exact ha j k

theorem normalized_height_bound (h n e : ℕ) (T : Matrix (Fin (n+1)) (Fin (h+n+1)) ℚ)
    (entries : ∀ i j, ratBits (T i j) ≤ e) :
    solverHeight (totalBits (encodedGramInput T)) ≤ heightPolynomial.eval (h+n+e) := by
  have volume : (n+1)*(h+n+1)*e ≤ (h+n+e+1)^3 := by
    calc
      _ ≤ (h+n+e+1)*(h+n+e+1)*(h+n+e+1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      _ = _ := by ring
  have bits := (inputBits_le T e entries).trans volume
  have pow := Nat.pow_le_pow_left (Nat.add_le_add_right bits 1) 6
  simp only [heightPolynomial,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat]
  unfold solverHeight
  omega

end WitnessSolve
end Recovery
end LinearProgramming
end Optimization
end OAI

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessProgram

open RAM
open OAI.Optimization.LinearProgramming.Geometry

theorem tableau_height {h n : ℕ} (E : Matrix (Fin h) (Fin n) ℚ) (S : Finset (Fin n))
    (hn : 0<n) (e : ℕ) (three : 3 ≤ e) (entries : ∀ i j, ratBits (E i j) ≤ e) :
    ∀ i j, ratBits (tableau E S hn i j) ≤ e := by
  change ∀ i j, ratBits (Elimination.augmentedRows (system E S hn) (rhs h n) i j) ≤ e
  apply WitnessSolve.augmented_entries
  · intro i j
    refine Fin.cases (motive := fun row => ratBits (system E S hn row j) ≤ e) ?_ (fun a => ?_) i
    · change ratBits (if j=⟨0,hn⟩ then (1:ℚ) else 0) ≤ e
      split <;> exact three
    · exact maskedEquations_bits E S entries three a j
  · intro i
    exact Fin.cases (motive := fun j => ratBits (rhs h n j) ≤ e) three (fun _ => three) i

theorem solver_height {h n : ℕ} (E : Matrix (Fin h) (Fin n) ℚ) (S : Finset (Fin n))
    (hn : 0<n) (e : ℕ) (three : 3 ≤ e) (entries : ∀ i j, ratBits (E i j) ≤ e) :
    WitnessSolve.solverHeight (totalBits (encodedGramInput (tableau E S hn))) ≤
      WitnessSolve.heightPolynomial.eval (h+n+e) :=
  WitnessSolve.normalized_height_bound h n e _ (tableau_height E S hn e three entries)

end WitnessProgram
end Recovery
end LinearProgramming
end Optimization
end OAI
