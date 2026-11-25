import OAI.Computability.NearSquareRoot.KernelBinaryQueryLift
import OAI.Computability.NearSquareRoot.KernelPassRational

/-! # Rational query action on the full compiled frequency row -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BinaryQuery
open OAI.LinearAlgebra.FiniteFourier KernelPass KernelNormalization Matrix Finset
noncomputable section

/-- Each paired column contributes two ordinary exponents. Adding the test
over the physical columns computes all the labels for the repair table. -/
def test (m u : ℕ) (c : Column (Arity m u)) (j : Fin m) : ZMod 2 :=
  ∑ t : Fin 2, exponent j (halves m u (letterAt c t))

variable {m u h : ℕ}

/-- Tensoring the diagonal signs multiplies their two-bit column contributions. -/
theorem packed_signature (j : Fin m) :
    lift h (diagonal fun ω => character (exponent j (halves m u ω))) =
      (diagonal (fun y : Addr (Arity m u) h => (-1 : ℚ)^((∑ t, test m u (y t)) j).val)).map
        (algebraMap ℚ ℂ) := by
  ext y x
  change (∏ k, diagonal (fun ω => character (exponent j (halves m u ω))) (expose h y k) (expose h x k)) = _
  by_cases e : y = x
  · subst x
    rw [Matrix.map_apply, diagonal_apply_eq]
    simp only [diagonal_apply_eq, character]
    rw [← digitPhase_sum, Fintype.sum_prod_type]
    simp only [Finset.sum_apply, test, digitPhase_apply, map_pow, map_neg, map_one]
    rfl
  · have notEq : expose h y ≠ expose h x := fun d => e ((expose h).injective d)
    obtain ⟨k, hk⟩ := Function.ne_iff.mp notEq
    rw [Matrix.map_apply, diagonal_apply_ne _ e, map_zero]
    exact prod_eq_zero (mem_univ k) (diagonal_apply_ne _ hk)

/-- The rational restriction is exact: it is the conjugate of the rational
sign diagonal by the self-inverse physical Walsh transform. -/
theorem rational_query (j : Fin m) : rationalLift h (query (u:=u) j) =
    Plan.walshMatrix (Arity m u) h *
      diagonal (fun y : Addr (Arity m u) h => (-1 : ℚ)^((∑ t, test m u (y t)) j).val) *
      Plan.walshMatrix (Arity m u) h := by
  let F := Plan.walshMatrix (Arity m u) h
  let D := diagonal (fun y : Addr (Arity m u) h => (-1 : ℚ)^((∑ t, test m u (y t)) j).val)
  let map := algebraMap ℚ ℂ
  have eq := packed_diagonalizes (u:=u) h j
  rw [packed_signature] at eq
  change F.map map * lift h (query (u:=u) j) = D.map map * F.map map at eq
  have FF : F.map map * F.map map = 1 := by
    rw [← Matrix.map_mul, Plan.walshMatrix_mul_self, Matrix.map_one _ (map_zero map) (map_one map)]
  have rat : lift h (query (u:=u) j) = (F*D*F).map map := by
    have z := congrArg (F.map map * ·) eq
    simpa only [Matrix.map_mul, ← mul_assoc, FF, one_mul] using z
  ext y x
  change rationalPart (lift h (query (u:=u) j) y x) = _
  rw [rat, Matrix.map_apply, rationalPart_cast]

theorem rational_diagonalizes (j : Fin m) :
    Plan.walshMatrix (Arity m u) h * rationalLift h (query (u:=u) j) =
      diagonal (fun y : Addr (Arity m u) h => (-1 : ℚ)^((∑ t, test m u (y t)) j).val) *
        Plan.walshMatrix (Arity m u) h := by
  rw [rational_query, ← mul_assoc, ← mul_assoc, Plan.walshMatrix_mul_self, one_mul]

theorem rational_frequency (j : Fin m) (v : Addr (Arity m u) h → ℚ) (y : Addr (Arity m u) h) :
    (Plan.walshMatrix (Arity m u) h *ᵥ (rationalLift h (query (u:=u) j) *ᵥ v)) y =
      (-1 : ℚ)^((∑ t, test m u (y t)) j).val * (Plan.walshMatrix (Arity m u) h *ᵥ v) y := by
  rw [Matrix.mulVec_mulVec, rational_diagonalizes, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]

/-- The full repaired product on arbitrary paired widths is conjugate to the
single rational product-of-signs diagonal of the frequency table. -/
theorem product_kernel (m u h : ℕ) :
    (Plan.walshMatrix (Arity m u) h *
      diagonal (fun y : Addr (Arity m u) h => ∏ j : Fin m, (-1 : ℚ)^((∑ c, test m u (y c)) j).val) *
      Plan.walshMatrix (Arity m u) h).map (algebraMap ℚ ℂ) =
        lift h (List.ofFn (query (m:=m) (u:=u))).prod := by
  let F := Plan.walshMatrix (Arity m u) h
  let c := algebraMap ℚ ℂ
  let v (j : Fin m) (y : Addr (Arity m u) h) := (-1 : ℚ)^((∑ t, test m u (y t)) j).val
  let D (l : List (Fin m)) := diagonal (fun y => (l.map (fun j => v j y)).prod)
  have go (l : List (Fin m)) :
      F.map c * lift h (l.map (query (u:=u))).prod = (D l).map c * F.map c := by
    induction l with
    | nil =>
      have done : D [] = 1 := by ext y x; simp [D, Matrix.one_apply]
      simp [done]
    | cons j l ih =>
      have ds : D (j::l) = diagonal (v j) * D l := by
        dsimp only [D]
        rw [diagonal_mul_diagonal]
        rfl
      have eq := packed_diagonalizes (u:=u) h j
      rw [packed_signature] at eq
      change F.map c * lift h (query (u:=u) j) = (diagonal (v j)).map c * F.map c at eq
      simp only [List.map_cons, List.prod_cons, lift_mul, ds, Matrix.map_mul]
      rw [← mul_assoc, eq, mul_assoc, ih, ← mul_assoc]
  have EE : F.map c * F.map c = 1 := by
    rw [← Matrix.map_mul, Plan.walshMatrix_mul_self, Matrix.map_one _ (map_zero c) (map_one c)]
  have endeq := congrArg (F.map c * ·) (go (List.ofFn id))
  have eqD : D (List.ofFn id) = diagonal (fun y => ∏ j, v j y) := by
    simp [D,List.map_ofFn, List.prod_ofFn]
  rw [eqD] at endeq
  simpa only [Matrix.map_mul, ← mul_assoc, EE, one_mul, List.map_ofFn, Function.comp_id, F, c, v]
    using endeq.symm

end
end BinaryQuery

end NearSquareRoot
end Computability
end OAI
