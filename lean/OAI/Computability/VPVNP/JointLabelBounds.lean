import OAI.Computability.VPVNP.JointLabelSystem
import OAI.Computability.VPVNP.GrammarCoefficientBounds
import OAI.Computability.VPVNP.PolynomialBounds
import Mathlib.Data.Nat.Size

/-!
# Degree and coefficient bounds for the joint integer equations

In §8.1, a parse contributing to a grammar equation contains one label per
vertex of a full ordered binary tree with `n` leaves. The integer constant
subtracted from its parse count comes from the clocked accepting paths. The
additional motif equations depend only on the fixed integral tensors.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointLabelSystem

open MvPolynomial

/-- Every accepting path has its canonical string of clocked choices. -/
theorem acceptingCount_le {n : ℕ} (x : Fin n → Bool) :
    acceptingCount x ≤ 2 ^ (n ^ clockExponent) := by
  rw [acceptingCount_eq_card_witnesses]
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- The designated query is homogeneous of degree `2n - 1` before
subtraction of its integer constant. -/
theorem grammarEquation_totalDegree_le {n : ℕ} (hn : 2 ≤ n) (c : ℕ) (x : Fin n → Bool) :
    (grammarEquation hn c x).totalDegree ≤ 2 * n - 1 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply (labelQuery_isHomogeneous _ _ _).totalDegree_le.trans
  change 2 * (n - 1) + 1 ≤ 2 * n - 1
  omega

/-- An exponent bounding the parse count. The factors account for ordered
tree shapes, child states and terminal variables. -/
def parseExponent (c n : ℕ) := 2 * n + n * (c + 5) * (2 * n) + (2 * n) * n

private theorem parse_count_bound {n : ℕ} (hn : 2 ≤ n) (c : ℕ) :
    4 ^ (n - 1) * (n ^ (c + 5)) ^ (2 * (n - 1)) * (n * 2) ^ (n - 1 + 1)
      ≤ 2 ^ parseExponent c n := by
  have hshape : 4 ^ (n - 1) ≤ 2 ^ (2 * n) := calc
    4 ^ (n - 1) ≤ 4 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 2 ^ (2 * n) := by rw [pow_mul]; rfl
  have hstate : n ^ (c + 5) ≤ 2 ^ (n * (c + 5)) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  have hstates : (n ^ (c + 5)) ^ (2 * (n - 1)) ≤ 2 ^ (n * (c + 5) * (2 * n)) := by
    rw [pow_mul _ _ (2 * n)]
    exact (Nat.pow_le_pow_left hstate _).trans (Nat.pow_le_pow_right Nat.one_le_two_pow (by omega))
  have hterm : (n * 2) ^ (n - 1 + 1) ≤ 2 ^ (2 * n * n) := by
    rw [show n - 1 + 1 = n by omega, Nat.mul_comm n 2, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  simpa only [parseExponent, pow_add] using Nat.mul_le_mul (Nat.mul_le_mul hshape hstates) hterm

/-- An exponent bounding the magnitude of any integer grammar coefficient. -/
def grammarExponent (c n : ℕ) := parseExponent c n + n ^ clockExponent + 1

theorem grammarEquation_coeff_natAbs_le {n : ℕ} (hn : 2 ≤ n) (c : ℕ) (x : Fin n → Bool)
    (e : Production n c →₀ ℕ) : ((grammarEquation hn c x).coeff e).natAbs ≤ 2 ^ grammarExponent c n := by
  classical
  let d : Fin n := ⟨n - 1, by omega⟩
  let h : Fin (n ^ (c + 5)) := ⟨0, pow_pos (by omega) _⟩
  obtain ⟨hpos, hcount⟩ := coeff_labelQuery_bounds d h x e
  have hparse : ((labelQuery d h x).coeff e).natAbs ≤ 2 ^ parseExponent c n := by
    apply le_trans _ (parse_count_bound hn c)
    apply Int.ofNat_le.mp
    rw [Int.natAbs_of_nonneg hpos]
    simpa only [d, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] using hcount
  have hpath : ((C (acceptingCount x : ℤ) : MvPolynomial (Production n c) ℤ).coeff e).natAbs ≤
      2 ^ (n ^ clockExponent) := by
    rw [coeff_C]
    split_ifs <;> simp [acceptingCount_le]
  rw [grammarEquation, coeff_sub]
  refine (Int.natAbs_sub_le _ _).trans ((Nat.add_le_add hparse hpath).trans ?_)
  let a := parseExponent c n + n ^ clockExponent
  have hp : 2 ^ parseExponent c n ≤ 2 ^ a :=
    Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  have hw : 2 ^ (n ^ clockExponent) ≤ 2 ^ a :=
    Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
  simpa only [grammarExponent, pow_succ, Nat.mul_two, a] using Nat.add_le_add hp hw

variable {J Z : Type*} [Fintype J] (G : MotifParameters.Data J Z)

/-- One matrix entry per party is multiplied by a constant tensor coordinate
in each summand of a base identity. -/
theorem motifEquation_totalDegree_le (o : G.Output) : (G.equation o).totalDegree ≤ Fintype.card J := by
  classical
  unfold MotifParameters.Data.equation
  apply (totalDegree_sub _ _).trans
  refine max_le (by rw [totalDegree_C]; exact Nat.zero_le _) (totalDegree_finsetSum_le fun t _ => ?_)
  unfold WireTensor.applyLocal
  refine totalDegree_finsetSum_le fun b _ => (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, Nat.add_zero]
  simpa only [MotifParameters.Data.localMap, totalDegree_X, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one] using
      totalDegree_finsetProd Finset.univ (fun j => X (R := ℤ) (⟨o.1, t, j, o.2 j, b j⟩ : G.Entry))

variable [Fintype Z]

/-- The fixed integer coefficient height of all local motif equations. -/
noncomputable def motifHeight : ℕ := by
  classical exact Finset.univ.sup fun o : G.Output =>
    (G.equation o).support.sup fun e => ((G.equation o).coeff e).natAbs

theorem motifEquation_coeff_natAbs_le (o : G.Output) (e : G.Entry →₀ ℕ) :
    ((G.equation o).coeff e).natAbs ≤ motifHeight G := by
  classical
  by_cases he : e ∈ (G.equation o).support
  · unfold motifHeight
    exact (Finset.le_sup (f := fun e => ((G.equation o).coeff e).natAbs) he).trans
      (Finset.le_sup (f := fun o : G.Output => (G.equation o).support.sup
        fun e => ((G.equation o).coeff e).natAbs) (Finset.mem_univ o))
  · simp [notMem_support_iff.mp he]

/-- The union of the two systems preserves the separate degree estimates. -/
theorem equations_totalDegree_le {n : ℕ} (hn : 2 ≤ n) (c : ℕ)
    (G : MotifParameters.Data J Z) (j : (Fin n → Bool) ⊕ G.Output) :
    (equations hn c G j).totalDegree ≤ max (2 * n - 1) (Fintype.card J) :=
  unionEquations_totalDegree_le _ _
    (fun x => (grammarEquation_totalDegree_le hn c x).trans (le_max_left ..))
    (fun o => (motifEquation_totalDegree_le G o).trans (le_max_right ..)) j

/-- One exponent for the entire joint system at length `n`. -/
noncomputable def coefficientExponent (c : ℕ) (G : MotifParameters.Data J Z) (n : ℕ) :=
  grammarExponent c n + motifHeight G

theorem equations_coeff_natAbs_le {n : ℕ} (hn : 2 ≤ n) (c : ℕ)
    (G : MotifParameters.Data J Z) (j : (Fin n → Bool) ⊕ G.Output)
    (e : Fin (Fintype.card (Production n c ⊕ G.Entry)) →₀ ℕ) :
    ((equations hn c G j).coeff e).natAbs ≤ 2 ^ coefficientExponent c G n := by
  refine unionEquations_coeff_natAbs_le _ _ (fun x a => ?_) (fun o a => ?_) j e
  · exact (grammarEquation_coeff_natAbs_le hn c x a).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  · exact ((motifEquation_coeff_natAbs_le G o a).trans Nat.lt_two_pow_self.le).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))

/-- The joint height exponent is a polynomial bound for each fixed circuit
size exponent and fixed motif system, uniformly in the equation and monomial. -/
theorem polynomiallyBounded_coefficientExponent (c : ℕ) (G : MotifParameters.Data J Z) :
    PolynomiallyBounded (coefficientExponent c G) := by
  let h := PolynomiallyBounded.id
  let h₂ := (PolynomiallyBounded.const 2).mul h
  have hp := (h₂.add ((h.mul (PolynomiallyBounded.const (c + 5))).mul h₂)).add (h₂.mul h)
  exact (((hp.add (h.pow clockExponent)).add (PolynomiallyBounded.const 1)).add
    (PolynomiallyBounded.const (motifHeight G)))

/-- The unsigned bit length of any coefficient is at most the common exponent plus one. -/
theorem equations_coeff_size_le {n : ℕ} (hn : 2 ≤ n) (c : ℕ) (G : MotifParameters.Data J Z)
    (j : (Fin n → Bool) ⊕ G.Output) (e : Fin (Fintype.card (Production n c ⊕ G.Entry)) →₀ ℕ) :
    ((equations hn c G j).coeff e).natAbs.size ≤ coefficientExponent c G n + 1 := by
  simpa only [Nat.size_pow] using Nat.size_le_size (equations_coeff_natAbs_le hn c G j e)

end JointLabelSystem

end VPVNP
end Computability
end OAI
