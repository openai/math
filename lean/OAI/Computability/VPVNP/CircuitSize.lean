import OAI.Computability.VPVNP.CircuitComposition
import OAI.Computability.VPVNP.CircuitDescent
import Mathlib.Data.Nat.Find

/-!
# Minimum exact circuit size

Every formal polynomial has a division-free arithmetic circuit. Taking the
minimum over topologically ordered circuits therefore defines the gate count
`L_F` of §1, including zero-gate circuits for variables and field constants.
-/

namespace OAI
namespace Computability
namespace VPVNP

variable {R σ τ : Type*} [CommRing R]

/-- A single scalar input is an output of a circuit with no binary gates. -/
def Circuit.constant (a : R) : Circuit R σ 0 := ⟨.nil, .const a⟩

/-- A single variable is an output of a circuit with no binary gates. -/
def Circuit.variable (i : σ) : Circuit R σ 0 := ⟨.nil, .var i⟩

@[simp] theorem Circuit.polynomial_constant (a : R) :
    (Circuit.constant a : Circuit R σ 0).polynomial = MvPolynomial.C a := rfl

@[simp] theorem Circuit.polynomial_variable (i : σ) :
    (Circuit.variable i : Circuit R σ 0).polynomial = MvPolynomial.X i := rfl

/-- Every multivariate polynomial is the formal output of a finite exact circuit. -/
theorem exists_circuit_polynomial (p : MvPolynomial σ R) :
    ∃ n, ∃ c : Circuit R σ n, c.polynomial = p := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, Circuit.constant a, rfl⟩
  | add p q hp hq =>
    obtain ⟨n, c, rfl⟩ := hp
    obtain ⟨m, d, rfl⟩ := hq
    exact ⟨n + m + 1, Circuit.combine .add c d, Circuit.polynomial_combine ..⟩
  | mul_X p i hp =>
    obtain ⟨n, c, rfl⟩ := hp
    exact ⟨n + 0 + 1, Circuit.combine .mul c (Circuit.variable i),
      Circuit.polynomial_combine ..⟩

/-- The least number of binary addition, subtraction and multiplication gates
in a circuit computing `p` as a formal polynomial, with arbitrary scalar inputs. -/
noncomputable def circuitSize (p : MvPolynomial σ R) : ℕ := by
  classical
  exact Nat.find (exists_circuit_polynomial p)

theorem circuitSize_spec (p : MvPolynomial σ R) :
    ∃ c : Circuit R σ (circuitSize p), c.polynomial = p := by
  classical
  exact Nat.find_spec (exists_circuit_polynomial p)

theorem circuitSize_le_iff {p : MvPolynomial σ R} {n : ℕ} :
    circuitSize p ≤ n ↔ ∃ m ≤ n, ∃ c : Circuit R σ m, c.polynomial = p := by
  classical
  exact Nat.find_le_iff (exists_circuit_polynomial p) n

theorem circuitSize_le_of_circuit {n : ℕ} (c : Circuit R σ n) :
    circuitSize c.polynomial ≤ n :=
  circuitSize_le_iff.mpr ⟨n, le_rfl, c, rfl⟩

@[simp] theorem circuitSize_C (a : R) : circuitSize (MvPolynomial.C (σ := σ) a) = 0 :=
  Nat.eq_zero_of_le_zero (circuitSize_le_of_circuit (Circuit.constant a))

@[simp] theorem circuitSize_X (i : σ) : circuitSize (MvPolynomial.X (R := R) i) = 0 :=
  Nat.eq_zero_of_le_zero (circuitSize_le_of_circuit (Circuit.variable i))

theorem circuitSize_binOp_le (op : BinOp) (p q : MvPolynomial σ R) :
    circuitSize (op.apply p q) ≤ circuitSize p + circuitSize q + 1 := by
  obtain ⟨c, hc⟩ := circuitSize_spec p
  obtain ⟨d, hd⟩ := circuitSize_spec q
  simpa only [Circuit.polynomial_combine, hc, hd] using
    circuitSize_le_of_circuit (Circuit.combine op c d)

/-- Replacing variables by variables or constants preserves an upper bound
on the number of binary gates, regardless of the field constants used. -/
theorem circuitSize_projection_le (φ : Projection R σ τ) (p : MvPolynomial σ R) :
    circuitSize (φ.hom p) ≤ circuitSize p := by
  obtain ⟨c, hc⟩ := circuitSize_spec p
  simpa only [Circuit.project_polynomial, hc] using circuitSize_le_of_circuit (c.subst φ id)

/-- Applying a scalar homomorphism to the output cannot increase its minimum gate count. -/
theorem circuitSize_map_le {S : Type*} [CommRing S] (f : R →+* S) (p : MvPolynomial σ R) :
    circuitSize (MvPolynomial.map f p) ≤ circuitSize p := by
  obtain ⟨c, hc⟩ := circuitSize_spec p
  simpa only [Circuit.map_polynomial, hc] using circuitSize_le_of_circuit (c.mapConstants f)

/-- Section 1's reduction to one algebraically closed field. For a polynomial over
the prime field `k`, a lower bound over its algebraic closure `K` holds with the
same numerical value over every field extension `F` of `k`. -/
theorem circuitSize_descent_le {k K F : Type*} [Field k] [Field K] [Field F]
    [Algebra k K] [Algebra k F] [IsAlgClosed K] (p : MvPolynomial σ k) :
    circuitSize (MvPolynomial.map (algebraMap k K) p) ≤
      circuitSize (MvPolynomial.map (algebraMap k F) p) := by
  obtain ⟨c, hc⟩ := circuitSize_spec (MvPolynomial.map (algebraMap k F) p)
  obtain ⟨f, hf⟩ := c.exists_scalar_relabeling (K := K) p hc
  simpa only [hf] using circuitSize_le_of_circuit (c.mapConstants f)

end VPVNP
end Computability
end OAI
