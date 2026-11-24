import OAI.Computability.VPVNP.JointLabelBounds
import OAI.Computability.VPVNP.LabelEvaluator

/-!
# Applying the finite-algebra evaluator to the small-circuit label equations

At a length with a circuit of size at most `n^c`, the grammar assignment and
the fixed motif solution descend together. The prime is fixed in positive
characteristic and has polynomially bounded bit length in characteristic zero.
The resulting finite algebra therefore satisfies all instances of (8.1) and
all the local wire identities, with one normalized evaluator for every label
exponent vector.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointLabelSystem

open MvPolynomial LabelEvaluator

variable {J Z : Type*} [Fintype J] [Fintype Z] {n : ℕ}

/-- Degree bound for all grammar and motif equations, raised to at least three for the
finite-algebra construction. -/
def degreeBound (J : Type*) [Fintype J] (n : ℕ) : ℕ := max 3 (max (2 * n - 1) (Fintype.card J))

/-- When the joint grammar and motif equations have a characteristic-zero solution, descent
yields a finite model at a prime bounded by two to this exponent. -/
noncomputable def primeBits (c : ℕ) (G : MotifParameters.Data J Z) (n : ℕ) : ℕ :=
  let t := Fintype.card (Production n c ⊕ G.Entry)
  let d := degreeBound J n
  let a := Nat.clog 2 (multiplierDegree t d + d + 1) * t
  2 * (a + Nat.clog 2 (a + coefficientExponent c G n + 2)) + 1

/-- The exponent in the good-prime size bound is polynomial in the input length. -/
theorem primeBits_polynomiallyBounded (c : ℕ) (G : MotifParameters.Data J Z) :
    PolynomiallyBounded (primeBits c G) := by
  let t (n : ℕ) := Fintype.card (Production n c ⊕ G.Entry)
  have ht : PolynomiallyBounded t := variable_count_polynomiallyBounded G c
  have hd : PolynomiallyBounded (degreeBound J) :=
    (((PolynomiallyBounded.const 3).add ((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id)).add
      (.const (Fintype.card J))).of_le (fun n => by dsimp [degreeBound]; omega)
  have clog {g : ℕ → ℕ} (hg : PolynomiallyBounded g) :
      PolynomiallyBounded (fun n => Nat.clog 2 (g n)) :=
    hg.of_le (fun _ => Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le)
  exact RadicalCertificate.polynomiallyBounded_good_prime_bits ht
    (RadicalCertificate.polynomiallyBounded_clog_paperBound ht (clog hd))
    (clog hd) (clog (polynomiallyBounded_coefficientExponent c G))

/-- An actual small circuit and motif solution yield the finite-algebra
evaluator for the joint system. Both characteristic cases preserve the
specified quantifier order with respect to the input exponent vectors. -/
theorem exists_evaluator_of_circuit {k : Type*} [Field k] (q : ℕ) [CharP k q] {c s : ℕ}
    (hn : 2 ≤ n) (hc : 1 ≤ c) (hs : s ≤ n ^ c) (circuit : Circuit k (Fin n × Bool) s)
    (hpoly : circuit.polynomial = map (Int.castRingHom k) (P n))
    (G : MotifParameters.Data J Z) (κ : G.Entry → k) (hκ : G.IsSolution κ) :
    ∃ p : Nat.Primes, (q ≠ 0 → p.val = q) ∧ (q = 0 → p.val ≤ 2 ^ primeBits c G n) ∧
      Nonempty (Model p (degreeBound J n) (equations hn c G)) := by
  classical
  let : Fintype G.Output := Fintype.ofFinite _
  obtain ⟨a, ha⟩ := exists_solution hn hc hs circuit hpoly G κ hκ
  have hdeg (i) : (equations hn c G i).totalDegree ≤ degreeBound J n :=
    (equations_totalDegree_le hn c G i).trans (le_max_right ..)
  have hd : 3 ≤ degreeBound J n := le_max_left ..
  rcases CharP.char_is_prime_or_zero k q with hp | rfl
  · let p : Nat.Primes := ⟨q, hp⟩
    exact ⟨p, fun _ => rfl, fun h => (hp.ne_zero h).elim, exists_model_positive p _
      (degreeBound J n) hd hdeg a ha⟩
  · have := CharP.charP_to_charZero k
    obtain ⟨p, hp, hM⟩ := exists_model_charZero (equations hn c G) _ _ hd hdeg
      (equations_coeff_natAbs_le hn c G) a ha
    exact ⟨p, fun h => (h rfl).elim, fun _ => hp, hM⟩

/-- The single reduced algebra furnished by the evaluator satisfies every
path-count coefficient identity and every fixed motif equation simultaneously. -/
theorem evaluator_label_identities (hn : 2 ≤ n) (c : ℕ) (G : MotifParameters.Data J Z)
    {p : Nat.Primes} (M : Model p (degreeBound J n) (equations hn c G)) :
    (∀ x : Fin n → Bool, eval₂Hom (Int.castRingHom M.algebra)
      (M.labels ∘ leftIndex (Production n c) G.Entry)
      (labelQuery ⟨n - 1, by omega⟩ ⟨0, pow_pos (by omega) _⟩ x) = (acceptingCount x : M.algebra)) ∧
      G.IsSolution (M.labels ∘ rightIndex (Production n c) G.Entry) :=
  (solution_iff hn c G M.labels).mp M.solution

end JointLabelSystem

end VPVNP
end Computability
end OAI
