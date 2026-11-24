import OAI.Computability.VPVNP.CompressionTemplates
import OAI.Computability.VPVNP.JointLabelEvaluator
import OAI.Computability.VPVNP.EvaluatorAdviceBounds

/-!
# A common finite algebra for the grammar and both compressor templates

At any small-circuit length, the grammar, the six-party block and the port
graph block satisfy their respective equations over the original field.
All three assignments descend together. The number of parties in the two
motifs can differ. The prime and the slice model are chosen before any input
exponent vector for the monomial evaluator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open MvPolynomial JointLabelSystem LabelEvaluator

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Numbered grammar labels followed, up to a permutation of coordinates,
by the fixed shrinking and degree-refresh map parameters. -/
noncomputable abbrev compressorLabelCount (c n : ℕ) := Fintype.card (Production n c ⊕ B.Entry)

/-- The actual simultaneous equations. There is one grammar row per Boolean
input, and the fixed template rows retain their distinct parameter names. -/
noncomputable def compressorEquations {n : ℕ} (hn : 2 ≤ n) (c : ℕ) :
    (Fin n → Bool) ⊕ B.EquationIndex → MvPolynomial (Fin (B.compressorLabelCount c n)) ℤ :=
  unionEquations (grammarEquation hn c) B.equation

theorem compressorEquationCount (n : ℕ) :
    Fintype.card ((Fin n → Bool) ⊕ B.EquationIndex) = 2 ^ n + Fintype.card B.EquationIndex := by
  simp

theorem compressorLabelCount_polynomial (c : ℕ) :
    PolynomiallyBounded (B.compressorLabelCount c) := by
  let hw := PolynomiallyBounded.id.pow (c + 5)
  apply (((hw.mul (PolynomiallyBounded.id.mul (.const 2))).add
    ((PolynomiallyBounded.id.pow 2).mul (hw.pow 3))).add (.const (Fintype.card B.Entry))).of_le
  intro n
  rw [compressorLabelCount, Fintype.card_sum]
  apply Nat.add_le_add_right
  simpa only [Fintype.card_fin, Fintype.card_prod, Fintype.card_bool] using
    card_grammarLabel_le (Fin n × Bool) (Fin (n ^ (c + 5))) n

/-- The template contribution to the degree bound is constant across lengths. -/
noncomputable def compressorDegree (n : ℕ) : ℕ :=
  max 3 (max (2 * n - 1) (Finset.univ.sup fun i : B.EquationIndex ↦ (B.equation i).totalDegree))

/-- A fixed bound for the absolute coefficients of both template families. -/
noncomputable def compressorHeight : ℕ :=
  Finset.univ.sup fun i : B.EquationIndex ↦
    (B.equation i).support.sup fun e ↦ ((B.equation i).coeff e).natAbs

theorem compressorEquation_degree {n : ℕ} (hn : 2 ≤ n) (c : ℕ) (i) :
    (B.compressorEquations hn c i).totalDegree ≤ B.compressorDegree n := by
  refine unionEquations_totalDegree_le _ _ (fun x ↦ ?_) (fun o ↦ ?_) i
  · exact (grammarEquation_totalDegree_le hn c x).trans ((le_max_left ..).trans (le_max_right ..))
  · exact (Finset.le_sup (f := fun z : B.EquationIndex ↦ (B.equation z).totalDegree)
      (Finset.mem_univ o)).trans ((le_max_right ..).trans (le_max_right ..))

theorem compressorEquation_coeff {n : ℕ} (hn : 2 ≤ n) (c : ℕ) (i e) :
    ((B.compressorEquations hn c i).coeff e).natAbs ≤
      2 ^ (grammarExponent c n + B.compressorHeight) := by
  refine unionEquations_coeff_natAbs_le _ _ (fun x b ↦ ?_) (fun o a ↦ ?_) i e
  · exact (grammarEquation_coeff_natAbs_le hn c x b).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..))
  · by_cases ha : a ∈ (B.equation o).support
    · have hh : ((B.equation o).coeff a).natAbs ≤ B.compressorHeight :=
        (Finset.le_sup (f := fun b ↦ ((B.equation o).coeff b).natAbs) ha).trans
          (Finset.le_sup (f := fun i : B.EquationIndex ↦
            (B.equation i).support.sup fun b ↦ ((B.equation i).coeff b).natAbs) (Finset.mem_univ o))
      exact (hh.trans Nat.lt_two_pow_self.le).trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..))
    · simp [notMem_support_iff.mp ha]

theorem compressorDegree_polynomial : PolynomiallyBounded B.compressorDegree :=
  (((PolynomiallyBounded.const 3).add
    ((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id)).add
    (.const (Finset.univ.sup fun i : B.EquationIndex ↦ (B.equation i).totalDegree))).of_le
    fun n ↦ by dsimp [compressorDegree]; omega

theorem compressorCoeffExponent_polynomial (c : ℕ) :
    PolynomiallyBounded (fun n ↦ grammarExponent c n + B.compressorHeight) := by
  let h := PolynomiallyBounded.id
  let h₂ := (PolynomiallyBounded.const 2).mul h
  have hp := (h₂.add ((h.mul (PolynomiallyBounded.const (c + 5))).mul h₂)).add (h₂.mul h)
  exact (((hp.add (h.pow clockExponent)).add (.const 1)).add (.const B.compressorHeight))

/-- Prime-size exponent in characteristic zero, fixed before the evaluator inputs. -/
noncomputable def compressorPrimeBits (c n : ℕ) :=
  let t := B.compressorLabelCount c n
  let d := B.compressorDegree n
  let a := Nat.clog 2 (multiplierDegree t d + d + 1) * t
  2 * (a + Nat.clog 2 (a + (grammarExponent c n + B.compressorHeight) + 2)) + 1

theorem compressorPrimeBits_polynomial (c : ℕ) : PolynomiallyBounded (B.compressorPrimeBits c) := by
  have ht := B.compressorLabelCount_polynomial c
  have hd := B.compressorDegree_polynomial.clog
  have hb := (B.compressorCoeffExponent_polynomial c).clog
  exact RadicalCertificate.polynomiallyBounded_good_prime_bits ht
    (RadicalCertificate.polynomiallyBounded_clog_paperBound ht hd) hd hb

/-- Read the original production coefficient equations and both templates
back out of the numbered simultaneous system in an arbitrary ring. -/
theorem compressorSolution_iff {R : Type*} [CommRing R] {n : ℕ} (hn : 2 ≤ n) (c : ℕ)
    (a : Fin (B.compressorLabelCount c n) → R) :
    (∀ i, eval₂Hom (Int.castRingHom R) a (B.compressorEquations hn c i) = 0) ↔
      (∀ x : Fin n → Bool, eval₂Hom (Int.castRingHom R) (a ∘ leftIndex (Production n c) B.Entry)
        (labelQuery ⟨n - 1, by omega⟩ ⟨0, pow_pos (by omega) _⟩ x) = (acceptingCount x : R)) ∧
      B.IsSolution (a ∘ rightIndex (Production n c) B.Entry) := by
  rw [compressorEquations, unionEquations_solution_iff]
  simp [grammarEquation, IsSolution, sub_eq_zero]

/-- Algebraic descent of the full joint system at every satisfiable length. -/
theorem exists_compressorModel_of_solution (q : ℕ) [CharP k q] {n c : ℕ}
    (hn : 2 ≤ n) (a : Fin (B.compressorLabelCount c n) → k)
    (ha : ∀ i, eval₂ (Int.castRingHom k) a (B.compressorEquations hn c i) = 0) :
    ∃ p : Nat.Primes, (q ≠ 0 → p.val = q) ∧ (q = 0 → p.val ≤ 2 ^ B.compressorPrimeBits c n) ∧
      Nonempty (Model p (B.compressorDegree n) (B.compressorEquations hn c)) := by
  have hd : 3 ≤ B.compressorDegree n := le_max_left ..
  rcases CharP.char_is_prime_or_zero k q with hp | rfl
  · let p : Nat.Primes := ⟨q, hp⟩
    exact ⟨p, fun _ ↦ rfl, fun h ↦ (hp.ne_zero h).elim, exists_model_positive p _
      (B.compressorDegree n) hd (B.compressorEquation_degree hn c) a ha⟩
  · have := CharP.charP_to_charZero k
    obtain ⟨p, hp, hm⟩ := exists_model_charZero (B.compressorEquations hn c) _ _ hd
      (B.compressorEquation_degree hn c) (B.compressorEquation_coeff hn c) a ha
    exact ⟨p, fun h ↦ (h rfl).elim, fun _ ↦ hp, hm⟩

/-- A small circuit and the two compressor templates supply one simultaneous
solution to all the formal label equations. -/
theorem exists_compressorSolution_of_circuit {n c s : ℕ}
    (hn : 2 ≤ n) (hc : 1 ≤ c) (hs : s ≤ n ^ c) (circuit : Circuit k (Fin n × Bool) s)
    (hpoly : circuit.polynomial = map (Int.castRingHom k) (P n)) :
    ∃ a : Fin (B.compressorLabelCount c n) → k,
      ∀ i, eval₂ (Int.castRingHom k) a (B.compressorEquations hn c i) = 0 := by
  obtain ⟨labels, hlabels⟩ := pathCount_labelEquations hn hc hs circuit hpoly
  obtain ⟨κ, hκ⟩ := B.exists_solution
  let a := joinAssignment labels κ
  have ha := (B.compressorSolution_iff hn c a).mpr (by
    simpa only [a, joinAssignment_left, joinAssignment_right] using And.intro hlabels hκ)
  exact ⟨a, ha⟩

/-- From an actual circuit at the indicated length, obtain one reduced
finite-algebra model for the entire compressor. In positive characteristic
the prime is the given characteristic, and in characteristic zero its bit
length is polynomially bounded. -/
theorem exists_compressorEvaluator (q : ℕ) [CharP k q] {n c s : ℕ}
    (hn : 2 ≤ n) (hc : 1 ≤ c) (hs : s ≤ n ^ c) (circuit : Circuit k (Fin n × Bool) s)
    (hpoly : circuit.polynomial = map (Int.castRingHom k) (P n)) :
    ∃ p : Nat.Primes, (q ≠ 0 → p.val = q) ∧ (q = 0 → p.val ≤ 2 ^ B.compressorPrimeBits c n) ∧
      Nonempty (Model p (B.compressorDegree n) (B.compressorEquations hn c)) := by
  obtain ⟨a,ha⟩ := B.exists_compressorSolution_of_circuit hn hc hs circuit hpoly
  exact B.exists_compressorModel_of_solution q hn a ha

/-- The same model specializes every path-count equation and the two fixed
wire identities. Its functional and all exponent-vector path counts come
from `LabelEvaluator.Model.functional_one` and `Model.branchCount_mod`. -/
theorem compressorEvaluator_readback {n : ℕ} (hn : 2 ≤ n) (c : ℕ) {p : Nat.Primes}
    (M : Model p (B.compressorDegree n) (B.compressorEquations hn c)) :
    (∀ x : Fin n → Bool, eval₂Hom (Int.castRingHom M.algebra)
      (M.labels ∘ leftIndex (Production n c) B.Entry)
      (labelQuery ⟨n - 1, by omega⟩ ⟨0, pow_pos (by omega) _⟩ x) = (acceptingCount x : M.algebra)) ∧
      B.IsSolution (M.labels ∘ rightIndex (Production n c) B.Entry) :=
  (B.compressorSolution_iff hn c M.labels).mp M.solution

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
