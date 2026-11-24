import OAI.Computability.VPVNP.BalancedGrammar
import OAI.Computability.VPVNP.BalancedCoefficients
import OAI.Computability.VPVNP.CircuitGrammar
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Balanced rank decompositions of exact circuits

In Theorem 4.2 of *VP and VNP differ over every field*, a monomial selects one variable
at each of the `ℓ` parties. Its circuit may use arbitrary intermediate monomials. Taking
the queried coefficients of a balanced product expansion yields one matrix on each party
cut. The sum of these matrices recovers the coefficient tensor, and the number of graded
circuit states bounds every matrix rank.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial ParseGrammar

variable {I J k : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Field k] {s : ℕ}

/-- An assignment to the selected parties, viewed as an exponent of the whole polynomial. -/
noncomputable def cutExponent (S : Finset I) (a : S → J) : (I × J) →₀ ℕ :=
  ∑ i : S, Finsupp.single (i.val, a i) 1

omit [Fintype I] [DecidableEq I] [Fintype J] in
theorem cutExponent_restrict (S : Finset I) (a : I → J) :
    cutExponent S (fun i ↦ a i.val) = partyExponent S a := by
  simpa only [cutExponent, partyExponent, ← Finset.attach_eq_univ] using
    (Finset.sum_attach S fun i ↦ Finsupp.single (i, a i) (1 : ℕ))

/-- Matrix of one cut, including the factorization through a finite state index. -/
structure CutFactors (S : Finset I) (B : Type*) (J k : Type*) where
  /-- Left factor of the cut matrix, with one row per assignment of labels in `J` to the
  parties of `S` and one column per state in `B`. -/
  left : Matrix (S → J) B k
  /-- Right factor of the cut matrix, with one row per state in `B` and one column per
  assignment of labels in `J` to the complementary parties. -/
  right : Matrix B (↥(Sᶜ : Finset I) → J) k

/-- Matrix on assignments to the two sides of the cut, obtained by multiplying the factors and
summing over the shared state index `B`. -/
noncomputable def CutFactors.matrix {S : Finset I} {B : Type*} [Fintype B]
    (F : CutFactors S B J k) : Matrix (S → J) (↥(Sᶜ : Finset I) → J) k :=
  F.left * F.right

theorem CutFactors.rank_le {S : Finset I} {B : Type*} [Fintype B]
    (F : CutFactors S B J k) : F.matrix.rank ≤ Fintype.card B :=
  (Matrix.rank_mul_le_left F.left F.right).trans F.left.rank_le_card_width

/-- The finite index of all balanced states, for a circuit on party-indexed variables. -/
abbrev Circuit.BalancedStates (I J : Type*) [Fintype I] (s : ℕ) :=
  BalancedIndex (Fintype.card I) (Circuit.GrammarSlots (I × J) s) (Fintype.card I)

theorem Circuit.card_balancedStates_le (I J : Type*) [Fintype I] [Fintype J] (s : ℕ) :
    Fintype.card (Circuit.BalancedStates I J s) ≤
      Fintype.card I * (Fintype.card I * Fintype.card J + s + 1) := by
  classical
  simpa only [Fintype.card_prod, Fintype.card_fin, Circuit.card_grammarSlots] using
    (Fintype.card_subtype_le
      (fun u : Fin (Fintype.card I) × Circuit.GrammarSlots (I × J) s ↦
        Fintype.card I ≤ 3 * (u.1.val + 1) ∧ 3 * (u.1.val + 1) ≤ 2 * Fintype.card I))

/-- Every coefficient selecting one variable per party is the sum of factored
cut matrices. An unbalanced cut contributes the zero matrix, and each factorization
uses only the balanced graded states of the given circuit. -/
theorem Circuit.exists_balanced_cutFactors (c : Circuit k (I × J) s)
    (hI : 3 ≤ Fintype.card I) :
    ∃ F : (S : Finset I) → CutFactors S (Circuit.BalancedStates I J s) J k,
      (∀ a : I → J, c.polynomial.coeff (partyExponent Finset.univ a) =
        ∑ S : Finset I, (F S).matrix (fun i ↦ a i.val) (fun i ↦ a i.val)) ∧
      (∀ S, ¬ (Fintype.card I ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * Fintype.card I) →
        (F S).matrix = 0) := by
  classical
  let ℓ := Fintype.card I
  let d : Fin ℓ := ⟨ℓ - 1, by dsimp [ℓ]; omega⟩
  have hd : d.val + 1 = ℓ := by dsimp [d, ℓ]; omega
  obtain ⟨G, hG⟩ := c.exists_parseGrammar ℓ
  obtain ⟨m, hm⟩ := G.exists_balanced_expansion ℓ hI d none (by rw [hd]; omega)
  let g (b : Circuit.BalancedStates I J s) := G.eval b.val.1 b.val.2
  let F (S : Finset I) : CutFactors S (Circuit.BalancedStates I J s) J k :=
    ⟨.of fun x b ↦ (g b).coeff (cutExponent S x),
     .of fun b y ↦ (m b).coeff (cutExponent Sᶜ y)⟩
  refine ⟨F, ?_, ?_⟩
  · intro a
    have hc := hG d
    rw [hd] at hc
    have hcoeff : (homogeneousComponent ℓ c.polynomial).coeff (partyExponent Finset.univ a) =
        c.polynomial.coeff (partyExponent Finset.univ a) := by
      simp only [coeff_homogeneousComponent, degree_partyExponent, Finset.card_univ, ℓ, ite_true]
    rw [← hcoeff, ← hc, hm, coeff_sum]
    simp_rw [mul_comm (m _) (G.eval _ _), coeff_mul_partyExponent]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    simp only [F, CutFactors.matrix, Matrix.mul_apply, Matrix.of_apply, cutExponent_restrict, g]
    rfl
  · intro S hS
    ext x y
    change ∑ b, (g b).coeff (cutExponent S x) * (m b).coeff (cutExponent Sᶜ y) = 0
    apply Finset.sum_eq_zero
    intro b _
    have hg := G.eval_isHomogeneous b.val.1 b.val.2
    have hdS : (cutExponent S x).degree = S.card := by
      simp [cutExponent, Finsupp.degree_single]
    have hn : S.card ≠ b.val.1.val + 1 := by
      intro h
      exact hS (h ▸ b.property)
    rw [show (g b).coeff (cutExponent S x) = 0 from
      IsWeightedHomogeneous.coeff_eq_zero hg _ (by
        change Finsupp.weight (fun _ : I × J ↦ (1 : ℕ)) (cutExponent S x) ≠ _
        rwa [← Finsupp.degree_eq_weight_one, hdS]),
      zero_mul]

/-- Grouping by cut gives the balanced flattening-rank estimate of Theorem 4.2. -/
theorem Circuit.exists_balanced_matrices (c : Circuit k (I × J) s) (hI : 3 ≤ Fintype.card I) :
    ∃ M : (S : Finset I) → Matrix (S → J) (↥(Sᶜ : Finset I) → J) k,
      (∀ a : I → J, c.polynomial.coeff (partyExponent Finset.univ a) =
        ∑ S : Finset I, M S (fun i ↦ a i.val) (fun i ↦ a i.val)) ∧
      (∀ S, ¬ (Fintype.card I ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * Fintype.card I) → M S = 0) ∧
      ∀ S, (M S).rank ≤ Fintype.card I * (Fintype.card I * Fintype.card J + s + 1) := by
  classical
  obtain ⟨F, hcoeff, hbal⟩ := c.exists_balanced_cutFactors hI
  exact ⟨fun S ↦ (F S).matrix, hcoeff, hbal,
    fun S ↦ (F S).rank_le.trans (card_balancedStates_le I J s)⟩

end VPVNP
end Computability
end OAI
