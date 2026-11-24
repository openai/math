import OAI.Computability.VPVNP.PolynomialBounds
import OAI.Computability.VPVNP.VerifierCircuit

/-!
# VNP membership from Boolean verification

For a family of Boolean verifiers with polynomially many choice bits and gates, the
paired coefficient-counting polynomials lie in VNP. The size and degree estimates
come from the explicitly compiled arithmetic summand. For the machine-defined
family, the remaining input to this construction is a polynomial-size Boolean
circuit family implementing the canonical path verifier.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Verifier

variable {F : Type*} [Field F]

private theorem bounded_of_verifier_bound {t g f : ℕ → ℕ}
    (ht : PolynomiallyBounded t) (hg : PolynomiallyBounded g)
    (hf : ∀ n, f n ≤ 8 * (n + t n + g n + 1)) : PolynomiallyBounded f := by
  exact ((PolynomiallyBounded.const 8).mul
    (((PolynomiallyBounded.id.add ht).add hg).add (PolynomiallyBounded.const 1))).of_le hf

/-- A bounded Boolean verifier gives a VNP representation of its paired counting
polynomial, with a formal summand on the visible variables and all witness bits. -/
theorem isVNP_of_counting_verifier {t g : ℕ → ℕ}
    (ht : PolynomiallyBounded t) (hg : PolynomiallyBounded g)
    (c : (n : ℕ) → BooleanTranscript.Circuit (Inputs n (t n)) (g n)) :
    IsVNP (F := F) (σ := fun n => Fin n × Bool)
      (fun n => pairedPolynomial (fun x => ∑ y : Fin (t n) → Bool,
        BooleanTranscript.bit ((c n).eval (Sum.elim x y)))) := by
  let W (n : ℕ) := Witness n (t n) (g n)
  let p : Family F (fun n => Fin n × Bool) := fun n => pairedPolynomial (fun x =>
    ∑ y : Fin (t n) → Bool, BooleanTranscript.bit ((c n).eval (Sum.elim x y)))
  let s : Family F (fun n => (Fin n × Bool) ⊕ W n) := fun n => summand (c n)
  change IsVNP p
  constructor
  · constructor
    · apply bounded_of_verifier_bound ht hg
      intro n
      simp
      omega
    · apply bounded_of_verifier_bound ht hg
      intro n
      exact (pairedPolynomial_isHomogeneous _).totalDegree_le.trans (by omega)
  · refine ⟨W, fun n => inferInstanceAs (Fintype (Witness n (t n) (g n))), s, ?_, ?_, ?_⟩
    · apply bounded_of_verifier_bound ht hg
      intro n
      simp [W, Witness, Inputs]
      omega
    · constructor
      · constructor
        · apply bounded_of_verifier_bound ht hg
          intro n
          simp [W, Witness, Inputs]
          omega
        · apply bounded_of_verifier_bound ht hg
          intro n
          exact (totalDegree_summand_le _).trans (by omega)
      · apply bounded_of_verifier_bound ht hg
        intro n
        obtain ⟨m, hm, d, hd⟩ := exists_circuit_summand (R := F) (c n)
        apply (circuitSize_le_iff.mpr ⟨m, hm, d, hd⟩).trans
        omega
    · intro n
      convert (sum_summand (R := F) (c n)).symm using 2
      · ext w
        simp
      · rfl

/-- Applying the generic verifier construction to the machine family (1.1). -/
theorem P_isVNP_of_verifier {g : ℕ → ℕ}
    (c : (n : ℕ) → BooleanTranscript.Circuit (Inputs n (n ^ clockExponent)) (g n))
    (hg : PolynomiallyBounded g)
    (hc : ∀ n x y, (c n).eval (Sum.elim x y) = verifiesInput x y) :
    IsVNP (F := F) (σ := fun n => Fin n × Bool)
      (fun n => MvPolynomial.map (Int.castRingHom F) (P n)) := by
  have ht : PolynomiallyBounded (fun n => n ^ clockExponent) :=
    ⟨1, clockExponent, 0, fun n _ => by simp⟩
  have h := isVNP_of_counting_verifier (F := F) ht hg c
  convert h using 1
  funext n
  rw [map_P]
  congr 1
  funext x
  simpa only [hc, BooleanTranscript.bit] using acceptingCount_eq_sum_witnesses (R := F) x

end Verifier

end VPVNP
end Computability
end OAI
