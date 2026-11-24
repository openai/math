import OAI.Computability.VPVNP.GraphCertificateExtraction
import OAI.Computability.VPVNP.LinearNormalization
import OAI.Computability.VPVNP.MacaulayRelations
import OAI.Computability.VPVNP.MonicGraphRelation
import OAI.Computability.VPVNP.PerronBounds
import OAI.Computability.VPVNP.PerronRelation

/-! # The effective weak Nullstellensatz bound for the evaluator

Section 8.2 uses the multiplier bound `(2D)^(4(n+2))` over algebraically
closed fields. We prove it using the graph of the equation values, a linear
Noether normalization, and a bounded Perron relation. Integral closedness
makes the minimal relation monic, and taking its top parameter coefficient
gives a bounded certificate. This also supplies the effective hypothesis
in the Macaulay row test of Appendix D.1.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate

open MvPolynomial

/-- Every inconsistent degree-`D` system in `n` variables has a certificate of the
explicit degree used in the paper. The equation count and the characteristic are arbitrary. -/
theorem effective_weakCertificateBound (E I : Type*) [Field E] [IsAlgClosed E] [Fintype I]
    {n D : ℕ} (hD : 3 ≤ D) :
    WeakCertificateBound E I n D ((2 * D) ^ (4 * (n + 2))) := by
  classical
  intro F hF hno
  obtain ⟨Q, hQ, hinj, hint⟩ := LinearNormalization.exists_linear_normalization
    (graphGenerator F) (graphGenerator_adjoin F hno)
  let T : MvPolynomial (Fin (n+1)) E := X 0
  let g : Fin ((n+1)+1) → MvPolynomial (Fin (n+1)) E := Fin.cons T Q
  have hd (j : Fin ((n+1)+1)) : (g j).totalDegree ≤ D+1 :=
    Fin.cases (by simp [g, T]) (fun i => graphGenerator_span_degree F hF (hQ i)) j
  obtain ⟨W, hW, hWdeg, hWzero⟩ := perron_relation g hd
  obtain ⟨U, hmonic, hzero, _, hdeg⟩ := monic_relation_of_relation Q T hinj (hint T) W hW hWzero
  obtain ⟨A, hA, hcert⟩ := graph_monic_certificate F hF Q hQ U (hdeg.trans hWdeg) hmonic hzero
  refine ⟨A, fun i => (hA i).trans ?_, hcert⟩
  apply le_trans _ (perronSimplexBound_le_paper_envelope hD)
  let B := perronSimplexBound (n + 1) (D + 1)
  change (D + 1) * B ≤ 2 * (D + 1) * (B + 1)^2
  exact Nat.mul_le_mul (by omega) (by nlinarith only [Nat.zero_le (B*B)])

/-- The actual effective bound in the evaluator's row-space test for radical membership.
The tested polynomial and the matrix may be defined over a smaller base field. -/
theorem row_test_effective {K E I : Type*} [Field K] [Field E] [Algebra K E] [IsAlgClosed E]
    [Fintype I] {n d R₀ P : ℕ} (hd : 3 ≤ d) (F : I → MvPolynomial (Fin n) K)
    (f : MvPolynomial (Fin n) K) (hF : ∀ i, (F i).totalDegree ≤ d) (hf : f.totalDegree ≤ R₀)
    (hP : (2 * max d (R₀+1)) ^ (4 * (n+3)) ≤ P) (hpos : P ≠ 0) :
    let H := (2 * max d (R₀+1)) ^ (4 * (n+3))
    (∀ x : Fin n → E, (∀ i, aeval x (F i) = 0) → aeval x f = 0) ↔
      coefficientRow (H + P * R₀ + d) (f ^ P) ∈ Submodule.span K
        (Set.range (macaulayMatrix F (H + P * R₀) (H + P * R₀ + d)).row) :=
  row_test_of_weakCertificateBound F f hP hpos hF hf
    (effective_weakCertificateBound E (Option I) (hd.trans (le_max_left ..)))

end RadicalCertificate

end VPVNP
end Computability
end OAI
