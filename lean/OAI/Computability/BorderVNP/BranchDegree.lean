import OAI.Computability.BorderVNP.BranchDegreeExtraction
import OAI.Computability.BorderVNP.BranchDegreeNormalization

/-! # Effective separating equations for polynomial images

Lemma 9.1 uses a singly exponential degree cutoff independent of the number of output
coordinates. We obtain such a cutoff by polynomial graph normalization and Perron's
monomial count. The argument applies to parameter maps over every infinite field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP.RadicalCertificate

/-- A point distinguished from a polynomial image by any formal relation is distinguished
by a relation of singly exponential degree in the number of parameters. -/
theorem bounded_separating_relation {I K : Type*} [Field K] [Infinite K] [Fintype I]
    {h d : ℕ} (Y : I → MvPolynomial (Fin h) K) (c : I → K) (hd : ∀ i, (Y i).totalDegree ≤ d)
    (q : MvPolynomial I K) (hq : aeval Y q = 0) (hc : eval c q ≠ 0) :
    ∃ f : MvPolynomial I K, f.totalDegree ≤ 2 * perronSimplexBound (h+1) (d+1) ∧
      aeval Y f = 0 ∧ eval c f = 1 := by
  obtain ⟨Q, U, hQ, hU, hmon, hz⟩ := monic_relation_in_span (realizedDifferences Y c)
    (X 0) (parameter_mem_graph Y c q hq hc) (by simp) (realizedDifferences_degree Y hd c) (by omega)
  obtain ⟨f, hdeg, hf, hfc⟩ := extract_separator Y c Q U hQ hmon hz
  exact ⟨f, hdeg.trans (Nat.mul_le_mul_left 2 hU), hf, hfc⟩

end Branch

end BorderVNP
end Computability
end OAI
