import OAI.Hierarchy.CircuitBalancedIdeal

namespace OAI
/-! # A bounded balanced-product decomposition of a circuit component -/

namespace Hierarchy

open CircuitSplit MvPolynomial Computability.VPVNP
open scoped BigOperators

theorem circuit_balanced_factors {F σ : Type*} [Field F] {p : MvPolynomial σ F}
    {d s : ℕ} (hd : 2 ≤ d) (small : circuitSize p ≤ s) :
    ∃ Q P : Fin (balancedCircuitTerms d s) → MvPolynomial σ F,
      (∀ v, ∃ j, (P v).IsHomogeneous j ∧ d < 3*j ∧ 3*j ≤ 2*d) ∧
      homogeneousComponent d p = ∑ v, Q v * P v := by
  classical
  obtain ⟨c, hc⟩ := circuitSize_spec p
  let values := gateValues c.program
  let P := generator values d s
  let I := Ideal.span (Set.range P)
  have room : values.length ≤ 3*s+1 := by
    dsimp [values]
    rw [length_gateValues]
    omega
  have member : homogeneousComponent d c.polynomial ∈ I := output_mem c d hd I
    (fun _ hg _ hlo hhi => component_mem_span room hg hlo hhi)
  rw [hc] at member
  obtain ⟨Q, hQ⟩ := Ideal.mem_span_range_iff_exists_fun.mp member
  exact ⟨Q, P, generator_balanced values hd, hQ.symm⟩


end Hierarchy

end OAI
