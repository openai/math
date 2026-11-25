import OAI.Computability.BorderVNP.ResidueAdviceCircuit

/-! # Uniform gate bound for the actual arithmetic-branch advice equations

Numbering the table coordinates and clearing its deformation parameter leaves a
degree-five bound, uniform in the advice field and the selected affine chart.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open VPVNP ParseTable

/-- A concrete common majorant for every arithmetic-branch advice equation. -/
theorem adviceGateBudget_le {v k s M : ℕ} (hv : v ≤ M) (hk : k ≤ M) (hs : s ≤ M) :
    adviceGateBudget v k s ≤ 64 * (M+1)^5 := by
  have hcount : parameterCount v k s ≤ (v+s+1)*v + (k+1)^2*(v+s+1)^3 := by
    simpa only [parameterCount, Fintype.card_fin] using parameter_count_le (Fin v) k s
  unfold adviceGateBudget tableGateBudget
  calc
    _ ≤ (k+1)*(v+s+1)*(2*v+3*((k+1)*(v+s+1)*(v+s+1))) +
        2*((v+s+1)*v + (k+1)^2*(v+s+1)^3 + 1) + 7 := by gcongr
    _ ≤ (M+1)*(M+M+1)*(2*M+3*((M+1)*(M+M+1)*(M+M+1))) +
        2*((M+M+1)*M + (M+1)^2*(M+M+1)^3 + 1) + 7 := by gcongr
    _ ≤ _ := by ring_nf; omega

/-- Polynomial coordinate, degree and circuit-size parameters give polynomial advice
gate counts, with the same exponent five in their common majorant. -/
theorem polynomiallyBounded_adviceGateBudget {v k s : ℕ → ℕ}
    (hv : PolynomiallyBounded v) (hk : PolynomiallyBounded k) (hs : PolynomiallyBounded s) :
    PolynomiallyBounded (fun n => adviceGateBudget (v n) (k n) (s n)) := by
  let h := ((hv.add hk).add hs).add (.const 1)
  apply ((PolynomiallyBounded.const 64).mul (h.pow 5)).of_le
  intro n
  exact adviceGateBudget_le (M := v n+k n+s n) (by omega) (by omega) (by omega)

end Branch

end BorderVNP
end Computability
end OAI
