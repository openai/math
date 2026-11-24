import OAI.Computability.VPVNP.SharpTensorLayout
import OAI.Computability.VPVNP.TensorPowerSharpProjection

/-!
# Tensor-power obstruction at the original exponent

The weighted incidence machine encodes the tensor form with length
`A * (h + 1)^4 * (2^b)^h`. Inserting this actual projection into the balanced
layout estimate recovers the central exponent `C` of Theorem 4.2.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial WireTensor TensorPowerCNF

variable {k : Type*} [Field k] {I : Type} [Fintype I] [DecidableEq I]
    {P : Type*} [Fintype P] [Nonempty P]

/-- An actual spectral witness above every balanced layout rules out arbitrarily
large small-circuit lengths of the universal counting polynomial. -/
theorem not_small_universal_of_exact_tensorPower_layout (F : SpectralPoint k P)
    (place : I → P) (centers : Finset I → Bool → P) {b C : ℕ} (hb : 0 < b) (hC : 0 < C)
    (hI : 3 ≤ Fintype.card I) (A : (I → Fin (2^b)) → k) (hnz : A ≠ 0)
    {scale threshold : ℝ} (hs : 0 < scale)
    (hlower : threshold <
      Real.logb 2 (F.value (placedTensor place (fun _ ↦ Fin (2^b)) A)) / (scale * b))
    (hcost : ∀ S : Finset I, Fintype.card I ≤ 3*S.card → 3*S.card ≤ 2*Fintype.card I →
      (C : ℝ) * F.wireDistance (centers S false) (centers S true) +
        ∑ i, F.wireDistance (place i) (centers S (cutSide S i)) ≤ scale * threshold) :
    ¬ ∀ N, ∃ n ≥ N, circuitSize (map (Int.castRingHom k) (VPVNP.P n)) ≤ n^C := by
  apply not_small_universal_of_sharp_tensor_layout F place centers hb hC hI A hnz hs hlower hcost
  intro T
  obtain ⟨M, hM, hproj⟩ := TensorPowerCNF.sharp_projection T
  exact ⟨M, 4, hM, hproj⟩

end VPVNP
end Computability
end OAI
