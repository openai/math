import OAI.Computability.VPVNP.SharpPowerObstruction
import OAI.Computability.VPVNP.TensorPowerLayout

/-!
# Cube-witness comparison at the original circuit exponent

For a tensor form admitting an encoding linear in its local dimension up to a
polynomial in the tensor power, the central wire in (4.5) costs the original
circuit exponent `C` times the centroid distance.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial WireTensor TensorPowerCNF

variable {k : Type*} [Field k] {I : Type} [Fintype I] [DecidableEq I]
    {P : Type*} [Fintype P] [Nonempty P]

/-- A literal projection with length `M * (h + 1)^D * (2^b)^h` supplies the exact
layout comparison from the paper, without multiplying the exponent `C`. -/
theorem not_small_universal_of_sharp_tensor_layout (F : SpectralPoint k P)
    (place : I → P) (centers : Finset I → Bool → P) {b C : ℕ} (hb : 0 < b) (hC : 0 < C)
    (hI : 3 ≤ Fintype.card I) (A : (I → Fin (2^b)) → k) (hnz : A ≠ 0)
    {scale threshold : ℝ} (hs : 0 < scale)
    (hlower : threshold <
      Real.logb 2 (F.value (placedTensor place (fun _ ↦ Fin (2^b)) A)) / (scale * b))
    (hcost : ∀ S : Finset I, Fintype.card I ≤ 3*S.card → 3*S.card ≤ 2*Fintype.card I →
      (C : ℝ) * F.wireDistance (centers S false) (centers S true) +
        ∑ i, F.wireDistance (place i) (centers S (cutSide S i)) ≤ scale * threshold)
    (hproject : ∀ T : (I → Digit b) → k, ∃ M D : ℕ, 0 < M ∧ ∀ h n,
      M * (h+1)^D * (2^b)^h ≤ n →
        ∃ φ : Projection k (Fin n × Bool) (I × Word b h),
          φ.hom (map (Int.castRingHom k) (VPVNP.P n)) = form T h) :
    ¬ ∀ N, ∃ n ≥ N, circuitSize (map (Int.castRingHom k) (VPVNP.P n)) ≤ n^C := by
  classical
  obtain ⟨A', hv, hgap⟩ := exists_digit_layout_witness F place centers hb A hnz hs hlower hcost
  obtain ⟨M, D, hM, hproj⟩ := hproject A'
  have hcard : Fintype.card (Digit b) = 2 ^ b := by simp [Digit]
  exact not_small_universal_of_sharp_projections F place centers A' (form A') M D C
    hM hC hI (hcard ▸ one_lt_pow₀ (by decide : 1 < (2 : ℕ)) hb.ne')
    (fun _ a ↦ coeff_form A' a) (fun h n hn ↦ hproj h n (by simpa only [hcard] using hn))
    hv hgap

end VPVNP
end Computability
end OAI
