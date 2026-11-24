import OAI.Computability.VPVNP.WireCATZero
import OAI.Computability.VPVNP.BalancedLayoutThreshold
import OAI.Computability.VPVNP.ExactTensorPowerLayout
import OAI.Computability.VPVNP.TerminalStarWitness
import OAI.Computability.VPVNP.CubeExclusion
import OAI.Computability.VPVNP.SpectralRealizable

/-!
# Excluding a Euclidean cube from spectral wire distances

A hypothetical cube realization supplies one tensor whose spectral value is
strictly above the cost of every balanced two-center layout. Tensor powers of
this witness are projections from the paired-variable universal family at all
sufficiently large input lengths. This excludes the cube under the small-circuit
hypothesis, at the paper's threshold of `18 * C²`.
-/

namespace OAI
namespace Computability
namespace VPVNP

open WireTensor
open scoped symmDiff

private theorem cube_wire_distances {k : Type*} [Field k] {ℓ : ℕ}
    (w : WireRealization k (Grassmann.cubeDistances ℓ)) (A B : Finset (Fin ℓ)) :
    w.spectrum.wireDistance (w.label A) (w.label B)^2 = (w.scale⁻¹)^2 * (A ∆ B).card := by
  have h := w.distances A B
  have h' : w.spectrum.wireDistance (w.label A) (w.label B) =
      w.scale⁻¹ * Real.sqrt ((A ∆ B).card : ℝ) := by
    rw [show Real.sqrt ((A ∆ B).card : ℝ) = w.scale * w.spectrum.wireDistance (w.label A) (w.label B) from h,
      inv_mul_cancel_left₀ w.scale_pos.ne']
  rw [h', mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]


/-- Infinitely many circuits of size at most `n^C` exclude the corners of the
Euclidean cube from every spectral wire metric over the field. The literal incidence-table encoding of the
tensor power preserves the asymptotic central wire exponent `C`. -/
theorem cube_obstruction (k : Type*) [Field k] {C ℓ : ℕ} (hC : 1 ≤ C)
    (hdim : 18 * C^2 ≤ ℓ)
    (hsmall : ∀ N, ∃ n ≥ N, circuitSize (MvPolynomial.map (Int.castRingHom k) (P n)) ≤ n^C) :
    ¬ RealizableUpToScale k (Grassmann.cubeDistances ℓ) := by
  intro hw
  obtain ⟨w⟩ := hw
  let σ := w.scale⁻¹
  have hσ : 0 < σ := inv_pos.mpr w.scale_pos
  have hcreal : (1 : ℝ) ≤ (C : ℕ) := by exact_mod_cast hC
  have hℓreal : (18 : ℝ)*((C : ℕ) : ℝ)^2 ≤ ℓ := by exact_mod_cast hdim
  have hℓ : 3 ≤ ℓ := by
    have hh : 1 ≤ C^2 := Nat.one_le_pow _ _ hC
    omega
  obtain ⟨S, centers, ε, hε, hgap⟩ := w.spectrum.exists_cubeCentroid_layout_threshold
    w.label hσ (cube_wire_distances w) hcreal hℓreal (by
      intro S
      let : Nontrivial S.Parties := S.old.injective.nontrivial
      exact S.point.catZero_embedding)
  let corner := S.old ∘ w.label
  have hcorner (A B : Finset (Fin ℓ)) :
      S.point.wireDistance (corner A) (corner B)^2 = σ^2 * (A ∆ B).card := by
    rw [show S.point.wireDistance (corner A) (corner B) = _ from S.distances _ _]
    exact cube_wire_distances w A B
  let : Nontrivial S.Parties := S.old.injective.nontrivial
  obtain ⟨b, hb, A, hnz, hval⟩ := S.point.exists_cubeStar_witness corner hσ hε hcorner
  have hn := not_small_universal_of_exact_tensorPower_layout S.point (fun i => corner {i}) centers hb
    (by omega : 0 < C) (by simpa only [Fintype.card_fin] using hℓ) A hnz hσ hval (by
      intro s hlo hhi
      simp only [Fintype.card_fin] at hlo hhi
      exact (hgap s hlo hhi).le)
  exact hn hsmall

end VPVNP
end Computability
end OAI
