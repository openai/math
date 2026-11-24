import OAI.Computability.VPVNP.NormRigidity
import Mathlib.Topology.Algebra.SeparationQuotient.Basic

/-!
# Euclidean distances of possibly degenerate spectral sectors

Section 4.1 obtains a seminorm on the coordinate plane of a sector. Realizing
the distances on any nonempty open set forces its square to be a positive
semidefinite quadratic form, including when some directions have zero length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireGeometry

universe u

/-- The separation quotient of a finite-dimensional seminormed space inherits an
inner product if its eight-point distances are realizable by spectral wires. -/
theorem exists_normPreserving_map_of_realizable
    {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (k : Type*) [Field k] (p : Seminorm ℝ E)
    (h : ∀ a : Fin 8 → E,
      WireTensor.RealizableUpToScale k (fun i j => p (a i - a j))) :
    ∃ (Q : Type u) (_ : NormedAddCommGroup Q) (_ : InnerProductSpace ℝ Q) (f : E →ₗ[ℝ] Q),
      ∀ x, ‖f x‖ = p x := by
  let : SeminormedAddCommGroup E := p.toAddGroupSeminorm.toSeminormedAddCommGroup
  let : NormedSpace ℝ E := { norm_smul_le := fun a x => (map_smul_eq_mul p a x).le }
  let Q := SeparationQuotient E
  let f : E →ₗ[ℝ] Q := (SeparationQuotient.mkCLM ℝ E).toLinearMap
  have hsur : Function.Surjective f := SeparationQuotient.surjective_mk
  let : FiniteDimensional ℝ Q := FiniteDimensional.of_surjective f hsur
  have hf (x : E) : ‖f x‖ = p x := rfl
  obtain ⟨innerQ⟩ := NormRigidity.innerProduct_of_local_costs (E := Q) isOpen_univ Set.univ_nonempty (by
    intro a _
    choose x hx using fun i => hsur (a i)
    obtain ⟨w⟩ := h x
    refine ⟨w.scale⁻¹, inv_pos.mpr w.scale_pos, ?_⟩
    have hd (i j : Fin 8) : w.scale⁻¹ * dist (a i) (a j) =
        w.spectrum.wireDistance (w.label i) (w.label j) := by
      rw [dist_eq_norm, ← hx i, ← hx j, ← map_sub, hf, w.distances,
        inv_mul_cancel_left₀ w.scale_pos.ne']
    simp only [hd]
    intro X Y P M hX hY hP hM factor
    exact NormRigidity.eightPointCost_of_spectrum w.spectrum w.label hX hY hP hM factor)
  exact ⟨Q, inferInstance, innerQ, f, hf⟩

/-- The squared seminorm of a difference along two fixed directions has a
single mixed coefficient valid for every real parameter, including when one
or both directions lie in the kernel. -/
theorem seminorm_sq_smul_sub (k : Type*) [Field k] {V : Type*} [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] (p : Seminorm ℝ V)
    (h : ∀ n (x : Fin n → V),
      WireTensor.RealizableUpToScale k (fun i j ↦ p (x i - x j))) (u v : V) :
    ∃ c : ℝ, ∀ T : ℝ, p (T • u - v) ^ 2 = T ^ 2 * p u ^ 2 + p v ^ 2 - 2 * T * c := by
  obtain ⟨Q, qnorm, qinner, q, hn⟩ := exists_normPreserving_map_of_realizable k p (h 8)
  refine ⟨inner ℝ (q u) (q v), fun T ↦ ?_⟩
  rw [← hn, map_sub, map_smul, norm_sub_sq_real, real_inner_smul_left, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, hn, hn]
  ring

end WireGeometry

namespace SpectralGeometry

open scoped InnerProductSpace
open WireTensor

private theorem realizePlaneGlobally {k : Type*} [Field k] (p : Seminorm ℝ (ℝ × ℝ))
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ f : Fin 8 → ℝ × ℝ, (∀ i, f i ∈ U) →
      RealizableUpToScale k (fun i j => p (f i - f j))) (f : Fin 8 → ℝ × ℝ) :
    RealizableUpToScale k (fun i j => p (f i - f j)) := by
  obtain ⟨c, r, hr, hmem⟩ := NormRigidity.exists_homothety_mem f hU hne
  have hr' := (h (fun i => c + r • f i) hmem).smul (inv_pos.mpr hr)
  simpa only [add_sub_add_left_eq_sub, ← smul_sub, map_smul_eq_mul,
    Real.norm_of_nonneg hr.le, inv_mul_cancel_left₀ hr.ne'] using hr'

private theorem quadratic_of_normPreserving_map (p : Seminorm ℝ (ℝ × ℝ))
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    (f : (ℝ × ℝ) →ₗ[ℝ] Q) (h : ∀ x, ‖f x‖ = p x) :
    ∃ L W B : ℝ, ∀ x : ℝ × ℝ, p x ^ 2 = x.1 ^ 2 * L + x.2 ^ 2 * W + x.1 * x.2 * B := by
  let e₁ : ℝ × ℝ := (1, 0)
  let e₂ : ℝ × ℝ := (0, 1)
  refine ⟨‖f e₁‖ ^ 2, ‖f e₂‖ ^ 2, 2 * ⟪f e₁, f e₂⟫_ℝ, ?_⟩
  intro x
  have hcoord : x = x.1 • e₁ + x.2 • e₂ := by ext <;> simp [e₁, e₂]
  rw [← h, ← real_inner_self_eq_norm_sq, hcoord, map_add, map_smul, map_smul]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm (f e₂) (f e₁), e₁, e₂, Prod.fst_add,
    Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one, mul_zero,
    add_zero, zero_add]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- The square of the pullback seminorm on the coordinate plane of a spectral
sector is a quadratic form. The topology in the open-set hypothesis is the
usual topology of the coordinate plane. -/
theorem sectorSeminorm_quadratic {k : Type*} [Field k] (p : Seminorm ℝ (ℝ × ℝ))
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ f : Fin 8 → ℝ × ℝ, (∀ i, f i ∈ U) →
      RealizableUpToScale k (fun i j => p (f i - f j))) :
    ∃ L W B : ℝ, ∀ x : ℝ × ℝ, p x ^ 2 = x.1 ^ 2 * L + x.2 ^ 2 * W + x.1 * x.2 * B := by
  obtain ⟨Q, qnorm, qinner, f, hf⟩ := WireGeometry.exists_normPreserving_map_of_realizable
    k p (realizePlaneGlobally p hU hne h)
  exact quadratic_of_normPreserving_map p f hf

end SpectralGeometry

end VPVNP
end Computability
end OAI
