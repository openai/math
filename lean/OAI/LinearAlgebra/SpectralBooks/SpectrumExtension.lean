import OAI.LinearAlgebra.SpectralBooks.SpectrumSeparation
import OAI.LinearAlgebra.SpectralBooks.SpectrumPolynomialSeparation
import OAI.LinearAlgebra.SpectralBooks.SpectrumComparisonExtension
import OAI.LinearAlgebra.SpectralBooks.GroundFieldComparison
import OAI.LinearAlgebra.SpectralBooks.TensorRestrictionDescent

/-! # Extending spectral evaluations

A point missing from a compact family of semiring homomorphisms can be
separated from that family by finitely many strict comparisons. Their
amplified sum contradicts strict comparison in the target semiring.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped NNReal
open Set

section

private theorem exists_finite_opposition {S E : Type*} [Semiring S]
    [TopologicalSpace E] [CompactSpace E] (f : S →+* ℝ≥0) (g : E → S →+* ℝ≥0)
    (hcont : ∀ s, Continuous (fun e ↦ g e s))
    (hne : ∀ e, f ≠ g e) :
    ∃ (J : Finset E) (A B : J → S), (∀ j, f (A j) < f (B j)) ∧
      (∀ e j, 0 < g e (B j)) ∧ ∀ e, ∃ j, g e (B j) < g e (A j) := by
  classical
  choose a b hf hg hpos using fun e ↦ exists_opposing_evaluations f (g e) (hne e)
  let U (e : E) := {q : E | g q (b e) < g q (a e)}
  have hopen (e : E) : IsOpen (U e) := isOpen_lt (hcont _) (hcont _)
  have hcover : (univ : Set E) ⊆ ⋃ e, U e :=
    fun e _ ↦ mem_iUnion.mpr ⟨e, hg e⟩
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  refine ⟨J, fun j ↦ a j.val, fun j ↦ b j.val, fun j ↦ hf j.val,
    fun e j ↦ (hpos j.val (g e)).2, ?_⟩
  intro e
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hJ (mem_univ e))
  obtain ⟨hj, he⟩ := mem_iUnion.mp hj
  exact ⟨⟨j, hj⟩, he⟩

/-- A normalized source homomorphism which respects every order comparison
of its images extends provided the target spectrum is compact and gives
strict comparison of positive powers. -/
theorem exists_spectrum_extension {S T : Type*} [CommSemiring S] [CommSemiring T]
    [Preorder T] (i : S →+* T) (f : S →+* ℝ≥0)
    (hmono : ∀ x y, i x ≤ i y → f x ≤ f y)
    (hcompact : IsCompact (normalizedSpectrum ((· ≤ ·) : T → T → Prop)))
    (hcompare : ∀ (x y : T), x ≠ 0 → y ≠ 0 →
      (∀ g : normalizedSpectrum ((· ≤ ·) : T → T → Prop), g.val x < g.val y) →
      ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → x ^ n ≤ C • y ^ n) :
    ∃ g : normalizedSpectrum ((· ≤ ·) : T → T → Prop), ∀ x, g.val (i x) = f x := by
  classical
  let E := normalizedSpectrum ((· ≤ ·) : T → T → Prop)
  let : CompactSpace E := isCompact_iff_compactSpace.mp hcompact
  let g (e : E) := (normalizedSpectrum.toRingHom e).comp i
  by_contra hnone
  have hne (e : E) : f ≠ g e := fun he ↦
    hnone ⟨e, fun x ↦ (DFunLike.congr_fun he x).symm⟩
  have hcont (x : S) : Continuous (fun e ↦ g e x) :=
    (continuous_apply (i x)).comp continuous_subtype_val
  obtain ⟨J, A, B, hf, hpos, hcover⟩ := exists_finite_opposition f g hcont hne
  obtain ⟨X, Y, hXY, hYX⟩ := exists_separating_pair_of_finite A B f (range g) hf
    (by rintro _ ⟨e, rfl⟩; exact hpos e) (by rintro _ ⟨e, rfl⟩; exact hcover e)
  exact hXY.not_ge (le_of_strict_restricted_spectral_comparison i f hmono hcompare Y X
    (fun e ↦ hYX (g e) ⟨e, rfl⟩))

namespace SiteTensor

universe v
variable {I F K : Type*} [Fintype I] [Nonempty I] [Field F] [Field K] [Algebra F K]

/-- Simultaneously extend a ground spectral point across any field extension. -/
theorem exists_spectrum_mapScalars
    (f : normalizedSpectrum (S := TensorClass.{v} I F) (· ≤ ·)) :
    ∃ g : normalizedSpectrum (S := TensorClass.{v} I K) (· ≤ ·),
      ∀ x, g.val (mapScalars (algebraMap F K) x) = f.val x :=
  exists_spectrum_extension (mapScalars (algebraMap F K)) (normalizedSpectrum.toRingHom f)
    (fun _ _ h ↦ spectral_le_of_baseChange f h) isCompact_spectrum (strictSpectralComparison I K)

/-- Scalar extension preserves the exact set of possible joint spectral values
on every family of tensors, including infinite families. -/
theorem range_joint_spectrum_mapScalars {ι : Type*} (x : ι → TensorClass.{v} I F) :
    range (fun g : normalizedSpectrum (S := TensorClass.{v} I K) (· ≤ ·) ↦
      fun j ↦ g.val (mapScalars (algebraMap F K) (x j))) =
    range (fun f : normalizedSpectrum (S := TensorClass.{v} I F) (· ≤ ·) ↦
      fun j ↦ f.val (x j)) := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨pullbackSpectrum (algebraMap F K) g, rfl⟩
  · rintro ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := exists_spectrum_mapScalars (K := K) f
    exact ⟨g, funext (fun j ↦ hg (x j))⟩

end SiteTensor
end

end SpectralBooks
end LinearAlgebra
end OAI
