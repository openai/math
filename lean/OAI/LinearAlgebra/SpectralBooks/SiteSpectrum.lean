import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Raw
import OAI.LinearAlgebra.SpectralBooks.Spectrum

/-!
# Finite-party diagonal bounds and simultaneous extension constraints

Each coordinate tensor is a restriction of the full diagonal indexed by its
coordinate positions. Conversely a nonzero coefficient supplies a restriction
to the scalar unit. The resulting bounds give compactness for spectral
evaluations, which lets the old tensor prices in a site extension be prescribed
simultaneously once every finite list can be matched.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical NNReal
noncomputable section

section

namespace Crossing

variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable {B : I → Type*} [∀ i, Fintype (B i)]

/-- Expand a tensor in the local coordinate bases. A common diagonal label
selects the entire coordinate tuple. A distinguished site supplies its coefficient. -/
theorem restricts_from_coordinate_diagonal_equiv {L : Type*} [Fintype L]
    (e : L ≃ (∀ i, B i)) (T : (∀ i, B i) → K) :
    IsRestriction T (basisTensor (I := I) (fun (l : L) _ ↦ l)) := by
  classical
  let o : I := Classical.choice inferInstance
  let M (i : I) (b : B i) (a : ∀ i, B i) : K :=
    (if b = a i then 1 else 0) * (if i = o then T a else 1)
  apply (restriction_basisTensor_iff _ _).mpr
  refine ⟨fun i b l ↦ M i b (e l), fun b ↦ ?_⟩
  have hprod (a : ∀ i, B i) :
      (∏ i, M i (b i) a) = if b = a then T a else 0 := by
    simp only [M, Finset.prod_mul_distrib, Fintype.prod_boole, ← funext_iff]
    simp
  rw [e.sum_comp (fun a ↦ ∏ i, M i (b i) a)]
  simp [hprod]

/-- A single nonzero coefficient makes the scalar unit a local linear image. -/
theorem unit_restricts_of_nonzero {T : (∀ i, B i) → K} (h : T ≠ 0) :
    IsRestriction (fun _ : I → PUnit ↦ (1 : K)) T := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, T a ≠ 0 := by
    by_contra! hn
    exact h (funext hn)
  let o : I := Classical.choice inferInstance
  let M (i : I) (_ : PUnit) (b : B i) : K :=
    (if b = a i then 1 else 0) * (if i = o then (T a)⁻¹ else 1)
  refine ⟨M, fun _ ↦ ?_⟩
  have hprod (b : ∀ i, B i) :
      (∏ i, M i PUnit.unit (b i)) = if b = a then (T a)⁻¹ else 0 := by
    simp only [M, Finset.prod_mul_distrib, Fintype.prod_boole, ← funext_iff]
    simp
  simp [hprod, mul_ite, ha]

end Crossing

namespace SiteTensor.Raw

universe v

/-- A concrete diagonal of finite size supplies every coefficient array,
even if the coordinate spaces and the set of sites use different universes. -/
theorem restricts_diagonal (I : Type*) [Fintype I] [Nonempty I]
    {K : Type*} [Field K] (X : Raw.{v} I K) :
    X.Restricts (diagonal I K (ULift.{v} (Fin (Fintype.card (∀ i, X.Leg i))))) := by
  classical
  let e : ULift.{v} (Fin (Fintype.card (∀ i, X.Leg i))) ≃ (∀ i, X.Leg i) :=
    Equiv.ulift.trans (Fintype.equivFin _).symm
  have h := Crossing.restricts_from_coordinate_diagonal_equiv e X.coeff
  unfold Crossing.basisTensor at h
  convert! h using 1
  funext x
  simp only [diagonal]
  congr 1
  funext a
  split_ifs <;> simp_all

/-- Conversely the multiplicative unit is a restriction of every nonzero tensor. -/
theorem one_restricts_of_nonzero {I : Type*} [Fintype I] [Nonempty I]
    {K : Type*} [Field K] (X : Raw.{v} I K) (h : X.coeff ≠ 0) :
    (one I K).Restricts X :=
  Crossing.unit_restricts_of_nonzero h

end SiteTensor.Raw

/-- On the enlarged site set, finite compatibility gives agreement on all
old evaluations and retains any closed wire-distance constraint. This also
allows prescribed values on uncountably many old tensors. -/
theorem exists_matching_spectral_point {S A : Type*} [Semiring S]
    (restricts : S → S → Prop) (hrank : ∀ x, ∃ n : ℕ, restricts x n)
    (tensor : A → S) (target : A → ℝ≥0)
    (wire : Set (normalizedSpectrum restricts)) (hclosed : IsClosed wire)
    (hfinite : ∀ a : Finset A, ∃ f ∈ wire, ∀ i ∈ a, f.val (tensor i) = target i) :
    ∃ f ∈ wire, ∀ i, f.val (tensor i) = target i := by
  classical
  let : CompactSpace (normalizedSpectrum restricts) :=
    isCompact_iff_compactSpace.mp (isCompact_normalizedSpectrum restricts hrank)
  let C (a : A) : Set (normalizedSpectrum restricts) := {f | f.val (tensor a) = target a}
  have hc (a : A) : IsClosed (C a) :=
    isClosed_eq ((continuous_apply (tensor a)).comp continuous_subtype_val) continuous_const
  have hp : (wire ∩ ⋂ a, C a).Nonempty :=
    hclosed.isCompact.inter_iInter_nonempty _ hc (fun a ↦ by
      obtain ⟨f, hf, ha⟩ := hfinite a
      exact ⟨f, hf, Set.mem_iInter₂.mpr ha⟩)
  obtain ⟨f, hf, h⟩ := hp
  exact ⟨f, hf, Set.mem_iInter.mp h⟩

end

end

end SpectralBooks
end LinearAlgebra
end OAI
