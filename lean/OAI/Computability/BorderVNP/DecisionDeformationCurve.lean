import OAI.Computability.BorderVNP.DecisionDeformationCuts
import OAI.Computability.BorderVNP.BranchCurveAffineDimension
import Mathlib.RingTheory.Polynomial.Ideal

/-! # A curve above the isolated zero in the special fiber

For the affine coordinate ring, adjoin the deformation parameter and replace
each cut by its sum with the parameter times a perturbation. No genericity of
the perturbations is needed for the existence of the horizontal component.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Decision

open Polynomial

variable {R ι : Type*} [CommRing R]

/-- The equation `G + t ℓ` in the coordinate ring of the variety times the affine line. -/
noncomputable def perturbEquation (G ℓ : R) : Polynomial R := C G + X * C ℓ

private theorem isolated_special_fiber {G ℓ : ι → R} {m : Ideal R}
    (isolated : m ∈ (Ideal.span (Set.range G)).minimalPrimes) :
    m.comap constantCoeff ∈
      (Ideal.span (Set.range (fun i => perturbEquation (G i) (ℓ i))) ⊔
        Ideal.span {(X : Polynomial R)}).minimalPrimes := by
  let f : Polynomial R →+* R := constantCoeff
  let I := Ideal.span (Set.range (fun i => perturbEquation (G i) (ℓ i)))
  have surj : Function.Surjective f := constantCoeff_surjective
  have : m.IsPrime := isolated.isPrime
  have him : I.map f = Ideal.span (Set.range G) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [f, perturbEquation]
  have hker : RingHom.ker f = Ideal.span {X} := ker_constantCoeff
  refine ⟨⟨Ideal.comap_isPrime f m, sup_le (Ideal.map_le_iff_le_comap.mp ?_) ?_⟩, ?_⟩
  · exact him ▸ isolated.le
  · rw [← hker]
    exact Ideal.comap_mono bot_le
  · intro Q hQ hQm
    have : Q.IsPrime := hQ.1
    have hkQ : RingHom.ker f ≤ Q := hker ▸ le_sup_right.trans hQ.2
    have hQim := Ideal.map_isPrime_of_surjective surj hkQ
    have hsub : Ideal.span (Set.range G) ≤ Q.map f := him ▸ Ideal.map_mono (le_sup_left.trans hQ.2)
    have hlim : Q.map f ≤ m := Ideal.map_le_iff_le_comap.mpr hQm
    have hinv := Ideal.comap_mono (f := f) (isolated.2 ⟨hQim, hsub⟩ hlim)
    rwa [Ideal.comap_map_of_surjective f surj, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkQ] at hinv

/-- With one equation per dimension, every choice of affine perturbations has
a dominant irreducible curve through the specified isolated zero. -/
theorem deformation_curve {E A : Type*} [Field E] [CommRing A] [Algebra E A]
    [Algebra.FiniteType E A] {d : ℕ} (G ℓ : Fin d → A) (m : Ideal A) [m.IsMaximal]
    (height : m.height = d) (isolated : m ∈ (Ideal.span (Set.range G)).minimalPrimes) :
    ∃ P ∈ (Ideal.span (Set.range (fun i => perturbEquation (G i) (ℓ i)))).minimalPrimes,
      P < m.comap constantCoeff ∧ ringKrullDim (Polynomial A ⧸ P) = 1 ∧
      Function.Injective (Polynomial.aeval (R := E) (Ideal.Quotient.mk P X)) := by
  classical
  let eqns := Finset.univ.image (fun i => perturbEquation (G i) (ℓ i))
  have he : (eqns : Set (Polynomial A)) = Set.range (fun i => perturbEquation (G i) (ℓ i)) := by
    simp [eqns]
  let M := m.comap (constantCoeff : Polynomial A →+* A)
  have : M.IsMaximal := Ideal.comap_isMaximal_of_surjective constantCoeff constantCoeff_surjective
  have : M.LiesOver m := ⟨by ext x; change x ∈ m ↔ constantCoeff (C x) ∈ m; simp⟩
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing E A
  have : Algebra.FiniteType E (Polynomial A) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have hheight : (eqns.card : ℕ∞) < M.height := by
    rw [Polynomial.height_eq_height_add_one m M, height]
    have hcount : eqns.card ≤ d := (Finset.card_image_le).trans_eq (Fintype.card_fin d)
    exact_mod_cast Nat.lt_succ_of_le hcount
  obtain ⟨P, hP, hM, hd, hdom⟩ := Branch.exists_affine_curve (K := E) eqns X M
    (he ▸ isolated_special_fiber (ℓ := ℓ) isolated) hheight
  exact ⟨P, he ▸ hP, hM, hd, hdom⟩

end Decision

end BorderVNP
end Computability
end OAI
