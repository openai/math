import OAI.Computability.VPVNP.LinearNormalizationDirection
import OAI.Computability.VPVNP.LinearNormalizationRoot
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# A linear shear eliminating one generator

Given a relation on generators `g₀,…,gₙ`, choose a direction where the
highest homogeneous component of the relation is nonzero. Its restriction to
a line through the sheared generators gives an integral equation. Each original
generator is then integral over the algebra of the `n` sheared generators.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LinearNormalization

open MvPolynomial

private theorem aeval_line {K B A I : Type*} [CommSemiring K] [CommSemiring B] [CommSemiring A]
    [Algebra K B] [Algebra K A] [Algebra B A] [IsScalarTower K B A]
    (p : MvPolynomial I K) (h : I → B) (v : I → K) (x : A) :
    Polynomial.aeval x (line p h v) =
      aeval (fun i => algebraMap B A (h i) + v i • x) p := by
  let f : Polynomial B →ₐ[K] A := (Polynomial.aeval x).restrictScalars K
  change f (aeval _ p) = _
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun z : I → A => aeval z p)
  funext i
  simp [f, Algebra.smul_def, ← IsScalarTower.algebraMap_apply K B A]

/-- A nontrivial polynomial relation permits removing one generator by a linear
change of coordinates, with an integral extension of the resulting algebra. -/
theorem exists_integral_shear {K A : Type*} [Field K] [Infinite K] [CommRing A] [Algebra K A]
    {n : ℕ} (g : Fin (n + 1) → A)
    (hg : ¬ Function.Injective (aeval g : MvPolynomial (Fin (n + 1)) K →ₐ[K] A)) :
    ∃ v : Fin n → K, ∀ i : Fin (n + 1),
      IsIntegral (Algebra.adjoin K (Set.range (fun j : Fin n => g j.succ - v j • g 0))) (g i) := by
  classical
  rcases subsingleton_or_nontrivial A with hs | hs
  · refine ⟨0, fun i => ?_⟩
    rw [Subsingleton.elim (g i) 0]
    exact isIntegral_zero
  rw [injective_iff_map_eq_zero] at hg
  push Not at hg
  obtain ⟨p, hp, hne⟩ := hg
  obtain ⟨v, hv, htop⟩ := exists_direction hne
  let w (j : Fin n) := v j.succ * (v 0)⁻¹
  let sh (j : Fin n) := g j.succ - w j • g 0
  let B := Algebra.adjoin K (Set.range sh)
  let h : Fin (n + 1) → B :=
    Fin.cons 0 (fun j => ⟨sh j, Algebra.subset_adjoin ⟨j, rfl⟩⟩)
  let x := (v 0)⁻¹ • g 0
  have coords (i : Fin (n + 1)) : algebraMap B A (h i) + v i • x = g i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change (0 : A) + v 0 • ((v 0)⁻¹ • g 0) = g 0
      simp [smul_smul, hv]
    · change sh j + v j.succ • ((v 0)⁻¹ • g 0) = g j.succ
      simp [sh, w, smul_smul]
  have hroot : Polynomial.aeval x (line p h v) = 0 := by
    rw [aeval_line, funext coords]
    exact hp
  have hx : IsIntegral B x := isIntegral_of_line_root p h v x htop hroot
  refine ⟨w, fun i => ?_⟩
  change IsIntegral B (g i)
  rw [← coords i]
  exact isIntegral_algebraMap.add (hx.smul (v i))

end LinearNormalization

end VPVNP
end Computability
end OAI
