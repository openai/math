import OAI.LinearAlgebra.FiniteFourier.DyadicPrimeOrbit
import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionDeformationBlock
import OAI.LinearAlgebra.FiniteFourier.PrimeAxisUnit
import Mathlib.LinearAlgebra.Basis.SMul

/-! # The binomial presentation of the prime cyclotomic factor

A frequency-one resolvent has scalar order-`p-1` power and survives in every
reduced residue fiber. Its powers give unit rescalings of the Fourier basis.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
namespace Deformation

open Polynomial Module Submodule
open scoped BigOperators

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

private theorem isUnit_scalar_of_unit_smul (f : A →ₗ[R] R) (hf : f 1 = 1)
    {r : R} {x : A} (h : IsUnit (r • x)) : IsUnit r := by
  have hinv : (r • x) * (↑h.unit⁻¹ : A) = 1 := h.mul_val_inv
  rw [smul_mul_assoc] at hinv
  have hmap := congrArg f hinv
  rw [map_smul, hf, smul_eq_mul] at hmap
  exact ⟨⟨r, _, hmap, (mul_comm ..).trans hmap⟩, rfl⟩

section Prime

variable {p : ℕ} [Fact p.Prime] (C : PrimeAxisOrbit p)
local notation "m" => (p - 1)
local notation "Aₚ" => AdjoinRoot (cyclotomic p R)
local notation "σₚ" => (primeAxisAction R p C.generator)

/-- The positive powers of the frequency-one vector form a basis with explicitly
unit diagonal change from the Rader Fourier basis; its zeroth power is one. -/
theorem exists_dyadicPrimeBinomialBasis (u : Rˣ) (hodd : 1 < m) (hpR : IsUnit (p : R))
    (hm : IsUnit ((m : ℕ) : R)) (hu : u^m = 1)
    (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val)) :
    ∃ (β : Rˣ) (Y : Aₚˣ) (scales : Fin m → Rˣ) (e : Basis (Fin m) R Aₚ),
      (Y : Aₚ) = dyadicPrimeFourier R C u ⟨1,hodd⟩ ∧
      (Y : Aₚ)^m = algebraMap R Aₚ β ∧
      (∀ j, e j = (Y : Aₚ)^j.val) ∧
      ∀ j, e j = (scales j : R) • dyadicPrimeFourier R C u j := by
  classical
  let z : Fin m := ⟨0, by omega⟩
  let o : Fin m := ⟨1, hodd⟩
  obtain ⟨b,hb⟩ := exists_dyadicPrimeFourier_basis R C u hm hu hs
  have hbz : b z = -1 := (hb z).trans (dyadicPrimeFourier_zero R C u _)
  have hfix : Module.End.eigenspace (σₚ).toLinearMap 1 = span R {(-1 : Aₚ)} := by
    simpa [z, dyadicPrimeFourier_zero] using dyadicPrimeFourier_eigenspace R C u hm hu hs z
  have hY : σₚ (b o) = (u : R) • b o := by
    simpa [hb, o] using dyadicPrimeFourier_eigen R C u hu o
  have hinv : (b o)^m ∈ Module.End.eigenspace (σₚ).toLinearMap 1 := by
    apply Module.End.mem_eigenspace_iff.mpr
    change σₚ ((b o)^m) = _
    rw [map_pow, hY, smul_pow, ← Units.val_pow_eq_pow_val, hu]
    rfl
  rw [hfix, mem_span_singleton] at hinv
  obtain ⟨a,ha⟩ := hinv
  have hβ : (b o)^m = algebraMap R Aₚ (-a) := by
    simpa [Algebra.smul_def] using ha.symm
  obtain ⟨hβu,hYu⟩ := primeAxis_isUnit_of_power_of_coord hpR b o (by simp) (by omega) hβ
  have hs₁ : b.repr 1 z = -1 := by
    have h := congrArg (fun x => b.repr x z) hbz
    simpa using (congrArg Neg.neg h).symm
  have hscale (j : Fin m) : ∃ l : Rˣ, (b o)^j.val = (l:R) • b j := by
    have he : (b o)^j.val ∈ Module.End.eigenspace (σₚ).toLinearMap ((u:R)^j.val) := by
      apply Module.End.mem_eigenspace_iff.mpr
      change σₚ ((b o)^j.val) = _
      rw [map_pow, hY, smul_pow]
    rw [dyadicPrimeFourier_eigenspace R C u hm hu hs j, ← hb, mem_span_singleton] at he
    obtain ⟨l,hl⟩ := he
    have hl' : IsUnit (l • b j) := hl ▸ hYu.pow _
    have hlU := isUnit_scalar_of_unit_smul (-b.coord z) (by simp [Basis.coord_apply, hs₁]) hl'
    exact ⟨hlU.unit, by simpa only [hlU.unit_spec] using hl.symm⟩
  choose l hl using hscale
  refine ⟨hβu.unit, hYu.unit, l, b.unitsSMul l, ?_, ?_, ?_, ?_⟩
  · simp [hb, o]
  · simpa only [hYu.unit_spec, hβu.unit_spec] using hβ
  · intro j
    rw [Basis.unitsSMul_apply, hYu.unit_spec, hl]
    rfl
  · intro j
    rw [Basis.unitsSMul_apply, hb]
    rfl

end Prime

/-- Evaluation of a binomial generator with a power basis is an algebra isomorphism. -/
def binomialPresentation {m : ℕ} (hm : 0 < m) [Nontrivial R]
    (β : R) (Y : A) (hY : Y^m = algebraMap R A β)
    (e : Basis (Fin m) R A) (he : ∀ j, e j = Y^j.val) :
    BinomialAxis m β ≃ₐ[R] A := by
  let f := AdjoinRoot.liftAlgHom ((X : R[X])^m - C β) (Algebra.ofId R A) Y
    (by simpa using sub_eq_zero.mpr hY)
  let b := binomialBasis hm β
  let l := b.equiv e (Equiv.refl _)
  have h : f.toLinearMap = l.toLinearMap := by
    apply b.ext
    intro j
    change f (b j) = l (b j)
    rw [Basis.equiv_apply, binomialBasis_apply, map_pow, AdjoinRoot.liftAlgHom_root]
    exact (he j).symm
  exact AlgEquiv.ofBijective f (show Function.Bijective f.toLinearMap by rw [h]; exact l.bijective)

@[simp] theorem binomialPresentation_root {m : ℕ} (hm : 0 < m) [Nontrivial R]
    (β : R) (Y : A) (hY : Y^m = algebraMap R A β)
    (e : Basis (Fin m) R A) (he : ∀ j, e j = Y^j.val) :
    binomialPresentation hm β Y hY e he (AdjoinRoot.root _) = Y :=
  AdjoinRoot.liftAlgHom_root ((X : R[X])^m - C β) (Algebra.ofId R A) Y (by simpa using sub_eq_zero.mpr hY)

end Deformation

end

end FiniteFourier
end LinearAlgebra
end OAI
