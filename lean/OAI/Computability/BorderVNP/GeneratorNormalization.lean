import OAI.Computability.VPVNP.LinearNormalization

/-! # Linear normalization over a prescribed infinite field of constants

The generic fibers in Sections 15.1, 15.2 and 15.4 are defined over extension fields.
Their slicing equations must use coefficients in the original field. The nonvanishing
locus of an extension-field polynomial meets the base-field grid. This allows each shear
in the linear Noether normalization argument to use base-field coefficients.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Generator

open MvPolynomial VPVNP.LinearNormalization

/-- The affine grid over an infinite subfield detects polynomials over the extension field. -/
theorem exists_base_nonzero (K : Type*) [Field K] [Infinite K] {E ι : Type*} [Field E]
    [Algebra K E] {p : MvPolynomial ι E} (hp : p ≠ 0) :
    ∃ a : ι → K, eval (algebraMap K E ∘ a) p ≠ 0 := by
  by_contra! he
  apply hp
  apply MvPolynomial.funext_set (fun _ => Set.range (algebraMap K E))
    (fun _ => Set.infinite_range_of_injective (algebraMap K E).injective)
  intro x hx
  choose a ha using fun i => hx i (Set.mem_univ i)
  have h : x = algebraMap K E ∘ a := by
    funext i
    exact (ha i).symm
  simp [h, he]

variable {K E A : Type*} [Field K] [Infinite K] [Field E] [Algebra K E]
  [CommRing A] [Nontrivial A] [Algebra E A] [Algebra K A] [IsScalarTower K E A]

private theorem base_shear {n : ℕ} (g : Fin (n+1) → A)
    (dep : ¬ Function.Injective (aeval g : MvPolynomial (Fin (n+1)) E →ₐ[E] A)) :
    ∃ v : Fin n → K, ∀ i : Fin (n+1),
      IsIntegral (Algebra.adjoin E (Set.range (fun j : Fin n => g j.succ - v j • g 0))) (g i) := by
  classical
  rw [injective_iff_map_eq_zero] at dep
  push Not at dep
  obtain ⟨p, hp, hne⟩ := dep
  obtain ⟨w, hw⟩ := exists_base_nonzero K (mul_ne_zero (X_ne_zero (R := E) (0 : Fin (n+1)))
    (topComponent_ne_zero hne))
  rw [map_mul, mul_ne_zero_iff, eval_X] at hw
  let v := algebraMap K E ∘ w
  let slopes (j : Fin n) := w j.succ * (w 0)⁻¹
  let sh (j : Fin n) := g j.succ - slopes j • g 0
  let B := Algebra.adjoin E (Set.range sh)
  let h : Fin (n+1) → B := Fin.cons 0 (fun j => ⟨sh j, Algebra.subset_adjoin ⟨j, rfl⟩⟩)
  let x := (v 0)⁻¹ • g 0
  have coords (i : Fin (n+1)) : algebraMap B A (h i) + v i • x = g i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change (0 : A) + v 0 • ((v 0)⁻¹ • g 0) = _
      simp [smul_smul, show v 0 ≠ 0 from hw.1]
    · change (g j.succ - slopes j • g 0) + v j.succ • ((v 0)⁻¹ • g 0) = _
      rw [smul_smul, ← algebraMap_smul E (slopes j) (g 0)]
      simp [v, slopes]
  have root : Polynomial.aeval x (line p h v) = 0 := by
    let f : Polynomial B →ₐ[E] A := (Polynomial.aeval x).restrictScalars E
    change f (aeval _ p) = 0
    rw [MvPolynomial.comp_aeval_apply]
    have hsub : (fun i => f (Polynomial.C (h i) + Polynomial.C (algebraMap E B (v i)) *
        Polynomial.X)) = g := by
      funext i
      simpa [f, Algebra.smul_def, ← IsScalarTower.algebraMap_apply E B A] using coords i
    change aeval _ p = 0
    rw [show (fun i => f ((Polynomial.C (h i) + Polynomial.C (algebraMap E B (v i)) *
      Polynomial.X))) = g from hsub]
    exact hp
  have hx := isIntegral_of_line_root p h v x hw.2 root
  refine ⟨slopes, fun i => ?_⟩
  change IsIntegral B (g i)
  rw [← coords i]
  exact isIntegral_algebraMap.add (hx.smul (v i))

/-- Normalize an integral tuple over `E` with linear forms from the subfield `K`.
The number of surviving forms is at most the input dimension. -/
theorem normalize_over_base {n : ℕ} (g : Fin n → A)
    (hg : ∀ a : A, IsIntegral (Algebra.adjoin E (Set.range g)) a) :
    ∃ r ≤ n, ∃ Q : Fin r → A,
      (∀ j, Q j ∈ Submodule.span K (Set.range g)) ∧
      Function.Injective (aeval Q : MvPolynomial (Fin r) E →ₐ[E] A) ∧
      ∀ a : A, IsIntegral (Algebra.adjoin E (Set.range Q)) a := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, g, fun j => j.elim0, ?_, hg⟩
    intro p q eq
    rw [eq_C_of_isEmpty p, eq_C_of_isEmpty q] at eq ⊢
    exact congrArg C ((algebraMap E A).injective (by simpa only [aeval_C] using eq))
  | succ n ih =>
    by_cases hi : Function.Injective (aeval g : MvPolynomial (Fin (n+1)) E →ₐ[E] A)
    · exact ⟨_, le_rfl, g, fun j => Submodule.subset_span ⟨j, rfl⟩, hi, hg⟩
    obtain ⟨v, hv⟩ := base_shear (K := K) g hi
    let g' (j : Fin n) := g j.succ - v j • g 0
    obtain ⟨r, hr, Q, hQ, hinj, hint⟩ := ih g' (fun a =>
      integral_over_new_generators (Algebra.adjoin E (Set.range g')) g hv a (hg a))
    have hs : Submodule.span K (Set.range g') ≤ Submodule.span K (Set.range g) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨i.succ, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    exact ⟨r, hr.trans (Nat.le_succ _), Q, fun j => hs (hQ j), hinj, hint⟩

end Generator

end BorderVNP
end Computability
end OAI
