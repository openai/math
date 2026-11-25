import OAI.Computability.BorderVNP.GeneratorNormalization
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Algebraic.Basic

/-! # Generic finite fibers of an affine map in equal dimensions

For a domain of transcendence degree at most `d`, every coordinate satisfies
a nonzero polynomial over the formal ring in the `d` outputs. Keep one
nonzero coefficient from each such relation. A nonzero function on the domain
also divides the image of a nonzero polynomial in the outputs. Thus a single
choice of output values avoids that function's zero set and gives finite
fibers, even after field extension.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Decision

open MvPolynomial

variable {E A : Type*} [Field E] [CommRing A] [IsDomain A] [Algebra E A] {d : ℕ}

omit [IsDomain A] in
private theorem coordinate_relation (g : Fin d → A)
    (dimension : Algebra.trdeg E A ≤ d) (x : A) :
    ∃ p : Polynomial (MvPolynomial (Fin d) E), p ≠ 0 ∧ p.eval₂ (aeval g).toRingHom x = 0 := by
  let v : Fin (d+1) → A := Fin.cons (α := fun _ => A) x g
  have dep : ¬ AlgebraicIndependent E v := by
    intro ind
    have h := ind.lift_cardinalMk_le_trdeg.trans (Cardinal.lift_le.mpr dimension)
    simp at h
  rw [algebraicIndependent_iff] at dep
  push Not at dep
  obtain ⟨f, hf, hne⟩ := dep
  let e := finSuccEquiv E d
  let ev := (Polynomial.eval₂RingHom (aeval g).toRingHom x).comp e.toRingHom
  have hev : ev = (aeval v).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ev, e, finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [ev, e, v, finSuccEquiv_X_zero]
      · simp [ev, e, v, finSuccEquiv_X_succ]
  exact ⟨e f, fun h => hne (e.injective (h.trans (map_zero e).symm)),
    (RingHom.congr_fun hev f).trans hf⟩

/-- A nonzero test in the target coordinates whose nonvanishing makes every
geometric fiber finite on the recorded coordinates and disjoint from the zero
set of the given function. -/
theorem generic_finite_fiber_test (g : Fin d → A) (dimension : Algebra.trdeg E A ≤ d)
    {m : ℕ} (coords : Fin m → A) (avoid : A) (hn : avoid ≠ 0) :
    ∃ test : MvPolynomial (Fin d) E, test ≠ 0 ∧ ∀ (L : Type*) [Field L] [Algebra E L]
      (b : Fin d → L), aeval b test ≠ 0 →
      (Set.range fun h : {h : A →ₐ[E] L // ∀ i, h (g i) = b i} =>
        fun j => h.val (coords j)).Finite ∧
      ∀ h : A →ₐ[E] L, (∀ i, h (g i) = b i) → h avoid ≠ 0 := by
  classical
  let φ := aeval (R := E) g
  let := φ.toRingHom.toAlgebra
  have algebraic (x : A) : IsAlgebraic (MvPolynomial (Fin d) E) x := coordinate_relation g dimension x
  obtain ⟨f, hf, a, ha⟩ := (algebraic avoid).exists_nonzero_dvd (mem_nonZeroDivisors_iff_ne_zero.mpr hn)
  choose p hp hroot using fun j => algebraic (coords j)
  have coeff (j : Fin m) : ∃ k, (p j).coeff k ≠ 0 := by
    by_contra! hall
    exact hp j (Polynomial.ext (by simpa using hall))
  choose k hk using coeff
  let test := f * ∏ j, (p j).coeff (k j)
  refine ⟨test, mul_ne_zero hf (Finset.prod_ne_zero_iff.mpr fun j _ => hk j), fun L _ _ b ht => ?_⟩
  let ev := aeval (R := E) b
  have good : ev f ≠ 0 ∧ ∀ j, ev ((p j).coeff (k j)) ≠ 0 := by
    simpa [test, Finset.prod_ne_zero_iff, ev] using ht
  have cmp (h : A →ₐ[E] L) (he : ∀ i, h (g i) = b i) : h.comp φ = ev := by
    ext i
    simpa [φ, ev] using he i
  have nz (j : Fin m) : (p j).map ev.toRingHom ≠ 0 := by
    intro h
    have h0 := congrArg (fun p : Polynomial L => p.coeff (k j)) h
    exact good.2 j (by simpa using h0)
  constructor
  · apply (Set.Finite.pi' fun j => Polynomial.finite_setOfPred_isRoot (nz j)).subset
    rintro _ ⟨⟨h, he⟩, rfl⟩ j
    have root := congrArg h (hroot j)
    change h.toRingHom ((p j).eval₂ φ.toRingHom (coords j)) = h.toRingHom 0 at root
    rw [Polynomial.hom_eval₂, map_zero, show h.toRingHom.comp φ.toRingHom = ev.toRingHom from
      congrArg AlgHom.toRingHom (cmp h he)] at root
    exact (Polynomial.eval_map ..).trans root
  · intro h he hz
    apply good.1
    rw [← cmp h he]
    change h (φ f) = 0
    change φ f = avoid * a at ha
    rw [ha, map_mul, hz, zero_mul]

private theorem eval_along_line {L : Type*} [Field L] [Algebra E L] (u : Fin d → E)
    (t : L) (test : MvPolynomial (Fin (d+1)) E) :
    Polynomial.aeval t (aeval (Fin.cons (α := fun _ => Polynomial E) Polynomial.X
      (fun i => Polynomial.X * Polynomial.C (u i))) test) =
      aeval (Fin.cons (α := fun _ => L) t (fun i => t * algebraMap E L (u i))) test := by
  let slopes := Fin.cons (α := fun _ => Polynomial E) Polynomial.X
    (fun i => Polynomial.X * Polynomial.C (u i))
  let b := Fin.cons (α := fun _ => L) t (fun i => t * algebraMap E L (u i))
  have comp : (Polynomial.aeval (R := E) t).comp (aeval slopes) = aeval (R := E) b := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [slopes, b]
    · simpa [slopes, b] using mul_comm (algebraMap E L (u j)) t
  exact DFunLike.congr_fun comp test

/-- Choose a line of ground-field slopes through the origin avoiding the
test at its generic point, over every extension containing a transcendental
value of the line parameter. -/
theorem generic_line_avoids (K : Type*) [Field K] [Infinite K] [Algebra K E]
    {test : MvPolynomial (Fin (d+1)) E} (htest : test ≠ 0) :
    ∃ c : Fin d → K, ∀ (L : Type*) [Field L] [Algebra E L] (t : L),
      Transcendental E t →
      aeval (Fin.cons (α := fun _ => L) t (fun i => t * algebraMap E L (algebraMap K E (c i)))) test ≠ 0 := by
  obtain ⟨a, ha⟩ := Generator.exists_base_nonzero K (p := test * X 0) (mul_ne_zero htest (X_ne_zero _))
  have hn : eval (algebraMap K E ∘ a) test ≠ 0 ∧ algebraMap K E (a 0) ≠ 0 := by simpa using ha
  let c (i : Fin d) := a i.succ / a 0
  let slopes := Fin.cons (α := fun _ => Polynomial E) Polynomial.X
    (fun i => Polynomial.X * Polynomial.C (algebraMap K E (c i)))
  let P := aeval slopes test
  have p_ne : P ≠ 0 := by
    intro hz
    have he := eval_along_line (fun i => algebraMap K E (c i)) (algebraMap K E (a 0)) test
    change Polynomial.aeval (algebraMap K E (a 0)) P = _ at he
    rw [hz, map_zero] at he
    have b : Fin.cons (α := fun _ => E) (algebraMap K E (a 0))
        (fun i => algebraMap K E (a 0) * algebraMap E E (algebraMap K E (c i))) = algebraMap K E ∘ a := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · change algebraMap K E (a 0) * algebraMap K E (a j.succ / a 0) = algebraMap K E (a j.succ)
        rw [map_div₀, mul_div_cancel₀ _ hn.2]
    rw [b] at he
    exact hn.1 he.symm
  refine ⟨c, fun L _ _ t htrans => ?_⟩
  rw [← eval_along_line (fun i => algebraMap K E (c i)) t test]
  exact fun he => p_ne (transcendental_iff_injective.mp htrans (he.trans (map_zero _).symm))

end Decision

end BorderVNP
end Computability
end OAI
