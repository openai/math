import Mathlib.Algebra.QuadraticAlgebra.AlgHom
import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionJetRoots
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # The quadratic algebra on each deformation axis

The defining quotient has coordinates in the basis `1, U`. Evaluation at two roots
whose difference is invertible identifies it with a product. At the other endpoint,
a new generator congruent to the old one modulo the nilpotent parameter gives an
invertible basis change.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial
open scoped QuadraticAlgebra

variable {R : Type*} [CommRing R]

/-- The quadratic relation on an axis after specializing its constant coefficient. -/
noncomputable def quadraticAxisPoly (c : R) : R[X] := X ^ 2 + X + C c

/-- The algebra obtained by adjoining a generator with `U² + U + c = 0`. -/
abbrev QuadraticAxis (c : R) := AdjoinRoot (quadraticAxisPoly c)

theorem quadraticAxis_root_relation (c : R) :
    AdjoinRoot.root (quadraticAxisPoly c) ^ 2 + AdjoinRoot.root (quadraticAxisPoly c) +
      algebraMap R (QuadraticAxis c) c = 0 := by
  have h := AdjoinRoot.mk_self (f := quadraticAxisPoly c)
  change AdjoinRoot.mk (quadraticAxisPoly c) (X^2 + X + C c) = 0 at h
  rw [map_add, map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  exact h

private abbrev Coordinates (c : R) := QuadraticAlgebra R (-c) (-1)

private theorem coordinates_root_relation (c : R) :
    (ω : Coordinates c) ^ 2 + ω + algebraMap R _ c = 0 := by
  ext <;> simp [sq]

private noncomputable def coordinateLift {A : Type*} [CommRing A] [Algebra R A]
    (c : R) (v : A) (hv : v ^ 2 + v + algebraMap R A c = 0) :
    Coordinates c →ₐ[R] A :=
  QuadraticAlgebra.lift ⟨v, by
    simp only [Algebra.smul_def, map_neg, map_one, mul_one, neg_one_mul]
    linear_combination hv⟩

@[simp] private theorem coordinateLift_omega {A : Type*} [CommRing A] [Algebra R A]
    (c : R) (v : A) (hv) : coordinateLift c v hv ω = v := by
  simp [coordinateLift]

/-- Identify the monic quotient with its two coordinates. -/
noncomputable def quadraticAxisEquiv (c : R) :
    QuadraticAxis c ≃ₐ[R] QuadraticAlgebra R (-c) (-1) := by
  let f := AdjoinRoot.liftAlgHom (quadraticAxisPoly c) (Algebra.ofId R (Coordinates c))
    (ω : Coordinates c) (by simpa [quadraticAxisPoly] using coordinates_root_relation c)
  let g := coordinateLift c (AdjoinRoot.root (quadraticAxisPoly c)) (quadraticAxis_root_relation c)
  exact AlgEquiv.ofAlgHom f g (QuadraticAlgebra.algHom_ext (by simp [f, g]))
    (AdjoinRoot.algHom_ext (by simp [f, g]))

@[simp] theorem quadraticAxisEquiv_root (c : R) :
    quadraticAxisEquiv c (AdjoinRoot.root (quadraticAxisPoly c)) = ω := by
  exact AdjoinRoot.liftAlgHom_root (quadraticAxisPoly c) (Algebra.ofId R (Coordinates c)) ω
    (by simpa [quadraticAxisPoly] using coordinates_root_relation c)

private noncomputable def twoPointEval (c a b : R) (ha : a^2+a+c=0) (hb : b^2+b+c=0) :
    Coordinates c →ₐ[R] R × R :=
  (coordinateLift c a (by simpa using ha)).prod (coordinateLift c b (by simpa using hb))

private theorem twoPointEval_apply (c a b : R) (ha hb) (q : Coordinates c) :
    twoPointEval c a b ha hb q = (q.re + q.im*a, q.re + q.im*b) := by
  simp [twoPointEval, coordinateLift]

private theorem twoPointEval_bijective (c a b : R) (ha hb) (h : IsUnit (a-b)) :
    Function.Bijective (twoPointEval c a b ha hb) := by
  constructor
  · intro x y hxy
    rw [twoPointEval_apply, twoPointEval_apply] at hxy
    have hx := congrArg Prod.fst hxy
    have hy := congrArg Prod.snd hxy
    dsimp at hx hy
    have hi : x.im = y.im := h.mul_left_inj.mp (by linear_combination hx - hy)
    exact QuadraticAlgebra.ext (by simpa only [hi, add_left_inj] using hx) hi
  · rintro ⟨x, y⟩
    let slope := (x-y) * (↑h.unit⁻¹ : R)
    have hs : slope * (a-b) = x-y := by
      rw [show a-b = (h.unit : R) from h.unit_spec.symm]
      simp [slope, mul_assoc]
    refine ⟨⟨y-slope*b, slope⟩, ?_⟩
    rw [twoPointEval_apply]
    apply Prod.ext
    · dsimp
      linear_combination hs
    · dsimp
      ring

/-- Evaluation at the two roots of the split endpoint. -/
noncomputable def quadraticAxisSplit (c a b : R) (ha : a^2+a+c=0) (hb : b^2+b+c=0)
    (h : IsUnit (a-b)) : QuadraticAxis c ≃ₐ[R] R × R :=
  (quadraticAxisEquiv c).trans (AlgEquiv.ofBijective _ (twoPointEval_bijective c a b ha hb h))

@[simp] theorem quadraticAxisSplit_root (c a b : R) (ha hb h) :
    quadraticAxisSplit c a b ha hb h (AdjoinRoot.root (quadraticAxisPoly c)) = (a,b) := by
  simp [quadraticAxisSplit, twoPointEval]

/-- Sending the generator to a root congruent to the original generator modulo a
nilpotent scalar induces an isomorphism. Its determinant in the two power bases
is the coefficient of the original generator, congruent to one. -/
noncomputable def quadraticAxisChange {c d z : R} (hz : IsNilpotent z) (v : QuadraticAxis c)
    (hv : v ^ 2 + v + algebraMap R _ d = 0)
    (hcong : algebraMap R _ z ∣ v - AdjoinRoot.root (quadraticAxisPoly c)) :
    QuadraticAxis d ≃ₐ[R] QuadraticAxis c := by
  let e := quadraticAxisEquiv c
  have hroot : (e v)^2 + e v + algebraMap R _ d = 0 := by
    simpa only [map_add, map_pow, AlgEquiv.commutes, map_zero] using congrArg e hv
  let f := coordinateLift d (e v) hroot
  have hunit : IsUnit (e v).im := by
    obtain ⟨w, hw⟩ := hcong
    have hi : (e v).im - 1 = z * (e w).im := by
      have heq : e v - (ω : Coordinates c) = algebraMap R _ z * e w := by
        simpa only [map_sub, map_mul, e.commutes, e, quadraticAxisEquiv_root] using congrArg e hw
      simpa using congrArg QuadraticAlgebra.im heq
    have hn := (Commute.all z (e w).im).isNilpotent_mul_right hz
    rw [← hi] at hn
    simpa using hn.isUnit_add_one
  exact (quadraticAxisEquiv d).trans
    ((AlgEquiv.ofBijective f ((QuadraticAlgebra.isUnit_im_omega_iff_bijective f).mp
      (by simpa [f] using hunit))).trans e.symm)

@[simp] theorem quadraticAxisChange_root {c d z : R} (hz : IsNilpotent z)
    (v : QuadraticAxis c) (hv hcong) :
    quadraticAxisChange (d := d) hz v hv hcong (AdjoinRoot.root (quadraticAxisPoly d)) = v := by
  simp [quadraticAxisChange]

/-- Near zero, the deformed quadratic algebra splits, with the two evaluation
coordinates ordered by their residues `0` and `-1`. -/
theorem exists_quadraticAxisSplitAtZero (z ρ : R) (hz : IsNilpotent z) :
    ∃ e : QuadraticAxis (ρ*z) ≃ₐ[R] R × R,
      z ∣ (e (AdjoinRoot.root (quadraticAxisPoly (ρ*z)))).1 ∧
      z ∣ (e (AdjoinRoot.root (quadraticAxisPoly (ρ*z)))).2 + 1 := by
  obtain ⟨a, b, ha, hb, ea, eb, hu⟩ := quadraticRootsAtZero z ρ hz
  exact ⟨quadraticAxisSplit _ a b ea eb hu, by simpa using ha, by simpa using hb⟩

/-- At one, the unique lifted generator gives the quadratic part of the isomorphism
from the deformed algebra to the original algebra. -/
theorem exists_quadraticAxisChangeAtOne (z ρ : R) (hz : IsNilpotent z)
    (hdisc : IsUnit (1-4*ρ)) :
    ∃ e : QuadraticAxis (ρ*(1+z)) ≃ₐ[R] QuadraticAxis ρ,
      algebraMap R _ z ∣ e (AdjoinRoot.root (quadraticAxisPoly (ρ*(1+z)))) -
        AdjoinRoot.root (quadraticAxisPoly ρ) := by
  let ι := algebraMap R (QuadraticAxis ρ)
  have hdisc' : IsUnit (1 - 4 * ι ρ) := by
    simpa only [map_sub, map_one, map_mul, map_ofNat] using hdisc.map ι
  have hroot := quadraticAxis_root_relation ρ
  obtain ⟨v, ⟨hc, hv⟩, _⟩ := quadraticRootAtOne (hz.map ι) hroot
    (quadraticDerivative_isUnit hroot hdisc')
  have hv' : v^2 + v + ι (ρ*(1+z)) = 0 := by simpa [ι] using hv
  exact ⟨quadraticAxisChange hz v hv' hc, by rwa [quadraticAxisChange_root]⟩

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
