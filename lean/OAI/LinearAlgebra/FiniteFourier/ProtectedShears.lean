import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! # Unit shears over protected coefficient rings

Simultaneous lifting of residues realizes an arbitrary shear as two shears with
unit coefficients, even when the original coefficient is a nonunit. The same
choice works across all maximal ideals of the protected ring.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R : Type*} [CommRing R]

/-- A finite algebra over a semilocal ring is semilocal. -/
theorem finite_maximalSpectrum_of_finite_algebra (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Finite (MaximalSpectrum R)] [Module.Finite R S] :
    Finite (MaximalSpectrum S) := by
  let (m : MaximalSpectrum R) : Finite (m.asIdeal.primesOver S) :=
    (Algebra.QuasiFinite.finite_primesOver (S := S) m.asIdeal).to_subtype
  let f (m : MaximalSpectrum S) : Σ n : MaximalSpectrum R, n.asIdeal.primesOver S :=
    ⟨⟨m.asIdeal.under R, inferInstance⟩, m.asIdeal, inferInstance, inferInstance⟩
  apply Finite.of_injective f
  intro m n h
  exact MaximalSpectrum.ext (congrArg (fun p : Σ n : MaximalSpectrum R, n.asIdeal.primesOver S =>
    p.2.val) h)

/-- Adjoining a root of unity to the protected base ring leaves finitely
many maximal ideals in the cyclotomic coefficient ring. -/
theorem finite_maximalSpectrum_adjoin_root (R : Type*) [CommRing R]
    [Finite (MaximalSpectrum R)] {E : Type*} [CommRing E] [Algebra R E]
    {ξ : E} {M : ℕ} (hM : 0 < M) (hξ : ξ ^ M = 1) :
    Finite (MaximalSpectrum (Algebra.adjoin R {ξ})) := by
  have hi : IsIntegral R ξ := IsIntegral.of_pow hM (hξ ▸ isIntegral_one)
  let : Module.Finite R (Algebra.adjoin R {ξ}) := Algebra.finite_adjoin_simple_of_isIntegral hi
  exact finite_maximalSpectrum_of_finite_algebra R _

private theorem isUnit_of_residues_ne_zero (x : R)
    (hx : ∀ m : MaximalSpectrum R, Ideal.Quotient.mk m.asIdeal x ≠ 0) : IsUnit x := by
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hn)
  exact hx ⟨m, hm⟩ (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)

/-- Over a semilocal ring with two invertible, every coefficient is a sum of two units. -/
theorem exists_unit_split [Finite (MaximalSpectrum R)] (h₂ : IsUnit (2 : R)) (μ : R) :
    ∃ t : R, IsUnit t ∧ IsUnit (μ - t) := by
  classical
  let T (m : MaximalSpectrum R) := Ideal.Quotient.mk m.asIdeal
  let x (m : MaximalSpectrum R) : R ⧸ m.asIdeal := if T m μ = 1 then -1 else 1
  have hx (m) : x m ≠ 0 ∧ T m μ - x m ≠ 0 := by
    have htwo : (2 : R ⧸ m.asIdeal) ≠ 0 := by
      simpa only [map_ofNat] using (h₂.map (T m)).ne_zero
    by_cases h : T m μ = 1
    · simpa [x, h, one_add_one_eq_two] using htwo
    · simp [x, h, sub_ne_zero]
  have hcop : Pairwise (fun m n : MaximalSpectrum R => IsCoprime m.asIdeal n.asIdeal) :=
    fun _ _ h => Ideal.isCoprime_of_isMaximal (fun he => h (MaximalSpectrum.ext he))
  obtain ⟨t, ht⟩ := Ideal.pi_quotient_surjective hcop x
  refine ⟨t, isUnit_of_residues_ne_zero _ (fun m => ?_),
    isUnit_of_residues_ne_zero _ (fun m => ?_)⟩
  · rw [ht m]
    exact (hx m).1
  · rw [map_sub, ht m]
    exact (hx m).2

/-- Each factor has an invertible coefficient and can therefore be obtained by
diagonal conjugation from the fixed unit shear. -/
theorem transvection_eq_mul_two_units [Finite (MaximalSpectrum R)] (h₂ : IsUnit (2 : R))
    {I : Type*} [Fintype I] [DecidableEq I] {i j : I} (hij : i ≠ j) (μ : R) :
    ∃ u v : Rˣ, Matrix.transvection i j μ =
      Matrix.transvection i j (u : R) * Matrix.transvection i j (v : R) := by
  obtain ⟨t, ht, ht'⟩ := exists_unit_split h₂ μ
  refine ⟨ht.unit, ht'.unit, ?_⟩
  rw [Matrix.transvection_mul_transvection_same _ _ hij, ht.unit_spec, ht'.unit_spec,
    add_sub_cancel]

/-- When the order is invertible in the coefficient domain, every nontrivial
Newton factor is a unit before passing to a field of fractions. -/
theorem newtonFactor_isUnit [IsDomain R] {n j : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ n)
    (hn : IsUnit (n : R)) (hj : 0 < j) (hjn : j < n) : IsUnit (1 - ζ ^ j) := by
  have hp : (ζ ^ j) ^ n = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hne := hζ.pow_ne_one_of_pos_of_lt hj.ne' hjn
  have hu := isUnit_of_dvd_unit (sub_one_dvd_natCast_of_pow_eq_one hp hne) hn
  simpa [neg_sub] using hu.neg

/-- In particular, a primitive root retains its exact order in every residue
field when its order is a unit in the coefficient domain. -/
theorem primitiveRoot_map_of_unit_order [IsDomain R] {S : Type*} [CommRing S] [Nontrivial S]
    (f : R →+* S) {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : IsUnit (n : R)) :
    IsPrimitiveRoot (f ζ) n := by
  have hpos : 0 < n := Nat.pos_of_ne_zero fun h => hn.ne_zero (by simp [h])
  apply IsPrimitiveRoot.mk_of_lt _ hpos (by rw [← map_pow, hζ.pow_eq_one, map_one])
  intro j hj hjn he
  have hu := (newtonFactor_isUnit hζ hn hj hjn).map f
  exact hu.ne_zero (by simp [he])

/-- The fixed parameters used to compile the protected three-`C` word
are all invertible when two is invertible. -/
theorem compiler_eighthRoot_units [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 8)
    (h₂ : IsUnit (2 : R)) :
    IsUnit ζ ∧ IsUnit (ζ - 1) ∧ IsUnit (ζ + 1) ∧ IsUnit (ζ ^ 2 + 1) := by
  have h₈ : IsUnit (8 : R) := by convert h₂.pow 3 using 1; norm_num
  have hsub (j : ℕ) (hj : 0 < j) (hj' : j < 8) : IsUnit (ζ ^ j - 1) := by
    simpa only [neg_sub] using (newtonFactor_isUnit hζ (by simpa using h₈) hj hj').neg
  refine ⟨hζ.isUnit (by decide), by simpa using hsub 1 (by decide) (by decide),
    isUnit_of_dvd_unit ?_ (hsub 2 (by decide) (by decide)),
    isUnit_of_dvd_unit ?_ (hsub 4 (by decide) (by decide))⟩
  · exact ⟨ζ - 1, by ring⟩
  · exact ⟨ζ ^ 2 - 1, by ring⟩

end FiniteFourier
end LinearAlgebra
end OAI
