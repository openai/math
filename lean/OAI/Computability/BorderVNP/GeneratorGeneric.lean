import OAI.Computability.BorderVNP.Model
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Generic truth of Boolean combinations under polynomial maps

For an infinite scalar field, a truth set contains a dense Zariski open set precisely when
it contains the nonvanishing locus of a nonzero polynomial. If the image of a polynomial
map escapes every proper closed set in a finite collection, all their membership tests have
the same generic values before and after substitution. This is the finite-union step of
Corollary 15.6 and places no bound on the number of tests.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Generator

open MvPolynomial Set

/-- Zariski topology on the actual affine points, induced from the prime spectrum. -/
noncomputable abbrev affineTopology (ι K : Type*) [Field K] : TopologicalSpace (ι → K) :=
  TopologicalSpace.induced (pointToPoint (k := K) (K := K)) inferInstance

variable {ι κ K : Type*} [Field K]

/-- Use the affine Zariski topology for the point-set statements in this module. -/
noncomputable local instance pointTopologyGeneric : TopologicalSpace (ι → K) := affineTopology ι K

/-- The coefficient-identity closure used for border circuits is affine topological closure. -/
theorem affine_closure (S : Set (ι → K)) : closure S = imageClosure S := by
  ext x
  rw [closure_induced (f := pointToPoint (k := K) (K := K)), ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    vanishingIdeal_pointToPoint]
  change (∀ q ∈ vanishingIdeal K S, q ∈ vanishingIdeal K {x}) ↔ _
  simp only [mem_vanishingIdeal_iff, forall_mem_singleton]
  rfl

/-- A property holding throughout a dense open subset of affine space. -/
def Generic (S : Set (ι → K)) : Prop := ∃ U : Set (ι → K), IsOpen U ∧ Dense U ∧ U ⊆ S

/-- The basic open set where `p` is nonzero. -/
def principalOpen (p : MvPolynomial ι K) : Set (ι → K) := {x | eval x p ≠ 0}

private theorem principalOpen_isOpen (p : MvPolynomial ι K) : IsOpen (principalOpen p) := by
  apply isClosed_compl_iff.mp
  rw [← closure_subset_iff_isClosed, affine_closure]
  intro x hx
  exact fun hn => hn (hx p (fun _ hy => not_ne_iff.mp hy))

/-- The nonvanishing locus of any nonzero polynomial is Zariski dense. -/
theorem principalOpen_dense [Infinite K] {p : MvPolynomial ι K} (hp : p ≠ 0) :
    Dense (principalOpen p) := by
  rw [dense_iff_closure_eq, affine_closure, eq_univ_iff_forall]
  intro x q hq
  have hprod : q * p = 0 := MvPolynomial.funext fun y => by
    by_cases h : eval y p = 0
    · simp [h]
    · simp [hq y h]
  simp [(mul_eq_zero.mp hprod).resolve_right hp]

/-- Every nonempty affine open contains a nonempty principal open. -/
theorem principalOpen_inside {U : Set (ι → K)} (hu : IsOpen U) (hne : U.Nonempty) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ principalOpen p ⊆ U := by
  obtain ⟨x, hx⟩ := hne
  have hcx : x ∉ imageClosure Uᶜ := by
    rwa [← affine_closure, hu.isClosed_compl.closure_eq, notMem_compl_iff]
  change ¬ ∀ p : MvPolynomial ι K, (∀ y ∈ Uᶜ, eval y p = 0) → eval x p = 0 at hcx
  push Not at hcx
  obtain ⟨p, hpu, hpx⟩ := hcx
  refine ⟨p, fun e => hpx (e ▸ map_zero _), fun y hy => ?_⟩
  by_contra hyn
  exact hy (hpu y hyn)

/-- Over an infinite field, a generic property holds on a nonempty principal open, and conversely. -/
theorem generic_iff [Infinite K] (S : Set (ι → K)) :
    Generic S ↔ ∃ p : MvPolynomial ι K, p ≠ 0 ∧ principalOpen p ⊆ S := by
  constructor
  · rintro ⟨U, hu, hd, hus⟩
    obtain ⟨p, hp, hpu⟩ := principalOpen_inside hu hd.nonempty
    exact ⟨p, hp, hpu.trans hus⟩
  · rintro ⟨p, hp, hsub⟩
    exact ⟨_, principalOpen_isOpen p, principalOpen_dense hp, hsub⟩

private theorem generic_congr_on [Infinite K] {S T U : Set (ι → K)}
    (hu : Generic U) (h : ∀ x ∈ U, (x ∈ S ↔ x ∈ T)) : Generic S ↔ Generic T := by
  obtain ⟨p, hp, hpu⟩ := (generic_iff U).mp hu
  have forward (A B : Set (ι → K)) (e : ∀ x ∈ U, x ∈ A → x ∈ B) :
      Generic A → Generic B := by
    intro ha
    obtain ⟨q, hq, hqa⟩ := (generic_iff A).mp ha
    refine (generic_iff B).mpr ⟨p * q, mul_ne_zero hp hq, fun x hx => ?_⟩
    change eval x (p * q) ≠ 0 at hx
    rw [map_mul, mul_ne_zero_iff] at hx
    exact e x (hpu hx.1) (hqa hx.2)
  exact ⟨forward S T fun x hx => (h x hx).mp, forward T S fun x hx => (h x hx).mpr⟩

/-- A proper algebraic set missed by one image point has a polynomial equation whose
pullback along the map is a nonzero polynomial. -/
theorem exists_pulled_equation {Z : Set (ι → K)} (hz : IsClosed Z)
    (G : ι → MvPolynomial κ K) (hes : ¬ range (fun t i => eval t (G i)) ⊆ Z) :
    ∃ p : MvPolynomial ι K, (∀ x ∈ Z, eval x p = 0) ∧ eval₂ C G p ≠ 0 := by
  rw [Set.not_subset] at hes
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hes
  rw [← hz.closure_eq, affine_closure] at ht
  change ¬ ∀ p : MvPolynomial ι K, (∀ x ∈ Z, eval x p = 0) → eval _ p = 0 at ht
  push Not at ht
  obtain ⟨p, hp, hpt⟩ := ht
  refine ⟨p, hp, fun e => hpt ?_⟩
  have pull : eval t (eval₂ C G p) = eval (fun i => eval t (G i)) p := by
    rw [eval_eval₂]
    have : (eval t).comp C = RingHom.id K := by ext; simp
    rw [this, eval₂_id]
  rw [← pull, e, map_zero]

private theorem generic_constant {α : Type*} (c : Prop) : Generic {_x : α → K | c} ↔ c := by
  constructor
  · rintro ⟨U, _, hd, hU⟩
    obtain ⟨x, hx⟩ := hd.nonempty
    exact hU hx
  · intro hc
    exact ⟨univ, isOpen_univ, dense_univ, fun _ _ => hc⟩

/-- Every finite Boolean combination of closed-set tests preserves its generic truth value
under a polynomial map escaping each proper test set. The Boolean truth table is arbitrary. -/
theorem generic_boolean_pullback [Infinite K] {j : Type*} [Fintype j] (Z : j → Set (ι → K))
    (closed : ∀ i, IsClosed (Z i)) (G : ι → MvPolynomial κ K)
    (escapes : ∀ i, Z i ≠ univ → ¬ range (fun t k => eval t (G k)) ⊆ Z i)
    (test : (j → Prop) → Prop) :
    Generic {x | test (fun i => x ∈ Z i)} ↔
      Generic {t | test (fun i => (fun k => eval t (G k)) ∈ Z i)} := by
  classical
  have hchoose (i : j) : ∃ p : MvPolynomial ι K, eval₂ C G p ≠ 0 ∧
      (Z i ≠ univ → ∀ x ∈ Z i, eval x p = 0) := by
    by_cases hi : Z i = univ
    · exact ⟨1, by simp, fun h => (h hi).elim⟩
    obtain ⟨p, hp, hG⟩ := exists_pulled_equation (closed i) G (escapes i hi)
    exact ⟨p, hG, fun _ => hp⟩
  choose p hGp hz using hchoose
  let q := ∏ i, p i
  have hGq : eval₂ C G q ≠ 0 := by
    change eval₂Hom C G (∏ i, p i) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hGp i
  have hq : q ≠ 0 := fun e => hGq (e ▸ map_zero (eval₂Hom C G))
  have value (x : ι → K) (hx : eval x q ≠ 0) :
      (fun i => x ∈ Z i) = (fun i => Z i = univ) := by
    change eval x (∏ i, p i) ≠ 0 at hx
    rw [map_prod, Finset.prod_ne_zero_iff] at hx
    funext i
    apply propext
    exact ⟨fun hi => by_contra fun h => hx i (Finset.mem_univ i) (hz i h x hi), fun h => h ▸ mem_univ x⟩
  let c := test (fun i => Z i = univ)
  trans c
  · rw [← generic_constant (K := K) (α := ι) c]
    apply generic_congr_on (U := principalOpen q)
      ((generic_iff _).mpr ⟨q, hq, subset_rfl⟩)
    intro x hx
    change test (fun i => x ∈ Z i) ↔ c
    rw [value x hx]
  · symm
    rw [← generic_constant (K := K) (α := κ) c]
    apply generic_congr_on (U := principalOpen (eval₂ C G q))
      ((generic_iff _).mpr ⟨_, hGq, subset_rfl⟩)
    intro t ht
    change eval t (eval₂ C G q) ≠ 0 at ht
    rw [eval_eval₂] at ht
    have : (eval t).comp C = RingHom.id K := by ext; simp
    rw [this, eval₂_id] at ht
    change test (fun i => (fun k => eval t (G k)) ∈ Z i) ↔ c
    rw [value _ ht]

end Generator

end BorderVNP
end Computability
end OAI
