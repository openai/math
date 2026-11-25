import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Prime-power roots and repair nodes over the coefficient ring

Starting with a primitive prime-th root, adjoining a prime-power root of it
is a monic extension with an explicit power basis. The powers of the new
root stay distinct in every residue field. Their differences are therefore
units, as required for the Vandermonde repair of arbitrary erasure patterns.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime]

/-- The one-level root adjunction over the base coefficients. -/
abbrev PrimeCyclotomicExtension (ζ : R) (p a : ℕ) :=
  AdjoinRoot (X ^ (p ^ a) - C ζ)

/-- The generator whose `p^a`-th power is the specified base root. -/
noncomputable abbrev primeCyclotomicRoot (ζ : R) (p a : ℕ) : PrimeCyclotomicExtension ζ p a :=
  AdjoinRoot.root _

omit [Fact p.Prime] in
theorem primeCyclotomicRoot_pow (ζ : R) (a : ℕ) :
    primeCyclotomicRoot ζ p a ^ (p ^ a) = algebraMap R _ ζ := by
  rw [AdjoinRoot.algebraMap_eq, ← sub_eq_zero, ← AdjoinRoot.eval₂_root,
    eval₂_sub, eval₂_C, eval₂_pow, eval₂_X]

/-- A basis of exactly `p^a` coefficient components for restriction of scalars. -/
noncomputable def primeCyclotomicBasis [Nontrivial R] (ζ : R) (a : ℕ) :
    Module.Basis (Fin (p ^ a)) R (PrimeCyclotomicExtension ζ p a) :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C ζ (pow_ne_zero a (Fact.out : p.Prime).ne_zero))).basis.reindex
    (finCongr (natDegree_X_pow_sub_C (R := R)))

/-- The cyclotomic relation and invertibility of the prime give the exact order
after any specialization to a nontrivial ring. -/
theorem primeCyclotomicRoot_map_primitive {ζ : R} (a : ℕ)
    (hp : IsUnit (p : R)) (hpow : ζ ^ p = 1)
    (hsum : ∑ i ∈ Finset.range p, ζ ^ i = 0)
    {S : Type*} [CommRing S] [Nontrivial S] (φ : PrimeCyclotomicExtension ζ p a →+* S) :
    IsPrimitiveRoot (φ (primeCyclotomicRoot ζ p a)) (p ^ (a + 1)) := by
  let ψ := φ.comp (algebraMap R (PrimeCyclotomicExtension ζ p a))
  have he : φ (primeCyclotomicRoot ζ p a) ^ (p ^ a) = ψ ζ := by
    rw [← map_pow, primeCyclotomicRoot_pow]
    rfl
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_prime_pow
  · rw [he]
    intro hz
    have hx := congrArg ψ hsum
    simp only [map_sum, map_pow, hz, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, map_zero] at hx
    exact (by simpa using (hp.map ψ).ne_zero : (p : S) ≠ 0) hx
  · rw [pow_succ, pow_mul, he, ← map_pow, hpow, map_one]

/-- The consecutive powers of the new root give pairwise unit differences,
including over base rings with nontrivial residue characteristics. -/
theorem primeCyclotomicNodes_pairwise_of_sum {ζ : R} (a : ℕ)
    (hp : IsUnit (p : R)) (hpow : ζ ^ p = 1)
    (hsum : ∑ i ∈ Finset.range p, ζ ^ i = 0) {W : ℕ} (hW : W ≤ p ^ (a + 1)) :
    Pairwise (fun i j : Fin W => IsUnit
      (primeCyclotomicRoot ζ p a ^ i.val - primeCyclotomicRoot ζ p a ^ j.val)) := by
  classical
  intro i j hij
  by_contra h
  obtain ⟨I, hI, hm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr h)
  let : I.IsMaximal := hI
  let φ := Ideal.Quotient.mk I
  have hm' := Ideal.Quotient.eq_zero_iff_mem.mpr hm
  have eq : φ (primeCyclotomicRoot ζ p a) ^ i.val = φ (primeCyclotomicRoot ζ p a) ^ j.val := by
    simpa only [map_sub, map_pow, sub_eq_zero] using hm'
  exact hij (Fin.ext ((primeCyclotomicRoot_map_primitive a hp hpow hsum φ).pow_inj
    (i.isLt.trans_le hW) (j.isLt.trans_le hW) eq))

/-- In a domain the cyclotomic relation follows from primitivity. -/
theorem primeCyclotomicNodes_pairwise [IsDomain R] {ζ : R} (a : ℕ)
    (hp : IsUnit (p : R)) (hζ : IsPrimitiveRoot ζ p) {W : ℕ} (hW : W ≤ p ^ (a + 1)) :
    Pairwise (fun i j : Fin W => IsUnit
      (primeCyclotomicRoot ζ p a ^ i.val - primeCyclotomicRoot ζ p a ^ j.val)) :=
  primeCyclotomicNodes_pairwise_of_sum a hp hζ.pow_eq_one
    (hζ.geom_sum_eq_zero (Fact.out : p.Prime).one_lt) hW

theorem primeCyclotomicExtension_nontrivial [Nontrivial R] (ζ : R) (a : ℕ) :
    Nontrivial (PrimeCyclotomicExtension ζ p a) := by
  have hpos := pow_pos (Fact.out : p.Prime).pos a
  apply (AdjoinRoot.nontrivial_iff_of_monic (monic_X_pow_sub_C ζ hpos.ne')).mpr
  exact natDegree_pos_iff_degree_pos.mp (by rwa [natDegree_X_pow_sub_C])

/-- Raising the extension generator to the complementary prime power gives the
smaller clock root, with unit differences from one in all interior powers. -/
theorem primeCyclotomicRoot_power_data [Nontrivial R] {ζ : R} (a k : ℕ)
    (hk : k ≤ a + 1) (hp : IsUnit (p : R)) (hpow : ζ ^ p = 1)
    (hsum : ∑ i ∈ Finset.range p, ζ ^ i = 0) :
    let ξ := primeCyclotomicRoot ζ p a ^ p ^ (a + 1 - k)
    IsPrimitiveRoot ξ (p ^ k) ∧ ∀ i, 0 < i → i < p ^ k → IsUnit (ξ ^ i - 1) := by
  let : Nontrivial (PrimeCyclotomicExtension ζ p a) := primeCyclotomicExtension_nontrivial ζ a
  have hη := primeCyclotomicRoot_map_primitive a hp hpow hsum (RingHom.id _)
  let e := p ^ (a + 1 - k)
  have he : 0 < e := pow_pos (Fact.out : p.Prime).pos _
  have htotal : p ^ (a + 1) = e * p ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  refine ⟨hη.pow (pow_pos (Fact.out : p.Prime).pos _) htotal, ?_⟩
  intro i hi hlt
  have hindex : e * i < p ^ (a + 1) := by rw [htotal]; exact Nat.mul_lt_mul_of_pos_left hlt he
  have hz : 0 < p ^ (a + 1) := pow_pos (Fact.out : p.Prime).pos _
  have hne : (⟨e*i, hindex⟩ : Fin (p ^ (a + 1))) ≠ ⟨0, hz⟩ := by
    intro hh
    exact (Nat.mul_pos he hi).ne' (congrArg Fin.val hh)
  simpa only [← pow_mul, pow_zero] using
    (primeCyclotomicNodes_pairwise_of_sum a hp hpow hsum le_rfl hne)

/-- The finite check nodes and the root for a power-of-`p` matrix
pencil can be chosen in the same finite free algebra. The basis size is
fixed by the step parameters and does not depend on the transform length. -/
theorem exists_primeCyclotomicRepairExtension [Nontrivial R] {ζ : R} (hp : IsUnit (p : R))
    (hpow : ζ ^ p = 1) (hsum : ∑ i ∈ Finset.range p, ζ ^ i = 0) (k W : ℕ) :
    ∃ a : ℕ, ∃ (ξ : PrimeCyclotomicExtension ζ p a)
      (ρ : Fin W → PrimeCyclotomicExtension ζ p a),
      IsPrimitiveRoot ξ (p ^ k) ∧
      (∀ i, 0 < i → i < p ^ k → IsUnit (ξ ^ i - 1)) ∧
      Pairwise (fun i j => IsUnit (ρ i - ρ j)) := by
  let a := max k W
  have hk : k ≤ a + 1 := (le_max_left k W).trans (Nat.le_succ a)
  have hW : W ≤ p ^ (a + 1) :=
    (le_max_right k W).trans ((Nat.le_succ a).trans
      (Nat.lt_pow_self (n := a+1) (Fact.out : p.Prime).one_lt).le)
  obtain ⟨hr, hu⟩ := primeCyclotomicRoot_power_data a k hk hp hpow hsum
  exact ⟨a, _, _, hr, hu, primeCyclotomicNodes_pairwise_of_sum a hp hpow hsum hW⟩

end FiniteFourier
end LinearAlgebra
end OAI
