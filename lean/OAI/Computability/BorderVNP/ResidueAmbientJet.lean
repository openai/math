import OAI.Computability.BorderVNP.ResidueAmbientCartier
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.MonoidAlgebra.Lift

/-!
# Top coefficients of truncated parameter jets

A linear functional reading the top monomial in a box of truncated variables also
reads the same coefficient after translation of polynomials of degree less than
the truncation order in each coordinate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open scoped BigOperators
open ResidueBox

variable {ι σ K B A : Type*}

/-- Translation by constants preserves the coefficient of the top box monomial on reduced
representatives. The hypothesis describes the values of the coefficient functional on the
monomial basis. -/
theorem jet_top_translate [Fintype ι] [CommRing B] [CommRing A] [Algebra B A]
    (n : ℕ) (top : A →ₗ[B] B) (v : ι → B) (ε : ι → A)
    (hbasis : ∀ b : ι → ℕ, (∀ i, b i ≤ n) →
      top (∏ i, ε i ^ b i) = if b = (fun _ => n) then 1 else 0)
    (r : ι → ℕ) (hr : ∀ i, r i ≤ n) :
    top (∏ i, (algebraMap B A (v i) + ε i) ^ r i) = if r = (fun _ => n) then 1 else 0 := by
  classical
  let s := Fintype.piFinset fun i => Finset.range (r i + 1)
  let c (b : ι → ℕ) := ∏ i, (v i ^ (r i - b i)) * (r i).choose (b i)
  have expand : (∏ i, (algebraMap B A (v i) + ε i) ^ r i) =
      ∑ b ∈ s, algebraMap B A (c b) * ∏ i, ε i ^ b i := by
    simp only [add_comm (algebraMap B A _), add_pow, Finset.prod_univ_sum, s]
    apply Finset.sum_congr rfl
    intro b _
    dsimp [c]
    rw [map_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_mul, map_natCast, map_pow]
    ring
  rw [expand, map_sum]
  have term (b : ι → ℕ) (hb : b ∈ s) :
      top (algebraMap B A (c b) * ∏ i, ε i ^ b i) =
        c b * (if b = (fun _ => n) then 1 else 0) := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul, hbasis]
    intro i
    have := Finset.mem_range.mp (Fintype.mem_piFinset.mp hb i)
    exact Nat.le_trans (by omega) (hr i)
  by_cases h : r = (fun _ => n)
  · subst r
    rw [ite_eq_left rfl, Finset.sum_eq_single_of_mem (fun _ : ι => n)
      (Fintype.mem_piFinset.mpr (fun _ => Finset.mem_range.mpr (Nat.lt_succ_self _)))]
    · rw [term _ (Fintype.mem_piFinset.mpr (fun _ => Finset.mem_range.mpr (Nat.lt_succ_self _)))]
      simp [c]
    · intro b hb hn
      simp [term b hb, hn]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ (fun _ => n) := by
      intro he
      apply h
      funext i
      have hi := Finset.mem_range.mp (Fintype.mem_piFinset.mp hb i)
      rw [congrFun he i] at hi
      exact le_antisymm (hr i) (by omega)
    simp [term b hb, hbn]

/-- The chart algebra polynomial in the parameter variables and Laurent in the base parameter. -/
abbrev Mixed (σ K : Type*) [CommSemiring K] := AddMonoidAlgebra K ((σ → ℕ) × ℤ)

/-- The exponent embedding distinguishes the invertible parameter from the polynomial variables. -/
def mixedIndex : ((σ → ℕ) × ℤ) →+ Exponent σ where
  toFun e := fun i => i.elim e.2 (fun k => (e.1 k : ℤ))
  map_zero' := by funext i; cases i <;> simp
  map_add' x y := by funext i; cases i <;> simp

/-- Embedding of the mixed chart algebra in the full algebra of signed exponent vectors. -/
noncomputable def mixedToLaurent [CommSemiring K] : Mixed σ K →+* Laurent σ K :=
  AddMonoidAlgebra.mapDomainRingHom K mixedIndex

/-- Distinct mixed Laurent polynomials remain distinct in the full Laurent algebra. -/
theorem mixedToLaurent_injective [CommSemiring K] :
    Function.Injective (mixedToLaurent (K := K) (σ := σ)) := by
  apply AddMonoidAlgebra.mapDomain_injective
  intro x y h
  apply Prod.ext
  · funext i
    exact Int.ofNat_inj.mp (congrFun h (some i))
  · exact congrFun h none

/-- The embedding preserves individual chart monomials and coefficients. -/
theorem mixedToLaurent_single [CommSemiring K] (e : (σ → ℕ) × ℤ) (c : K) :
    mixedToLaurent (AddMonoidAlgebra.single e c) = AddMonoidAlgebra.single (mixedIndex e) c :=
  AddMonoidAlgebra.mapDomain_single

/-- The value of a monomial, with integer powers at the unit parameter. -/
def mixedMonomial [Fintype σ] [CommRing B] (v : σ → B) (t : Bˣ) :
    Multiplicative ((σ → ℕ) × ℤ) →* B where
  toFun e := (↑(t ^ e.toAdd.2) : B) * ∏ i, v i ^ e.toAdd.1 i
  map_one' := by simp
  map_mul' e d := by
    change (↑(t ^ (e.toAdd.2 + d.toAdd.2)) : B) * ∏ i, v i ^ (e.toAdd.1 i + d.toAdd.1 i) = _
    simp only [zpow_add, Units.val_mul, pow_add, Finset.prod_mul_distrib]
    ring

/-- Evaluation on the affine chart, permitting the polynomial variables to vanish. -/
noncomputable def mixedEval [Fintype σ] [CommRing K] [CommRing B]
    (φ : K →+* B) (v : σ → B) (t : Bˣ) : Mixed σ K →+* B :=
  AddMonoidAlgebra.liftNCRingHom φ (mixedMonomial v t) (fun _ _ => Commute.all _ _)

/-- Formula for evaluation on a single chart monomial. -/
theorem mixedEval_single [Fintype σ] [CommRing K] [CommRing B] (φ : K →+* B)
    (v : σ → B) (t : Bˣ) (e : (σ → ℕ) × ℤ) (c : K) :
    mixedEval φ v t (AddMonoidAlgebra.single e c) = φ c * ((↑(t ^ e.2) : B) * ∏ i, v i ^ e.1 i) :=
  AddMonoidAlgebra.liftNCRingHom_single ..

/-- Evaluation commutes with a homomorphism of the target rings, including on negative
powers of the base parameter. -/
theorem mixedEval_map [Fintype σ] [CommRing K] [CommRing B] [CommRing A]
    (φ : K →+* B) (ψ : B →+* A) (v : σ → B) (t : Bˣ) (f : Mixed σ K) :
    ψ (mixedEval φ v t f) =
      mixedEval (ψ.comp φ) (fun i => ψ (v i)) (Units.map ψ.toMonoidHom t) f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single e c =>
    rw [mixedEval_single, mixedEval_single, map_mul, map_mul, map_prod]
    simp only [map_pow, RingHom.comp_apply]
    have ht := congrArg Units.val (map_zpow (Units.map ψ.toMonoidHom) t e.2)
    rw [← ht]
    rfl

private theorem mixedEval_jet_pow [Fintype σ] [Field K] [CommRing B] [CommRing A] [Algebra B A]
    (p u : ℕ) [ExpChar A p] (φ : K →+* B) (v : σ → B) (t : Bˣ) (τ : Aˣ)
    (ε : Option σ → A) (hτ : (τ : A) = algebraMap B A (t : B) + ε none)
    (hε : ∀ i, ε i ^ p ^ u = 0) (f : Mixed σ K) :
    (mixedEval ((algebraMap B A).comp φ) (fun i => algebraMap B A (v i) + ε (some i)) τ f) ^ p ^ u =
      algebraMap B A ((mixedEval φ v t f) ^ p ^ u) := by
  let T := iterateFrobenius A p u
  rw [map_pow (algebraMap B A)]
  change T (mixedEval _ _ _ _) = T (algebraMap B A (mixedEval φ v t f))
  rw [mixedEval_map, mixedEval_map φ (algebraMap B A), mixedEval_map]
  congr 2
  · funext i
    change (algebraMap B A (v i) + ε (some i)) ^ p ^ u = (algebraMap B A (v i)) ^ p ^ u
    rw [add_pow_expChar_pow, hε, add_zero]
  · apply Units.ext
    change (τ : A) ^ p ^ u = (algebraMap B A (t : B)) ^ p ^ u
    rw [hτ, add_pow_expChar_pow, hε, add_zero]

/-- The ambient top coefficient after jet evaluation is the Frobenius power of the
point evaluation of `Λ_q f`. The ordinary chart coordinates may vanish, and the base
parameter may have negative exponents. The nilpotents and the functional can belong
to any truncated algebra satisfying the monomial basis identities. -/
theorem ambient_top_jet [Fintype σ] [Field K] [CommRing B] [CommRing A] [Algebra B A]
    (p u : ℕ) [ExpChar K p] [PerfectRing K p] [ExpChar B p] [ExpChar A p]
    (φ : K →+* B) (v : σ → B) (t : Bˣ) (τ : Aˣ) (ε : Option σ → A)
    (hτ : (τ : A) = algebraMap B A (t : B) + ε none) (hε : ∀ i, ε i ^ p ^ u = 0)
    (top : A →ₗ[B] B) (hbasis : ∀ b : Option σ → ℕ, (∀ i, b i ≤ p ^ u - 1) →
      top (∏ i, ε i ^ b i) = if b = (fun _ => p ^ u - 1) then 1 else 0) (f : Mixed σ K) :
    ∃ g : Mixed σ K, mixedToLaurent g = ambientCartier p u (mixedToLaurent f) ∧
      top (mixedEval ((algebraMap B A).comp φ) (fun i => algebraMap B A (v i) + ε (some i)) τ f) =
        (mixedEval φ v t g) ^ p ^ u := by
  classical
  let q := p ^ u
  have hq : 0 < q := expChar_pow_pos K p u
  let jet := mixedEval ((algebraMap B A).comp φ) (fun i => algebraMap B A (v i) + ε (some i)) τ
  let point := mixedEval φ v t
  change ∃ g : Mixed σ K, _ ∧ top (jet f) = (point g) ^ q
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp [ambientCartier_zero], by simp [zero_pow hq.ne']⟩
  | add f h hf hh =>
    obtain ⟨g, hg, ht⟩ := hf
    obtain ⟨k, hk, hu⟩ := hh
    exact ⟨g + k, by rw [map_add, map_add, ambientCartier_add, hg, hk],
      by rw [map_add, map_add, ht, hu, map_add, add_pow_expChar_pow (p := p)]⟩
  | single e c =>
    let d : (σ → ℕ) × ℤ := (fun i => e.1 i / q, e.2 / q)
    let r : Option σ → ℕ := fun i => i.elim (e.2 % q).toNat (fun k => e.1 k % q)
    let m : (σ → ℕ) × ℤ := (fun i => r (some i), r none)
    let D : Mixed σ K := AddMonoidAlgebra.single d ((iterateFrobeniusEquiv K p u).symm c)
    let M : Mixed σ K := AddMonoidAlgebra.single m 1
    have hq' : 0 < (q : ℤ) := by exact_mod_cast hq
    have hrt : (r none : ℤ) = e.2 % q := Int.toNat_of_nonneg (Int.emod_nonneg _ hq'.ne')
    have hr (i : Option σ) : r i < q := by
      cases i with
      | none =>
        exact_mod_cast hrt.trans_lt (Int.emod_lt_of_pos _ hq')
      | some k => exact Nat.mod_lt _ hq
    have hfact : D ^ q * M = AddMonoidAlgebra.single e c := by
      rw [show D = AddMonoidAlgebra.single d _ by rfl, AddMonoidAlgebra.single_pow,
        show M = AddMonoidAlgebra.single m _ by rfl, AddMonoidAlgebra.single_mul_single, mul_one]
      congr 1
      · apply Prod.ext
        · funext i
          change q • (e.1 i / q) + e.1 i % q = e.1 i
          rw [nsmul_eq_mul, add_comm]
          exact Nat.mod_add_div (e.1 i) q
        · change q • (e.2 / (q : ℤ)) + (r none : ℤ) = e.2
          rw [nsmul_eq_mul, hrt, Int.mul_ediv_add_emod]
      · exact (iterateFrobeniusEquiv K p u).apply_symm_apply _
    have hindex : mixedIndex m = fun i => (r i : ℤ) := by funext i; cases i <;> rfl
    have hM : ambientCartier p u (mixedToLaurent M) =
        if r = (fun _ => q - 1) then 1 else 0 := by
      change ambientCartier p u (mixedToLaurent (AddMonoidAlgebra.single m 1)) = _
      rw [mixedToLaurent_single, hindex]
      rw [ambientCartier_reduced_single p u r hr]
      dsimp only [q]
      split_ifs <;> rfl
    have htop : top (jet M) = if r = (fun _ => q - 1) then 1 else 0 := by
      have heval : jet M =
          ∏ i : Option σ, (algebraMap B A (i.elim (t : B) v) + ε i) ^ r i := by
        rw [Fintype.prod_option, show jet M = _ from mixedEval_single _ _ _ m (1 : K)]
        simp only [map_one, one_mul]
        change (↑(τ ^ (r none : ℤ)) : A) * _ = (algebraMap B A (t : B) + ε none) ^ r none * _
        rw [zpow_natCast, Units.val_pow_eq_pow_val, hτ]
        rfl
      rw [heval, jet_top_translate _ top _ ε hbasis r (fun i => Nat.le_sub_one_of_lt (hr i))]
    rw [← hfact, map_mul, map_pow, ambientCartier_pow_mul, hM, map_mul, map_pow,
      mixedEval_jet_pow p u φ v t τ ε hτ hε D, ← Algebra.smul_def, map_smul, htop, smul_eq_mul]
    by_cases h : r = (fun _ => q - 1)
    · exact ⟨D, by simp [h], by simp [h, point, q]⟩
    · exact ⟨0, by simp [h], by simp [h, zero_pow hq.ne']⟩

end Residue

end BorderVNP
end Computability
end OAI
