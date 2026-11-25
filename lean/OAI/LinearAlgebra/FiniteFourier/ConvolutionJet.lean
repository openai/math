import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetQuadratic
import OAI.LinearAlgebra.FiniteFourier.JetReduction.ConvolutionJetReduction
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

/-! # Packed multiplication of truncated cyclotomic jets

A jet over a monogenic coefficient algebra has a rectangular array of
coefficients. Padded Kronecker substitution recovers each raw product row
from an ordinary polynomial product. This works over arbitrary commutative
coefficient rings, in particular the quadratic orders in integral descent.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial
open scoped BigOperators Classical

noncomputable section
variable {S : Type*} [CommRing S] {e h : ℕ}

/-- Rectangular coefficients in the powers of the jet variable and of the
coefficient algebra generator, respectively. -/
abbrev JetArray (S : Type*) (e h : ℕ) := Fin h × Fin e → S

/-- Bivariate polynomial lift before either monic relation has been imposed. -/
def jetBivariate (a : JetArray S e h) : Polynomial S[X] :=
  ∑ i : Fin h × Fin e, monomial i.1.val (monomial i.2.val (a i))

/-- Substitute the same univariate indeterminate for the coefficient variable,
and its `(2e-1)`-st power for the jet variable. -/
def jetPack (a : JetArray S e h) : S[X] :=
  ∑ i : Fin h × Fin e, monomial (i.1.val * (2*e-1) + i.2.val) (a i)

/-- Both operands of the product fit in length `2eh`. -/
theorem jetPack_natDegree_lt (he : 0 < e) (hh : 0 < h) (a : JetArray S e h) :
    (jetPack a).natDegree < 2*e*h := by
  have hn : 0 < 2*e*h := by positivity
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := 2*e*h-1) ?_) (by omega)
  intro i _
  apply (natDegree_monomial_le _).trans
  have hi := i.1.isLt
  have hj := i.2.isLt
  have hmul := Nat.mul_le_mul_right (2*e) (show i.1.val+1 ≤ h by omega)
  have hsmall := Nat.mul_le_mul_left i.1.val (Nat.sub_le (2*e) 1)
  rw [Nat.add_mul, one_mul, mul_comm h] at hmul
  omega

private theorem jetDigitSum_eq {i j : Fin h × Fin e} {t k : ℕ} (hk : k < 2*e-1) :
    (i.1.val*(2*e-1)+i.2.val + (j.1.val*(2*e-1)+j.2.val) = t*(2*e-1)+k) ↔
      i.1.val+j.1.val = t ∧ i.2.val+j.2.val = k := by
  let s := 2*e-1
  have hc : i.2.val + j.2.val < s := by dsimp [s]; have := i.2.isLt; have := j.2.isLt; omega
  change k < s at hk
  have hs : 0 < s := Nat.zero_lt_of_lt hc
  change (_*s+_+(_*s+_) = _*s+_) ↔ _
  rw [show i.1.val*s+i.2.val+(j.1.val*s+j.2.val) =
        (i.1.val+j.1.val)*s + (i.2.val+j.2.val) by ring]
  constructor
  · intro heq
    have hmod := congrArg (· % s) heq
    simp [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hk] at hmod
    rw [hmod] at heq
    exact ⟨Nat.eq_of_mul_eq_mul_right hs (Nat.add_right_cancel heq), hmod⟩
  · rintro ⟨hr, hd⟩
    rw [hr, hd]

private theorem jetBivariate_product_coeff (a b : JetArray S e h) (t k : ℕ) :
    (((jetBivariate a * jetBivariate b).coeff t).coeff k) =
      ∑ i : Fin h × Fin e, ∑ j : Fin h × Fin e,
        if i.1.val+j.1.val=t ∧ i.2.val+j.2.val=k then a i * b j else 0 := by
  simp only [jetBivariate, Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial,
    finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp_all [coeff_monomial]

/-- No carry can cross a row in the ordinary packed product. -/
theorem jetPack_product_coeff (a b : JetArray S e h) (t : ℕ) {k : ℕ} (hk : k < 2*e-1) :
    (jetPack a * jetPack b).coeff (t*(2*e-1)+k) =
      ((jetBivariate a * jetBivariate b).coeff t).coeff k := by
  rw [jetBivariate_product_coeff]
  simp only [jetPack, Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial,
    finsetSum_coeff, coeff_monomial, jetDigitSum_eq hk]
  rw [Finset.sum_comm]

/-- Read a product row in the coefficient variable. -/
def unpackJetRow (e : ℕ) (p : S[X]) (t : ℕ) : S[X] :=
  ofFn (2*e-1) (fun k => p.coeff (t*(2*e-1)+k.val))

theorem unpackJetRow_mul (a b : JetArray S e h) (t : ℕ) :
    unpackJetRow e (jetPack a * jetPack b) t = (jetBivariate a * jetBivariate b).coeff t := by
  ext k
  by_cases hk : k < 2*e-1
  · rw [unpackJetRow, ofFn_coeff_eq_val_of_lt _ hk, jetPack_product_coeff a b t hk]
  · rw [unpackJetRow, ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk), jetBivariate_product_coeff]
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have := i.2.isLt
    have := j.2.isLt
    apply ite_eq_right
    omega

/-- The iterated quotient `(S[Y]/(m))[z]/(z^h)`. -/
abbrev JetQuotient (m : S[X]) (h : ℕ) := AdjoinRoot ((X : (AdjoinRoot m)[X]) ^ h)

/-- Interpret the input array in the iterated quotient. -/
def jetQuotientValue (m : S[X]) (a : JetArray S e h) : JetQuotient m h :=
  AdjoinRoot.mk (X ^ h) ((jetBivariate a).map (AdjoinRoot.mk m))

/-- Keep the first `h` rows and reduce each by the coefficient modulus. -/
def jetProductRows (e h : ℕ) (m p : S[X]) : Polynomial S[X] :=
  ofFn h fun t => (unpackJetRow e p t.val) %ₘ m

/-- Truncation and rowwise monic reduction of the packed product compute
multiplication in the actual jet ring. -/
theorem jetProductRows_correct (m : S[X]) (hm : m.Monic) (a b : JetArray S e h) :
    AdjoinRoot.mk (X ^ h)
      ((jetProductRows e h m (jetPack a * jetPack b)).map (AdjoinRoot.mk m)) =
      jetQuotientValue m a * jetQuotientValue m b := by
  unfold jetQuotientValue
  rw [← map_mul, ← Polynomial.map_mul, AdjoinRoot.mk_eq_mk, X_pow_dvd_iff]
  intro t ht
  rw [coeff_sub, coeff_map, coeff_map, jetProductRows, ofFn_coeff_eq_val_of_lt _ ht,
    unpackJetRow_mul]
  apply sub_eq_zero.mpr
  simpa only [AdjoinRoot.modByMonicHom_mk] using
    (AdjoinRoot.mk_leftInverse hm (AdjoinRoot.mk m ((jetBivariate a * jetBivariate b).coeff t)))

variable {R : Type*} [CommRing R]

/-- Decode the two base-ring entries of each cell in the quadratic power basis. -/
def quadraticJetArray (φ : R →+* S) (η : S) (u v : JetArray R e h) : JetArray S e h :=
  fun i => φ (u i) + η * φ (v i)

theorem jetPack_quadraticJetArray (φ : R →+* S) (η : S) (u v : JetArray R e h) :
    jetPack (quadraticJetArray φ η u v) =
      quadraticPolynomial φ η (jetPack u) (jetPack v) := by
  simp only [jetPack, quadraticJetArray, quadraticPolynomial, Polynomial.map_sum,
    map_monomial, Finset.mul_sum, C_mul_monomial, ← Finset.sum_add_distrib, ← map_add]

/-- Common input to child `j` at length `2eh`, as a vector over the base ring. -/
def jetChildInput (a₀ a₁ : JetArray R e h) (j : Fin 3) : Fin (2*e*h) → R :=
  fun i => quadraticRow ((jetPack a₀).coeff i) ((jetPack a₁).coeff i) j

/-- Decode the three untruncated base-ring convolutions as a single packed
polynomial over the quadratic order. -/
def jetChildProduct (φ : R →+* S) (η : S) (c d : R) (a₀ a₁ b₀ b₁ : JetArray R e h) : S[X] :=
  ofFn (2*(2*e*h)-1) fun k =>
    let q := quadraticDecode c d (fun j =>
      openConv R (2*e*h) (jetChildInput a₀ a₁ j) (jetChildInput b₀ b₁ j) k)
    φ q.1 + η * φ q.2

theorem jetChildProduct_eq (φ : R →+* S) (η : S) (c d : R)
    (hη : η^2 = φ c + η * φ d) (he : 0 < e) (hh : 0 < h) (a₀ a₁ b₀ b₁ : JetArray R e h) :
    jetChildProduct φ η c d a₀ a₁ b₀ b₁ =
      jetPack (quadraticJetArray φ η a₀ a₁) * jetPack (quadraticJetArray φ η b₀ b₁) := by
  let n := 2*e*h
  have hn : ∀ a : JetArray R e h, ofFn n (fun i => (jetPack a).coeff i.val) = jetPack a :=
    fun a => ofFn_comp_toFn_eq_id_of_natDegree_lt (jetPack_natDegree_lt he hh a)
  ext k
  by_cases hk : k < 2*n-1
  · rw [jetChildProduct, ofFn_coeff_eq_val_of_lt _ hk, jetPack_quadraticJetArray,
      jetPack_quadraticJetArray]
    dsimp only [jetChildInput]
    have H := quadratic_openConv_coeff φ η c d hη
      (fun i : Fin n => (jetPack a₀).coeff i.val) (fun i => (jetPack a₁).coeff i.val)
      (fun i => (jetPack b₀).coeff i.val) (fun i => (jetPack b₁).coeff i.val) ⟨k, hk⟩
    dsimp only at H
    rw [hn, hn, hn, hn] at H
    exact H
  · rw [jetChildProduct, ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    have ha := jetPack_natDegree_lt he hh (quadraticJetArray φ η a₀ a₁)
    have hb := jetPack_natDegree_lt he hh (quadraticJetArray φ η b₀ b₁)
    apply natDegree_mul_le.trans_lt
    dsimp [n] at hk
    omega

/-- An entire jet product, including the two fixed-factor products in each
retained row for reciprocal reduction. -/
def jetConvolutionRows (e h : ℕ) (m p : S[X]) : Polynomial S[X] :=
  ofFn h fun t => JetReduction.reduce e m (unpackJetRow e p t.val)

/-- Three ordinary base-ring products with common encoders, followed by row
truncation and fixed-factor multiplication, realize multiplication in
`(S[Y]/(m))[z]/(z^h)` under any monic quadratic relation for the base generator. -/
theorem jetConvolution_correct (φ : R →+* S) (η : S) (c d : R)
    (hη : η^2 = φ c + η * φ d) (he : 0 < e) (hh : 0 < h)
    (m : S[X]) (hm : m.Monic) (hd : m.natDegree = e) (a₀ a₁ b₀ b₁ : JetArray R e h) :
    AdjoinRoot.mk (X ^ h) ((jetConvolutionRows e h m
      (jetChildProduct φ η c d a₀ a₁ b₀ b₁)).map (AdjoinRoot.mk m)) =
      jetQuotientValue m (quadraticJetArray φ η a₀ a₁) *
      jetQuotientValue m (quadraticJetArray φ η b₀ b₁) := by
  rw [jetChildProduct_eq φ η c d hη he hh, ← jetProductRows_correct m hm]
  congr 2
  unfold jetConvolutionRows jetProductRows
  congr 1
  funext t
  apply JetReduction.reduce_eq_modByMonic he hm hd
  exact (ofFn_natDegree_lt (show 1 ≤ 2*e-1 by omega) _).trans (by omega)

end

end FiniteFourier
end LinearAlgebra
end OAI
