import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

/-!
# Finite support of the Cartier tests

Section 10.2 of *An explicit VNP family requires superpolynomial border circuit size over every
field* uses the exponent box with nonnegative polynomial coordinates and one signed Laurent
coordinate. This file proves the support assertion for the actual product in (10.3) and for
the compression of an arbitrary test in the proof that the residue vector is nonzero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueBox

open scoped BigOperators Pointwise

variable {σ ι E : Type*} [CommSemiring E]

/-- Laurent exponent vectors, with `none` denoting the coordinate of `t`. -/
abbrev Exponent (σ : Type*) := Option σ → ℤ

/-- Finite Laurent polynomials in the coordinates of the curve chart. -/
abbrev Laurent (σ E : Type*) [CommSemiring E] := AddMonoidAlgebra E (Exponent σ)

/-- The support box of §10.2, with signed exponents allowed only in the last variable. -/
def InBox (H : ℕ) (e : Exponent σ) : Prop :=
  (- (H : ℤ) ≤ e none ∧ e none ≤ H) ∧ ∀ i, 0 ≤ e (some i) ∧ e (some i) ≤ H

/-- The radius of the box of tests, for degree bound `L` and sum of equation degrees `S`. -/
def radius (L S : ℕ) : ℕ := 4 * (L + S + 2)

/-- Including the exponent vectors of ordinary polynomials among signed vectors. -/
def polynomialExponents (ι : Type*) : (ι →₀ ℕ) →+ (ι → ℤ) where
  toFun e i := e i
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp

/-- The polynomial chart equations embedded in the Laurent algebra. -/
noncomputable def toLaurent : MvPolynomial (Option σ) E →+* Laurent σ E :=
  AddMonoidAlgebra.mapDomainRingHom E (polynomialExponents _)

/-- Each coordinate of an embedded polynomial monomial is between zero and the total degree. -/
theorem polynomial_coordinate_bounds (g : MvPolynomial (Option σ) E)
    {e : Exponent σ} (he : e ∈ (toLaurent g).coeff.support) (i : Option σ) :
    0 ≤ e i ∧ e i ≤ g.totalDegree := by
  classical
  change e ∈ (g.coeff.mapDomain (polynomialExponents _)).support at he
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support he)
  change 0 ≤ (m i : ℤ) ∧ (m i : ℤ) ≤ g.totalDegree
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast
    (MvPolynomial.le_degreeOf_of_mem_support i hm).trans (g.degreeOf_le_totalDegree i)⟩

/-- The polynomial factor multiplying each test before Cartier extraction. -/
noncomputable def equationProduct [Fintype ι] (q : ℕ)
    (g : ι → MvPolynomial (Option σ) E) : Laurent σ E :=
  toLaurent (∏ i, g i ^ (q - 1))

/-- The interval of possible shifts of a test exponent, including possible cancellations. -/
theorem equationProduct_coordinate_bounds [Fintype ι] (q : ℕ)
    (g : ι → MvPolynomial (Option σ) E) {e : Exponent σ}
    (he : e ∈ (equationProduct q g).coeff.support) (i : Option σ) :
    0 ≤ e i ∧ e i ≤ ((q - 1) * ∑ j, (g j).totalDegree : ℕ) := by
  obtain ⟨hl, hu⟩ := polynomial_coordinate_bounds _ he i
  refine ⟨hl, hu.trans ?_⟩
  exact_mod_cast calc
    (∏ j, g j ^ (q - 1)).totalDegree ≤ ∑ j, (g j ^ (q - 1)).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ j, (q - 1) * (g j).totalDegree := Finset.sum_le_sum fun j _ =>
      MvPolynomial.totalDegree_pow _ _
    _ = _ := (Finset.mul_sum ..).symm

/-- The exponent inspected to compute the coefficient at `d` in the Cartier extraction. -/
def sourceIndex (q : ℕ) (d : Exponent σ) : Exponent σ :=
  fun i => q * d i + (q : ℤ) - 1

private theorem sourceIndex_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (sourceIndex (σ := σ) q) := by
  intro x y h
  funext i
  have hi := congrFun h i
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  apply mul_left_cancel₀ hq'
  change (q : ℤ) * x i + q - 1 = (q : ℤ) * y i + q - 1 at hi
  omega

/-- The coefficient operator of (10.2). The coefficient map is inverse Frobenius,
or the identity when `q` is a power of the coefficient field's cardinality. -/
noncomputable def extract (q : ℕ) (hq : 0 < q) (root : E →+* E) (f : Laurent σ E) :
    Laurent σ E := .ofCoeff
  ((f.coeff.comapDomain (sourceIndex q) (sourceIndex_injective hq).injOn).mapRange root root.map_zero)

/-- Coefficient rule for the Laurent-polynomial extraction. -/
theorem extract_coeff (q : ℕ) (hq : 0 < q) (root : E →+* E) (f : Laurent σ E)
    (d : Exponent σ) : (extract q hq root f).coeff d = root (f.coeff (sourceIndex q d)) := rfl

private theorem mem_source_of_mem_extract {q : ℕ} {hq : 0 < q} {root : E →+* E}
    {f : Laurent σ E} {d : Exponent σ} (hd : d ∈ (extract q hq root f).coeff.support) :
    sourceIndex q d ∈ f.coeff.support := by
  rw [Finsupp.mem_support_iff] at hd ⊢
  intro hz
  exact hd ((extract_coeff ..).trans (by rw [hz, map_zero]))

/-- Each exponent before extraction is the sum of an exponent of the test and a
nonnegative shift whose coordinates are bounded by `(q − 1) S`. -/
theorem before_extraction_bounds [Fintype ι] (q : ℕ) (g : ι → MvPolynomial (Option σ) E)
    (f : Laurent σ E) {j : Exponent σ} (hj : j ∈ (f * equationProduct q g).coeff.support) :
    ∃ e ∈ f.coeff.support, ∀ i, e i ≤ j i ∧
      j i ≤ e i + ((q - 1) * ∑ k, (g k).totalDegree : ℕ) := by
  classical
  obtain ⟨e, he, a, ha, rfl⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hj)
  refine ⟨e, he, fun i => ?_⟩
  obtain ⟨hl, hu⟩ := equationProduct_coordinate_bounds q g ha i
  change e i ≤ e i + a i ∧ e i + a i ≤ _
  omega

private theorem extracted_nonnegative {q d : ℤ} (hq : 0 < q) (hl : 0 ≤ q * d + q - 1) :
    0 ≤ d := by
  by_contra! h
  have := mul_le_mul_of_nonneg_left (show d ≤ -1 by omega) hq.le
  linarith

private theorem extracted_lower {q H d : ℤ} (hq : 1 ≤ q) (hH : 0 ≤ H)
    (hl : -H ≤ q * d + q - 1) : -H ≤ d := by
  by_contra! h
  have hd := mul_le_mul_of_nonneg_left (show d ≤ -H - 1 by omega) (by omega : 0 ≤ q)
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) hH]

private theorem extracted_upper {q S L d : ℤ} (hq : 2 ≤ q) (hS : 0 ≤ S) (hL : 0 ≤ L)
    (hu : q * d + q - 1 ≤ 4 * (L + S + 2) + (q - 1) * S) :
    d + L ≤ 4 * (L + S + 2) := by
  by_contra! h
  have hd := mul_le_mul_of_nonneg_left (show 4 * (L + S + 2) - L + 1 ≤ d by omega)
    (by omega : 0 ≤ q)
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (show 0 ≤ 3 * L + 3 * S + 10 by omega)]

/-- The Laurent polynomial in a row of a residue pin matrix, as written in (10.3). -/
noncomputable def rowPolynomial [Fintype ι] (q : ℕ) (hq : 0 < q)
    (g : ι → MvPolynomial (Option σ) E) (root : E →+* E) (a b : E)
    (e μ : Exponent σ) : Laurent σ E :=
  AddMonoidAlgebra.single μ a *
    extract q hq root (AddMonoidAlgebra.single e b * equationProduct q g)

/-- The coefficient of (10.3) before expressing it in the prime-field basis. -/
theorem rowPolynomial_coeff [Fintype ι] (q : ℕ) (hq : 0 < q)
    (g : ι → MvPolynomial (Option σ) E) (root : E →+* E) (a b : E)
    (e μ k : Exponent σ) : (rowPolynomial q hq g root a b e μ).coeff k =
      a * root ((AddMonoidAlgebra.single e b * equationProduct q g).coeff
        (sourceIndex q (k - μ))) := by
  rw [rowPolynomial, AddMonoidAlgebra.coeff_single_mul_apply, extract_coeff]
  simp only [sub_eq_add_neg, add_comm k]

/-- The support of (10.3) stays in the same box. The shift `μ` has zero Laurent coordinate
and coordinate bounds `0 ≤ μᵢ ≤ L`, as follows in particular from its total degree bound. -/
theorem row_supported [Fintype ι] {q L : ℕ} (hq : 2 ≤ q)
    (g : ι → MvPolynomial (Option σ) E) (root : E →+* E) (a b : E)
    (e μ : Exponent σ) (he : InBox (radius L (∑ k, (g k).totalDegree)) e)
    (hμt : μ none = 0) (hμ : ∀ i, 0 ≤ μ (some i) ∧ μ (some i) ≤ L)
    {k : Exponent σ} (hk : k ∈ (rowPolynomial q (by omega) g root a b e μ).coeff.support) :
    InBox (radius L (∑ j, (g j).totalDegree)) k := by
  classical
  let S := ∑ j, (g j).totalDegree
  let H := radius L S
  have hH : (H : ℤ) = 4 * ((L : ℤ) + S + 2) := by simp [H, radius]
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
    (AddMonoidAlgebra.support_coeff_single_mul_subset _ _ _ hk)
  have hs := mem_source_of_mem_extract hd
  obtain ⟨u, hu, hb⟩ := before_extraction_bounds q g _ hs
  have hue : u = e := Finset.mem_singleton.mp (Finsupp.support_single_subset hu)
  subst u
  have hh (i : Option σ) := hb i
  have hwidth : (((q - 1) * S : ℕ) : ℤ) = ((q : ℤ) - 1) * S := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
  have upper (i : Option σ) (hi : e i ≤ H) : d i + L ≤ H := by
    apply le_trans (extracted_upper hq' (Int.natCast_nonneg S) (Int.natCast_nonneg L) ?_) hH.ge
    have h := (hh i).2
    change (q : ℤ) * d i + q - 1 ≤ e i + (((q - 1) * S : ℕ) : ℤ) at h
    rw [hwidth] at h
    linarith
  constructor
  · change - (H : ℤ) ≤ μ none + d none ∧ μ none + d none ≤ H
    rw [hμt, zero_add]
    refine ⟨extracted_lower (by omega) (Int.natCast_nonneg H) (he.1.1.trans (hh none).1), ?_⟩
    have := upper none he.1.2
    omega
  · intro i
    have hpos := extracted_nonnegative (by omega : (0 : ℤ) < q) ((he.2 i).1.trans (hh _).1)
    have htop := upper _ (he.2 i).2
    have := hμ i
    change 0 ≤ μ (some i) + d (some i) ∧ μ (some i) + d (some i) ≤ H
    omega

/-- For any test in `E[X,t,t⁻¹]`, taking `Q` larger than the absolute values of its
exponents brings the extracted test into the fixed box, independently of the test's degree. -/
theorem large_extraction_supported [Fintype ι] {Q : ℕ} (hQ : 0 < Q) (L : ℕ)
    (g : ι → MvPolynomial (Option σ) E) (root : E →+* E) (f : Laurent σ E)
    (hpoly : ∀ e ∈ f.coeff.support, ∀ i, 0 ≤ e (some i))
    (hlarge : ∀ e ∈ f.coeff.support, ∀ i, (e i).natAbs < Q)
    {d : Exponent σ} (hd : d ∈ (extract Q hQ root (f * equationProduct Q g)).coeff.support) :
    InBox (radius L (∑ k, (g k).totalDegree)) d := by
  let S := ∑ k, (g k).totalDegree
  let H := radius L S
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hH : (H : ℤ) = 4 * ((L : ℤ) + S + 2) := by simp [H, radius]
  have hS : (0 : ℤ) ≤ S := Int.natCast_nonneg S
  have hwidth : (((Q - 1) * S : ℕ) : ℤ) = ((Q : ℤ) - 1) * S := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
  obtain ⟨e, he, hspan⟩ := before_extraction_bounds Q g f (mem_source_of_mem_extract hd)
  have hsmall (i : Option σ) : - (Q : ℤ) < e i ∧ e i < Q := by
    have h := hlarge e he i
    omega
  have upper (i : Option σ) : d i ≤ S := by
    have hu := (hspan i).2
    change (Q : ℤ) * d i + Q - 1 ≤ e i + (((Q - 1) * S : ℕ) : ℤ) at hu
    rw [hwidth] at hu
    by_contra! hh
    have hm := mul_le_mul_of_nonneg_left (show (S : ℤ) + 1 ≤ d i by omega) hQ'.le
    nlinarith [(hsmall i).2]
  constructor
  · have hl := (hspan none).1
    change e none ≤ (Q : ℤ) * d none + Q - 1 at hl
    have hlow : -1 ≤ d none := by
      by_contra! hh
      have hm := mul_le_mul_of_nonneg_left (show d none ≤ -2 by omega) hQ'.le
      linarith [(hsmall none).1]
    have hu := upper none
    change - (H : ℤ) ≤ d none ∧ d none ≤ H
    omega
  · intro i
    have hpos := extracted_nonnegative hQ' ((hpoly e he i).trans (hspan _).1)
    have hu := upper (some i)
    change 0 ≤ d (some i) ∧ d (some i) ≤ H
    omega

/-- A positive power of any integer `p ≥ 2` suffices to compress a prescribed finite test
into the box. This auxiliary power may depend on the test. -/
theorem exists_large_extraction [Fintype ι] [Fintype σ] {p : ℕ} (hp : 2 ≤ p) (L : ℕ)
    (g : ι → MvPolynomial (Option σ) E) (f : Laurent σ E)
    (hpoly : ∀ e ∈ f.coeff.support, ∀ i, 0 ≤ e (some i)) :
    ∃ u > 0, ∀ root : E →+* E, ∀ d ∈
      (extract (p ^ u) (pow_pos (by omega) _) root (f * equationProduct (p ^ u) g)).coeff.support,
      InBox (radius L (∑ k, (g k).totalDegree)) d := by
  classical
  let T := ∑ e ∈ f.coeff.support, ∑ i, (e i).natAbs
  refine ⟨T + 1, by omega, fun root d hd => ?_⟩
  apply large_extraction_supported _ L g root f hpoly _ hd
  intro e he i
  have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (e j).natAbs) (Finset.mem_univ i)
  have he' := Finset.single_le_sum (fun e' _ => Nat.zero_le (∑ j, (e' j).natAbs)) he
  have h : (e i).natAbs ≤ T := hi.trans he'
  exact (h.trans (Nat.le_succ T)).trans_lt (Nat.lt_pow_self (by omega))

/-- In an interval shorter than the multiplicative group order, no distinct Laurent exponents
are congruent. The interval may start at a negative exponent. -/
theorem eq_of_modEq_of_mem_interval {lo W N a b : ℤ} (hW : W < N)
    (ha : lo ≤ a ∧ a ≤ lo + W) (hb : lo ≤ b ∧ b ≤ lo + W) (hab : a ≡ b [ZMOD N]) :
    a = b := by
  have h := (hab.sub_right lo).eq
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at h
  omega

end ResidueBox

end BorderVNP
end Computability
end OAI
