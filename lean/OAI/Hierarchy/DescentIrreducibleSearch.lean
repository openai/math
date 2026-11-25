import OAI.Hierarchy.DescentBinaryPolynomial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.Polynomial.Degree.Units

namespace OAI
/-! # Uniform bounded search for the degree-k binary field modulus -/

namespace Hierarchy.DescentBinaryField
open Polynomial DescentGL
open scoped BigOperators Polynomial

/-- Test a candidate factorization with bounded binary coefficient convolution. -/
def productFits {k : ℕ} (w f g : Bits k) : Bool :=
  agreeBelow k (convolution (bitAt f) (bitAt g)) (candidateBit w)

theorem productFits_iff {k : ℕ} (w f g : Bits k) : productFits w f g=true ↔
    wordPolynomial f * wordPolynomial g = candidate w := by
  have left : convolution (bitAt f) (bitAt g) = (wordPolynomial f * wordPolynomial g).coeff := by
    rw [←funext (wordPolynomial_coeff f),←funext (wordPolynomial_coeff g)]
    exact funext (convolution_coeff (wordPolynomial f) (wordPolynomial g))
  have right : candidateBit w = (candidate w).coeff := funext fun n => (candidate_coeff w n).symm
  rw [productFits,left,right]
  apply agreeBelow_poly_iff
  · have h := (natDegree_mul_le (p:=wordPolynomial f) (q:=wordPolynomial g)).trans
      (Nat.add_le_add (wordPolynomial_degree_le f) (wordPolynomial_degree_le g))
    omega
  · rw [candidate_degree]; omega

/-- All proper binary factor pairs have strictly fewer than k+1 coefficients.
The complete table of k-bit words therefore implements the test. -/
def irreducibleTest {k : ℕ} (w : Bits k) : Bool :=
  (words k).all fun f => (words k).all fun g => decide (productFits w f g≠true)

theorem irreducibleTest_iff {k : ℕ} (hk : 0<k) (w : Bits k) :
    irreducibleTest w=true ↔ Irreducible (candidate w) := by
  classical
  have test : irreducibleTest w=true ↔
      ∀f g : Bits k,wordPolynomial f * wordPolynomial g ≠ candidate w := by
    simp only [irreducibleTest,List.all_eq_true,mem_words,true_implies,decide_eq_true_eq]
    exact forall_congr' fun f=>forall_congr' fun g=>(productFits_iff w f g).not
  rw [test]
  constructor
  · intro passes
    apply (candidate_monic w).irreducible_iff_natDegree.mpr
    constructor
    · intro one
      have d := congrArg natDegree one
      simp only [candidate_degree,natDegree_one] at d
      omega
    · intro f g fm gm prod
      by_contra! bad
      have deg := congrArg natDegree prod
      rw [fm.natDegree_mul gm,candidate_degree] at deg
      have fl : f.natDegree<k := by omega
      have gl : g.natDegree<k := by omega
      exact passes (fun i=> f.coeff i.val) (fun i=>g.coeff i.val)
        (by rw [wordPolynomial_of_coeff f fl,wordPolynomial_of_coeff g gl,prod])
  · intro irreducible f g prod
    have nonzero : wordPolynomial f * wordPolynomial g ≠ 0 := by rw [prod]; exact (candidate_monic w).ne_zero
    have deg := congrArg natDegree prod
    rw [natDegree_mul (left_ne_zero_of_mul nonzero) (right_ne_zero_of_mul nonzero),candidate_degree] at deg
    have fl := wordPolynomial_degree_lt hk f
    have gl := wordPolynomial_degree_lt hk g
    rcases irreducible.isUnit_or_isUnit prod.symm with unit | unit <;>
      have zero := natDegree_eq_zero_of_isUnit unit <;> omega

/-- Primitive elements of a finite field give existence. The selector itself
loops only over explicitly encoded words and coefficient tests. -/
private theorem exists_passing_word {k : ℕ} (hk : 0<k) : ∃ w : Bits k, irreducibleTest w=true := by
  let F := ZMod 2
  let K := GaloisField 2 k
  obtain ⟨z,prim⟩ := Field.exists_primitive_element F K
  let p := minpoly F z
  have integral : IsIntegral F z := IsIntegral.of_finite F z
  have deg : p.natDegree=k := ((Field.primitive_element_iff_minpoly_natDegree_eq F z).mp prim).trans
    (GaloisField.finrank (p:=2) hk.ne')
  refine ⟨fun i=>p.coeff i.val,(irreducibleTest_iff hk _).mpr ?_⟩
  rw [candidate_of_coeff p (minpoly.monic integral) deg]
  exact minpoly.irreducible integral

/-- The first passing word in ordinary integer index order. -/
def lookupModulus (k : ℕ) : Option (Bits k) := (words k).find? irreducibleTest

theorem lookupModulus_spec {k : ℕ} (hk : 0<k) :
    ∃ w : Bits k, lookupModulus k=some w ∧ (candidate w).Monic ∧
      (candidate w).natDegree=k ∧ Irreducible (candidate w) := by
  obtain ⟨v,hv⟩ := exists_passing_word hk
  have someResult : (lookupModulus k).isSome := List.find?_isSome.mpr ⟨v,mem_words v,hv⟩
  cases found : lookupModulus k with
  | none => simp [found] at someResult
  | some w => exact ⟨w,rfl,candidate_monic w,candidate_degree w,
      (irreducibleTest_iff hk w).mp (List.find?_some found)⟩

/-- Worst-case bit operation budget for the actual three nested word loops.
Each tested coefficient takes n+1 ANDs, n+1 XORs and a comparison. -/
def preprocessingBitBudget (k : ℕ) :=
  (words k).length * (words k).length * (words k).length *
    (∑ n∈Finset.range (2*k+1),(2*(n+1)+1))

theorem preprocessingBitBudget_bound (k : ℕ) :
    preprocessingBitBudget k≤(2^k)^3*(2*k+1)*(4*k+3) := by
  have each : (∑n∈Finset.range (2*k+1),(2*(n+1)+1))≤(2*k+1)*(4*k+3) := by
    have h : ∀n∈Finset.range (2*k+1),2*(n+1)+1≤4*k+3 := by
      intro n hn
      have := Finset.mem_range.mp hn
      omega
    simpa using (Finset.sum_le_sum (f:=fun n : ℕ=>2*(n+1)+1) (g:=fun _=>4*k+3) h)
  dsimp only [preprocessingBitBudget]
  rw [length_words]
  exact (Nat.mul_le_mul_left _ each).trans_eq (by ring)

/-- Short-circuit a finite list of tests, adding the work charged by every
predicate that is actually evaluated. -/
def allWithCost {S : Type*} (test : S → Bool × ℕ) : List S → Bool × ℕ
  | [] => (true,0)
  | x::xs => let (pass,work) := test x
             if pass then let tail := allWithCost test xs; (tail.1,work+tail.2) else (false,work)

/-- A first-success scan with the same data-dependent work account. -/
def findWithCost {S : Type*} (test : S → Bool × ℕ) : List S → Option S × ℕ
  | [] => (none,0)
  | x::xs => let (pass,work) := test x
             if pass then (some x,work) else let tail := findWithCost test xs; (tail.1,work+tail.2)

theorem allWithCost_read {S : Type*} (test : S → Bool × ℕ) (xs : List S) :
    (allWithCost test xs).1=xs.all (fun x=>(test x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : test x with | mk pass work => cases pass <;> simp [allWithCost,h,ih]

theorem findWithCost_read {S : Type*} (test : S → Bool × ℕ) (xs : List S) :
    (findWithCost test xs).1=xs.find? (fun x=>(test x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : test x with | mk pass work => cases pass <;> simp [findWithCost,h,ih]

theorem allWithCost_bound {S : Type*} (test : S → Bool × ℕ) (xs : List S) (B : ℕ)
    (bounded : ∀x∈xs,(test x).2≤B) : (allWithCost test xs).2≤xs.length*B := by
  induction xs with
  | nil => simp [allWithCost]
  | cons x xs ih =>
    have head := bounded x (List.mem_cons_self ..)
    have tail := ih (fun y hy=>bounded y (List.mem_cons_of_mem _ hy))
    cases h : test x with
    | mk pass work => cases pass <;> simp [allWithCost,h,Nat.succ_mul] at * <;> omega

theorem findWithCost_bound {S : Type*} (test : S → Bool × ℕ) (xs : List S) (B : ℕ)
    (bounded : ∀x∈xs,(test x).2≤B) : (findWithCost test xs).2≤xs.length*B := by
  induction xs with
  | nil => simp [findWithCost]
  | cons x xs ih =>
    have head := bounded x (List.mem_cons_self ..)
    have tail := ih (fun y hy=>bounded y (List.mem_cons_of_mem _ hy))
    cases h : test x with
    | mk pass work => cases pass <;> simp [findWithCost,h,Nat.succ_mul] at * <;> omega

/-- Run polynomial factor-product comparison while charging each coefficient
for its additions, products and equality check. -/
def measuredProduct {k : ℕ} (w f g : Bits k) : Bool × ℕ :=
  allWithCost (fun n=> (decide (convolution (bitAt f) (bitAt g) n=candidateBit w n),2*(n+1)+1))
    (List.range (2*k+1))

private theorem measuredProduct_read {k : ℕ} (w f g : Bits k) : (measuredProduct w f g).1=productFits w f g :=
  allWithCost_read _ _

private theorem measuredProduct_bound {k : ℕ} (w f g : Bits k) :
    (measuredProduct w f g).2 ≤ (2*k+1)*(4*k+3) := by
  unfold measuredProduct
  apply (allWithCost_bound _ _ (4*k+3) ?_).trans_eq (by simp)
  intro n hn
  have := List.mem_range.mp hn
  dsimp
  omega

/-- A candidate modulus passes precisely when none of its word pairs
multiply to it. Charge only the product tests actually encountered. -/
def measuredIrreducible {k : ℕ} (w : Bits k) : Bool × ℕ :=
  allWithCost (fun f=>allWithCost (fun g=>let t:=measuredProduct w f g; (decide (t.1≠true),t.2))
    (words k)) (words k)

private theorem measuredIrreducible_read {k : ℕ} (w : Bits k) :
    (measuredIrreducible w).1=irreducibleTest w := by
  simp only [measuredIrreducible,allWithCost_read,measuredProduct_read,irreducibleTest]

private theorem measuredIrreducible_bound {k : ℕ} (w : Bits k) :
    (measuredIrreducible w).2≤(2^k)^2*((2*k+1)*(4*k+3)) := by
  unfold measuredIrreducible
  apply (allWithCost_bound _ _ (2^k*((2*k+1)*(4*k+3))) ?_).trans_eq (by rw [length_words]; ring)
  intro f _
  apply (allWithCost_bound _ _ ((2*k+1)*(4*k+3)) ?_).trans_eq (by rw [length_words])
  intro g _
  exact measuredProduct_bound w f g

/-- A uniform deterministic search together with the charged bit operations
on its actual sequence of factor comparisons. -/
def measuredLookup (k : ℕ) : Option (Bits k) × ℕ := findWithCost measuredIrreducible (words k)

theorem measuredLookup_spec (k : ℕ) : (measuredLookup k).1=lookupModulus k ∧
    (measuredLookup k).2≤(2^k)^3*(2*k+1)*(4*k+3) := by
  constructor
  · simp only [measuredLookup,findWithCost_read,measuredIrreducible_read,lookupModulus]
  · apply (findWithCost_bound _ _ ((2^k)^2*((2*k+1)*(4*k+3)))
      (fun w _=>measuredIrreducible_bound w)).trans_eq (by rw [length_words]; ring)

end Hierarchy.DescentBinaryField

end OAI
