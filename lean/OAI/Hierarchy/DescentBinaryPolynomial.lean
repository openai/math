import OAI.Hierarchy.DescentGLPrefix
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

namespace OAI
/-! # Fixed-length binary polynomial encodings for finite-field preprocessing -/

namespace Hierarchy.DescentBinaryField

open Polynomial DescentGL
open scoped BigOperators Polynomial Classical

/-- Store all bits of one binary index for constant-time coefficient access. -/
def storedWord (k : ℕ) (i : Fin (2^k)) : Bits k :=
  (Vector.ofFn ((finFunctionFinEquiv (m:=2) (n:=k)).symm i)).get

/-- The literal little-endian bit counter in the range `[0,2^k)`. -/
def words (k : ℕ) : List (Bits k) := List.ofFn (storedWord k)

private theorem read_stored {α : Type} {k : ℕ} (v : Fin k→α) : (Vector.ofFn v).get=v := by
  funext j
  exact Vector.getElem_ofFn j.isLt

@[simp] theorem mem_words {k : ℕ} (w : Bits k) : w∈words k := by
  let v : Fin k→Fin 2 := w
  let e : (Fin k→Fin 2) ≃ Fin (2^k) := finFunctionFinEquiv
  refine List.mem_ofFn.mpr ⟨e v,?_⟩
  exact (read_stored (e.symm (e v))).trans (e.symm_apply_apply v)

@[simp] theorem length_words (k : ℕ) : (words k).length=2^k :=
  List.length_ofFn (f:=storedWord k)

/-- Extend the word by zero above its top bit. -/
def bitAt {k : ℕ} (w : Bits k) (n : ℕ) : ZMod 2 := if hn : n<k then w ⟨n,hn⟩ else 0

noncomputable def wordPolynomial {k : ℕ} (w : Bits k) : (ZMod 2)[X] :=
  ∑ i : Fin k, monomial i.val (w i)

theorem wordPolynomial_coeff {k : ℕ} (w : Bits k) (n : ℕ) :
    (wordPolynomial w).coeff n=bitAt w n := by
  classical
  rw [wordPolynomial,finsetSum_coeff]
  by_cases hn : n<k
  · let i : Fin k := ⟨n,hn⟩
    rw [Finset.sum_eq_single i]
    · simp [bitAt,i,hn]
    · intro j _ ne
      have diff : j.val≠n := fun eqn => ne (Fin.ext eqn)
      simp [coeff_monomial,diff]
    · simp
  · rw [bitAt,dite_eq_right hn]
    apply Finset.sum_eq_zero
    intro i _
    have diff : i.val≠n := by omega
    simp [coeff_monomial,diff]

theorem wordPolynomial_degree_lt {k : ℕ} (hk : 0<k) (w : Bits k) : (wordPolynomial w).natDegree<k := by
  have bound : (wordPolynomial w).natDegree≤k-1 := natDegree_le_iff_coeff_eq_zero.mpr (fun n hn=>by
    simp [wordPolynomial_coeff,bitAt,show ¬n<k by omega])
  omega

theorem wordPolynomial_degree_le {k : ℕ} (w : Bits k) : (wordPolynomial w).natDegree≤k :=
  natDegree_le_iff_coeff_eq_zero.mpr fun n hn => by
    simp [wordPolynomial_coeff,bitAt,show ¬n<k by omega]

theorem wordPolynomial_of_coeff {k : ℕ} (p : (ZMod 2)[X]) (hp : p.natDegree<k) :
    wordPolynomial (fun i : Fin k => p.coeff i.val)=p := by
  ext n
  rw [wordPolynomial_coeff]
  by_cases h : n<k
  · simp [bitAt,h]
  · simp [bitAt,h,coeff_eq_zero_of_natDegree_lt (show p.natDegree<n by omega)]

/-- The monic degree `k` polynomial encoded by its `k` lower bits. -/
noncomputable def candidate {k : ℕ} (w : Bits k) : (ZMod 2)[X] := X^k+wordPolynomial w

def candidateBit {k : ℕ} (w : Bits k) (n : ℕ) : ZMod 2 := (if n=k then 1 else 0)+bitAt w n

theorem candidate_coeff {k : ℕ} (w : Bits k) (n : ℕ) : (candidate w).coeff n=candidateBit w n := by
  simp [candidate,candidateBit,wordPolynomial_coeff,coeff_X_pow,eq_comm]

private theorem candidate_top {k : ℕ} (w : Bits k) : (candidate w).coeff k=1 := by
  simp [candidate_coeff,candidateBit,bitAt]

private theorem candidate_degree_le {k : ℕ} (w : Bits k) : (candidate w).natDegree≤k :=
  natDegree_le_iff_coeff_eq_zero.mpr fun n hn => by
    simp [candidate_coeff,candidateBit,bitAt,show n≠k by omega,show ¬n<k by omega]

theorem candidate_degree {k : ℕ} (w : Bits k) : (candidate w).natDegree=k :=
  natDegree_eq_of_le_of_coeff_ne_zero (candidate_degree_le w) (by rw [candidate_top]; exact one_ne_zero)

theorem candidate_monic {k : ℕ} (w : Bits k) : (candidate w).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one k (candidate_degree_le w) (candidate_top w)

theorem candidate_of_coeff {k : ℕ} (p : (ZMod 2)[X]) (monic : p.Monic) (deg : p.natDegree=k) :
    candidate (fun i : Fin k=>p.coeff i.val)=p := by
  ext n
  by_cases h : n<k
  · simp [candidate_coeff,candidateBit,bitAt,h,ne_of_lt h]
  · by_cases eqn : n=k
    · subst n
      rw [candidate_top,←deg]
      exact monic.symm
    · simp [candidate_coeff,candidateBit,bitAt,h,eqn,coeff_eq_zero_of_natDegree_lt (show p.natDegree<n by omega)]

/-- One coefficient of binary carryless multiplication, computed by XORing
the `n+1` products of the two coefficient bits. -/
def convolution (f g : ℕ → ZMod 2) (n : ℕ) : ZMod 2 :=
  ∑ i∈Finset.range (n+1), f i * g (n-i)

theorem convolution_coeff (p q : (ZMod 2)[X]) (n : ℕ) : convolution p.coeff q.coeff n=(p*q).coeff n := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]; rfl

/-- Compare all coefficients up to and including degree `2k`. -/
def agreeBelow (k : ℕ) (f g : ℕ → ZMod 2) : Bool := (List.range (2*k+1)).all fun n => decide (f n=g n)

theorem agreeBelow_iff (k : ℕ) (f g : ℕ → ZMod 2) : agreeBelow k f g=true ↔ ∀ n≤2*k,f n=g n := by
  simp only [agreeBelow,List.all_eq_true,List.mem_range,decide_eq_true_eq,Nat.lt_succ_iff]

theorem agreeBelow_poly_iff {k : ℕ} (p q : (ZMod 2)[X]) (hp : p.natDegree≤2*k) (hq : q.natDegree≤2*k) :
    agreeBelow k p.coeff q.coeff=true ↔ p=q := by
  rw [agreeBelow_iff]
  constructor
  · intro agrees
    ext n
    by_cases inside : n≤2*k
    · exact agrees n inside
    · rw [coeff_eq_zero_of_natDegree_lt (show p.natDegree<n by omega),
        coeff_eq_zero_of_natDegree_lt (show q.natDegree<n by omega)]
  · rintro rfl n _
    rfl

end Hierarchy.DescentBinaryField

end OAI
