import OAI.Computability.MultitapeWeakETH.PortTemplates
import OAI.Computability.BorderVNP.BranchSpecializationConstants
import Mathlib.RingTheory.Norm.Basic

/-! # Fixed number-field coordinates for the characteristic-zero templates -/

namespace OAI.Computability.MultitapeWeakETH
open VPVNP Compression NumberField
open scoped NumberField Classical BigOperators
noncomputable section

/-- One number field suffices for the two compression blocks, with one
integer clearing every denominator. Both are chosen before the input size. -/
theorem integral_templates_of_port (port : PortZero) :
    ∃ (S : BlockSchedule (AlgebraicClosure ℚ)) (B : S.Templates) (K : Type) (_ : Field K)
      (_ : NumberField K) (f : B.Entry → K), 0 < S.laneBits ∧ 2 ≤ B.growthConstant ∧
      B.IsSolution f ∧ ∃ d : ℤ, d ≠ 0 ∧ ∀ i, IsIntegral ℤ ((d:K)*f i) := by
  obtain ⟨S,B,hlanes,growth,f,sol⟩ := templates_of_port port
  let _ : Fintype B.Entry := Fintype.ofFinite _
  obtain ⟨K,_,_,y,transfer,_⟩ := BorderVNP.Specialization.exists_numberField_realization
    (AlgebraicClosure ℚ) f ∅ (by simp)
  obtain ⟨d,hd,integral⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image y)
  exact ⟨S,B,K,inferInstance,inferInstance,y,hlanes,growth,fun o => transfer _ (sol o),d,hd,
    fun i => by simpa only [zsmul_eq_mul] using integral (y i) (Finset.mem_image_of_mem y (Finset.mem_univ i))⟩

namespace TemplateArithmetic

variable {I K : Type} [Fintype I] [Field K] [NumberField K] (f : I → K) (d : ℤ)
    (integral : ∀ i, IsIntegral ℤ ((d:K)*f i))

def numerator (i : I) : 𝓞 K := ⟨(d:K)*f i,integral i⟩

/-- Multiplication by a fixed template entry becomes an integer matrix
with the one common denominator d. -/
def numeratorMatrix (i : I) :=
  Algebra.leftMulMatrix (RingOfIntegers.basis K) (numerator f d integral i)

omit [Fintype I] [NumberField K] in
theorem scaled_product (is : List I) :
    algebraMap (𝓞 K) K (is.map (numerator f d integral)).prod =
      (d:K)^is.length*(is.map f).prod := by
  induction is with
  | nil => simp
  | cons a is ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,map_mul,ih,pow_succ]
    change (d*f a)*(_*_) = _; ring

/-- Bound the integer coordinates of a matrix product one step at a time.
The same fixed constants work for every monomial in every input expansion. -/
theorem coordinates_bound :
    ∃ C : ℕ, 0 < C ∧ ∀ is : List I, ∀ j,
      (((RingOfIntegers.basis K).repr (is.map (numerator f d integral)).prod j).natAbs) ≤
        C^(is.length+1) := by
  let basis := RingOfIntegers.basis K
  let J := Module.Free.ChooseBasisIndex ℤ (𝓞 K)
  let M := numeratorMatrix f d integral
  let bound := 1+(Finset.univ.sup fun p : I × J × J => (M p.1 p.2.1 p.2.2).natAbs) +
    Finset.univ.sup (fun j : J => (basis.repr 1 j).natAbs)
  let C := (Fintype.card J+1)*bound
  have positive : 0 < bound := by dsimp [bound]; omega
  have boundC : bound ≤ C := Nat.le_mul_of_pos_left bound (by omega)
  have entry (i : I) (j k : J) : (M i j k).natAbs ≤ bound := by
    have h := Finset.le_sup (f:=fun p : I × J × J => (M p.1 p.2.1 p.2.2).natAbs)
      (Finset.mem_univ (i,j,k))
    dsimp only at h
    dsimp only [bound]; omega
  refine ⟨C,positive.trans_le boundC,?_⟩
  intro is
  induction is with
  | nil =>
    intro j
    simp only [List.map_nil,List.prod_nil,List.length_nil,zero_add,pow_one]
    apply le_trans _ boundC
    have h := Finset.le_sup (f:=fun j : J => (basis.repr 1 j).natAbs) (Finset.mem_univ j)
    change (basis.repr 1 j).natAbs ≤ bound
    dsimp only [bound]; omega
  | cons i is ih =>
    intro j
    let a := (is.map (numerator f d integral)).prod
    have eq := congrFun (Algebra.leftMulMatrix_mulVec_repr basis (numerator f d integral i) a) j
    change ((∑ k, M i j k*basis.repr a k) : ℤ) = basis.repr (numerator f d integral i*a) j at eq
    change (basis.repr (numerator f d integral i*a) j).natAbs ≤ C^((is.length+1)+1)
    rw [← eq,pow_succ]
    calc
      _ ≤ ∑ k, (M i j k*basis.repr a k).natAbs := by
        exact Int.natAbs_sum_le _ _
      _ ≤ ∑ _ : J, bound*C^(is.length+1) := Finset.sum_le_sum fun k _ => by
        rw [Int.natAbs_mul]; exact Nat.mul_le_mul (entry i j k) (ih k)
      _ ≤ _ := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
        calc
          _ = C^(is.length+1)*(Fintype.card J*bound) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_succ _))

end TemplateArithmetic
end
end OAI.Computability.MultitapeWeakETH
