import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Blocks

open OAI.LinearAlgebra.MatrixExponent.Integral OAI.LinearAlgebra.TensorSpectrum

noncomputable section

/-!
# Actual finite tensor rank

The natural tensor is the diagonal coefficient tensor. Its local restrictions
are exactly the tensors admitting the corresponding number of rank-one terms.
Every finite coefficient tensor has such a decomposition, obtained by expanding
its individual coefficients. Exact rank is therefore a genuine minimum.
-/

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper
namespace CoefficientTensor

/-- The diagonal tensor with `n` independent scalar products. -/
def natTensor (n : ℕ) : Tensor O (Fin n) (Fin n) (Fin n) :=
  fun x y z => if x = y ∧ x = z then 1 else 0

theorem restrict_natTensor {X Y Z : Type*} (n : ℕ)
    (a : X → Fin n → O) (b : Y → Fin n → O) (c : Z → Fin n → O) :
    Tensor.restrict a b c (natTensor n) =
      fun x y z => ∑ i, a x i * b y i * c z i := by
  classical
  funext x y z
  simp [Tensor.restrict, natTensor, mul_ite, ite_and]

theorem rankAtMost_natTensor (n : ℕ) : Tensor.RankAtMost (natTensor n) n := by
  classical
  refine ⟨fun i x => if i = x then 1 else 0,
    fun i y => if i = y then 1 else 0,
    fun i z => if i = z then 1 else 0, ?_⟩
  funext x y z
  by_cases hxy : x = y <;> by_cases hxz : x = z <;>
    simp_all [natTensor, Tensor.rankOne, mul_ite, eq_comm]

/-- This equivalence exposes all three local matrices of the restriction. -/
theorem rankAtMost_iff_natTensor_restricts {X Y Z : Type*}
    (T : Tensor O X Y Z) (n : ℕ) :
    Tensor.RankAtMost T n ↔ Restricts (natTensor n) T := by
  constructor
  · rintro ⟨a, b, c, h⟩
    refine ⟨fun x i => a i x, fun y i => b i y, fun z i => c i z, ?_⟩
    simpa only [restrict_natTensor, Tensor.rankOne] using h
  · intro h
    exact h.rankAtMost (rankAtMost_natTensor n)

/-- The diagonal tensor on a sum of dimensions separates into its two blocks
under the actual standard bijection of finite coordinate sets. -/
theorem natTensor_add_pullback (r s : ℕ) :
    Tensor.pullback (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s))
      finSumFinEquiv finSumFinEquiv (natTensor (r + s)) =
      blockSum (natTensor r) (natTensor s) := by
  funext x y z
  simp only [Tensor.pullback, natTensor, Equiv.apply_eq_iff_eq]
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;>
    simp [blockSum, natTensor]

theorem natTensor_add_restricts (r s : ℕ) :
    Restricts (natTensor (r + s)) (blockSum (natTensor r) (natTensor s)) := by
  have h := Restricts.pullback (natTensor (r + s))
    (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)) finSumFinEquiv finSumFinEquiv
  rwa [natTensor_add_pullback] at h

theorem rankAtMost_blockSum {X Y Z U V W : Type*}
    {T : Tensor O X Y Z} {S : Tensor O U V W} {r s : ℕ}
    (hT : Tensor.RankAtMost T r) (hS : Tensor.RankAtMost S s) :
    Tensor.RankAtMost (blockSum T S) (r + s) := by
  apply (rankAtMost_iff_natTensor_restricts (blockSum T S) (r + s)).mpr
  exact (natTensor_add_restricts r s).trans
    (((rankAtMost_iff_natTensor_restricts T r).mp hT).blockSum
      ((rankAtMost_iff_natTensor_restricts S s).mp hS))

variable {X Y Z U V W : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Expand each actual coefficient into a separate rank-one tensor. -/
theorem rankAtMost_card (T : Tensor O X Y Z) :
    Tensor.RankAtMost T (Fintype.card (X × Y × Z)) := by
  classical
  let a : (X × Y × Z) → X → O :=
    fun p x => if p.1 = x then T p.1 p.2.1 p.2.2 else 0
  let b : (X × Y × Z) → Y → O := fun p y => if p.2.1 = y then 1 else 0
  let c : (X × Y × Z) → Z → O := fun p z => if p.2.2 = z then 1 else 0
  have h := Tensor.rankAtMost_sum_rankOne a b c
  have heq : (fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z) = T := by
    funext x y z
    simp [a, b, c, Tensor.rankOne, Fintype.sum_prod_type, mul_ite]
  rwa [heq] at h

theorem rankAtMost_finite (T : Tensor O X Y Z) :
    ∃ n : ℕ, Tensor.RankAtMost T n :=
  ⟨_, rankAtMost_card T⟩

/-- Selecting the first coordinates realizes the usual comparison of diagonal
tensors by actual local coefficient matrices. -/
theorem natTensor_restricts_of_le {r s : ℕ} (h : r ≤ s) :
    Restricts (natTensor s) (natTensor r) := by
  have hp := Restricts.pullback (natTensor s) (Fin.castLE h) (Fin.castLE h) (Fin.castLE h)
  have heq : Tensor.pullback (Fin.castLE h) (Fin.castLE h) (Fin.castLE h)
      (natTensor s) = natTensor r := by
    funext x y z
    simp [Tensor.pullback, natTensor, Fin.ext_iff]
  rwa [heq] at hp

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem rankAtMost_mono {T : Tensor O X Y Z} {r s : ℕ}
    (hT : Tensor.RankAtMost T r) (hrs : r ≤ s) : Tensor.RankAtMost T s := by
  apply (rankAtMost_iff_natTensor_restricts T s).mpr
  exact (natTensor_restricts_of_le hrs).trans
    ((rankAtMost_iff_natTensor_restricts T r).mp hT)

theorem unit_restricts_natTensor_one {T : Tensor O X Y Z} (hT : ∃ x y z, T x y z = 1) :
    Restricts T (natTensor 1) := by
  classical
  obtain ⟨x, y, z, hxyz⟩ := hT
  refine ⟨fun _ i => if i = x then 1 else 0,
    fun _ j => if j = y then 1 else 0,
    fun _ k => if k = z then 1 else 0, ?_⟩
  funext i j k
  have hij : i = j := Subsingleton.elim _ _
  have hik : i = k := Subsingleton.elim _ _
  subst j
  subst k
  simp [Tensor.restrict, natTensor, ite_mul, mul_ite, hxyz]

/-- The least size of an actual rank-one decomposition. -/
noncomputable def rank (T : Tensor O X Y Z) : ℕ := by
  classical
  exact Nat.find (rankAtMost_finite T)

theorem rank_spec (T : Tensor O X Y Z) : Tensor.RankAtMost T (rank T) := by
  classical
  exact Nat.find_spec (rankAtMost_finite T)

theorem rank_le_iff (T : Tensor O X Y Z) (n : ℕ) :
    rank T ≤ n ↔ Tensor.RankAtMost T n := by
  classical
  constructor
  · exact rankAtMost_mono (rank_spec T)
  · exact Nat.find_min' (rankAtMost_finite T)

theorem rank_mono [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor O X Y Z} {S : Tensor O U V W} (h : Restricts T S) :
    rank S ≤ rank T :=
  (rank_le_iff S _).mpr (h.rankAtMost (rank_spec T))

theorem rank_product_le [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor O X Y Z) (S : Tensor O U V W) :
    rank (Tensor.product T S) ≤ rank T * rank S :=
  (rank_le_iff _ _).mpr ((rank_spec T).product (rank_spec S))

theorem rank_blockSum_le [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor O X Y Z) (S : Tensor O U V W) :
    rank (blockSum T S) ≤ rank T + rank S :=
  (rank_le_iff _ _).mpr (rankAtMost_blockSum (rank_spec T) (rank_spec S))

theorem rank_eq_zero_iff (T : Tensor O X Y Z) : rank T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hr := rank_spec T
    rw [h] at hr
    rcases hr with ⟨a, b, c, heq⟩
    funext x y z
    simpa using congrFun (congrFun (congrFun heq x) y) z
  · rintro rfl
    exact Nat.eq_zero_of_le_zero
      ((rank_le_iff (0 : Tensor O X Y Z) 0).mpr Tensor.rankAtMost_zero)

end CoefficientTensor

namespace TensorRep

noncomputable def rank (T : TensorRep) : ℕ := CoefficientTensor.rank T.coeff

theorem Restricts.rank_le {A B : TensorRep} (h : Restricts A B) : rank B ≤ rank A :=
  CoefficientTensor.rank_mono h

theorem Equivalent.rank_eq {A B : TensorRep} (h : Equivalent A B) : rank A = rank B :=
  Nat.le_antisymm h.2.rank_le h.1.rank_le

end TensorRep

namespace TensorClass

theorem ofTensor_natTensor_add (r s : ℕ) :
    ofTensor (CoefficientTensor.natTensor (r + s)) =
      ofTensor (CoefficientTensor.blockSum
        (CoefficientTensor.natTensor r) (CoefficientTensor.natTensor s)) := by
  have h := ofTensor_pullback_equiv (CoefficientTensor.natTensor (r + s))
    (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)) finSumFinEquiv finSumFinEquiv
  rw [CoefficientTensor.natTensor_add_pullback] at h
  exact h.symm

theorem ofTensor_natTensor_one :
    ofTensor (CoefficientTensor.natTensor 1) =
      ofTensor (fun (_ _ _ : PUnit) => (1 : O)) := by
  let e : PUnit ≃ Fin 1 := Equiv.ofUnique _ _
  have h := ofTensor_pullback_equiv (CoefficientTensor.natTensor 1) e e e
  have heq : Tensor.pullback e e e (CoefficientTensor.natTensor 1) =
      fun (_ _ _ : PUnit) => (1 : O) := by
    funext x y z
    have hxy : x = y := Subsingleton.elim _ _
    have hxz : x = z := Subsingleton.elim _ _
    subst y
    subst z
    simp [Tensor.pullback, CoefficientTensor.natTensor]
  rw [heq] at h
  exact h.symm

theorem ofTensor_natTensor_zero :
    ofTensor (CoefficientTensor.natTensor 0) =
      ofTensor (0 : Tensor O Empty Empty Empty) := by
  apply ofTensor_eq
  · refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
    funext x
    exact Empty.elim x
  · refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
    funext x
    exact Fin.elim0 x

/-- Exact rank is invariant under mutual local restriction. -/
noncomputable def rank : TensorClass → ℕ :=
  Quotient.lift TensorRep.rank (fun _ _ h => h.rank_eq)

@[simp] theorem rank_ofRep (T : TensorRep) : rank (ofRep T) = T.rank := rfl

theorem rank_mono {A B : TensorClass} (h : A ≤ B) : rank A ≤ rank B := by
  induction A using Quotient.inductionOn with | h A =>
    induction B using Quotient.inductionOn with | h B =>
      exact TensorRep.Restricts.rank_le h

theorem rank_ofTensor {X Y Z : Type*} (T : Tensor O X Y Z) [Fintype X] [Fintype Y] [Fintype Z] :
    rank (ofTensor T) = CoefficientTensor.rank T := by
  apply Nat.le_antisymm
  · exact CoefficientTensor.rank_mono (TensorRep.restricts_ofTensor T)
  · exact CoefficientTensor.rank_mono (TensorRep.ofTensor_restricts T)

end TensorClass
end OAI.LinearAlgebra.MatrixExponent.Integral.Upper
