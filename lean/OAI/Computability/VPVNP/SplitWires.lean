import OAI.Computability.VPVNP.ContractionValue
import OAI.Computability.VPVNP.StarEmbedding
import OAI.Computability.VPVNP.MatrixWire
import OAI.Computability.VPVNP.WireSpectrum
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Contraction of a split pair of wires

In the first case of Theorem 2.4 of *VP and VNP differ over every field*,
the added party is the common endpoint of two bundles of binary wires.
Contracting with one covector gives a rectangular matrix on the old parties.
The identity covector on equal-size bundles recovers the old equality wire.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v w

namespace WireTensor

variable {k : Type u} {J : Type v} [CommSemiring k]

/-- Two wire bundles with a common new endpoint and outside endpoints `a` and `b`. -/
noncomputable def splitWires (a b : J) (I K : Type w) [Fintype I] [Fintype K] :
    Tensor k (Option J) :=
  tensorProduct (wire none (some a) I) (wire none (some b) K)

/-- The center keeps one independent index for each bundle. -/
def splitCenterEquiv (a b : J) (I K : Type w) [Fintype I] [Fintype K] :
    I × K ≃ (splitWires (k := k) a b I K).Basis none where
  toFun z := ((fun _ ↦ z.1, fun h ↦ nomatch h), (fun _ ↦ z.2, fun h ↦ nomatch h))
  invFun z := (z.1.1 rfl, z.2.1 rfl)
  left_inv _ := rfl
  right_inv z := by
    apply Prod.ext <;> apply Prod.ext <;> funext h
    all_goals first | rfl | cases h

/-- The old legs keep just the corresponding outside endpoint indices. -/
def splitLeafEquiv (a b : J) (I K : Type w) [Fintype I] [Fintype K] (j : J) :
    (j = a → I) × (j = b → K) ≃ (splitWires (k := k) a b I K).Basis (some j) where
  toFun z := (((fun h : some j = none ↦ nomatch h), fun h ↦ z.1 (Option.some.inj h)),
              ((fun h : some j = none ↦ nomatch h), fun h ↦ z.2 (Option.some.inj h)))
  invFun z := (fun h ↦ z.1.2 (congrArg some h), fun h ↦ z.2.2 (congrArg some h))
  left_inv _ := rfl
  right_inv z := by
    apply Prod.ext <;> apply Prod.ext <;> funext h
    all_goals first | rfl | cases h

/-- In endpoint bases a covector is a rectangular matrix of independent entries. -/
def splitMatrix (a b : J) (I K : Type w) [Fintype I] [Fintype K]
    (ξ : (splitWires (k := k) a b I K).Basis none → k) : Matrix I K k :=
  fun i j ↦ ξ (splitCenterEquiv a b I K (i, j))

/-- Exact readout of the matrix supplied by the center covector. -/
theorem contractCenter_splitWires_coeff (a b : J) (I K : Type w) [Fintype I] [Fintype K]
    (ξ : (splitWires (k := k) a b I K).Basis none → k)
    (x : (j : J) → (splitWires (k := k) a b I K).Basis (some j)) :
    (contractCenter (splitWires a b I K) ξ).coeff x =
      splitMatrix a b I K ξ ((x a).1.2 rfl) ((x b).2.2 rfl) := by
  classical
  let f (c : (splitWires (k := k) a b I K).Basis none) :=
    ξ c * (splitWires (k := k) a b I K).coeff (withCenter c x)
  change (∑ c, f c) = _
  rw [← (splitCenterEquiv (k := k) a b I K).sum_comp f, Fintype.sum_prod_type]
  change (∑ i : I, ∑ j : K, ξ (splitCenterEquiv a b I K (i, j)) *
    ((if i = (x a).1.2 rfl then 1 else 0) * if j = (x b).2.2 rfl then 1 else 0)) = _
  simp [mul_ite, splitMatrix]

/-- A tensor power of an equality wire is one wire whose index is the tuple
of the individual edge indices. -/
theorem wire_power_mutual [Fintype J] (a b : J) (I : Type w) [Fintype I] (n : ℕ) :
    Restricts (wire (k := k) a b (Fin n → I)) (tensorPowerFin n (wire a b I)) ∧
      Restricts (tensorPowerFin n (wire (k := k) a b I)) (wire a b (Fin n → I)) := by
  classical
  let e (j : J) : (Fin n → (j = a → I) × (j = b → I)) ≃
      (j = a → Fin n → I) × (j = b → Fin n → I) :=
    { toFun := fun z ↦ (fun h i ↦ (z i).1 h, fun h i ↦ (z i).2 h)
      invFun := fun z i ↦ (fun h ↦ z.1 h i, fun h ↦ z.2 h i)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  apply restricts_of_reindex e
  intro x
  simp only [tensorPowerFin, wire, Fintype.prod_boole, funext_iff]
  split_ifs <;> first | rfl | contradiction

/-- The split monomial before regrouping the parallel binary factors. -/
noncomputable def binarySplit (a b : J) (u v : ℕ) : Tensor.{u,v,0} k (Option J) :=
  tensorProduct (tensorPowerFin u (wire none (some a) (Fin 2)))
    (tensorPowerFin v (wire none (some b) (Fin 2)))

/-- Regrouping powers of two binary wires into the two dyadic bundles. -/
theorem binary_splitWires_mutual [Fintype J] (a b : J) (u v : ℕ) :
    let M := binarySplit (k := k) a b u v
    let S := splitWires (k := k) a b (Fin (2 ^ u)) (Fin (2 ^ v))
    Restricts S M ∧ Restricts M S := by
  classical
  have bundle (j : J) (n : ℕ) :
      let W := wire (k := k) none (some j) (Fin (2 ^ n))
      let P := tensorPowerFin n (wire (k := k) none (some j) (Fin 2))
      Restricts W P ∧ Restricts P W := by
    let e : (Fin n → Fin 2) ≃ Fin (2 ^ n) := Fintype.equivOfCardEq (by simp)
    have h := wire_power_mutual (k := k) none (some j) (Fin 2) n
    exact ⟨(wire_restricts_of_embedding _ _ e.toEmbedding).trans h.1,
      h.2.trans (wire_restricts_of_embedding _ _ e.symm.toEmbedding)⟩
  exact ⟨(bundle a u).1.tensorProduct (bundle b v).1, (bundle a u).2.tensorProduct (bundle b v).2⟩

/-- Contraction gives exactly the matrix tensor after local basis changes at the leaves. -/
theorem splitWires_matrix_mutual [Fintype J] (a b : J) (I K : Type w) [Fintype I] [Fintype K]
    (ξ : (splitWires (k := k) a b I K).Basis none → k) :
    let T := contractCenter (splitWires a b I K) ξ
    let M := matrixTensor a b (splitMatrix a b I K ξ)
    Restricts T M ∧ Restricts M T := by
  apply restricts_of_reindex (splitLeafEquiv a b I K)
  intro x
  exact (contractCenter_splitWires_coeff a b I K ξ (fun j ↦ splitLeafEquiv a b I K j (x j))).symm

/-- Conversely every matrix on the two outside endpoints occurs as a center contraction. -/
theorem exists_splitWires_matrix [Fintype J] (a b : J) {I K : Type w} [Fintype I] [Fintype K]
    (M : Matrix I K k) :
    ∃ ξ, Restricts (contractCenter (splitWires a b I K) ξ) (matrixTensor a b M) ∧
      Restricts (matrixTensor a b M) (contractCenter (splitWires a b I K) ξ) := by
  let e := splitCenterEquiv (k := k) a b I K
  let ξ := fun c ↦ M (e.symm c).1 (e.symm c).2
  have hM : splitMatrix a b I K ξ = M := by
    ext i j
    change M (e.symm (e (i, j))).1 (e.symm (e (i, j))).2 = M i j
    rw [e.symm_apply_apply]
  exact ⟨ξ, by simpa only [hM] using splitWires_matrix_mutual a b I K ξ⟩

/-- Embedding an old wire preserves both endpoint bases and adds a trivial
factor at the center. This identifies old and enlarged wire values. -/
theorem embedOld_wire_mutual [Fintype J] (a b : J) (I : Type) [Fintype I] :
    Restricts (embedOld (wire (k := k) a b I)) (wire (some a) (some b) I) ∧
      Restricts (wire (k := k) (some a) (some b) I) (embedOld (wire a b I)) := by
  let e (j : Option J) :
      (wire (k := k) (some a) (some b) I).Basis j ≃ (embedOld (wire (k := k) a b I)).Basis j :=
    match j with
    | none =>
      { toFun := fun _ ↦ PUnit.unit
        invFun := fun _ ↦ ((fun h ↦ nomatch h), fun h ↦ nomatch h)
        left_inv := fun z ↦ by apply Prod.ext <;> funext h <;> cases h
        right_inv := fun _ ↦ rfl }
    | some j =>
      { toFun := fun z ↦ (fun h ↦ z.1 (congrArg some h), fun h ↦ z.2 (congrArg some h))
        invFun := fun z ↦ (fun h ↦ z.1 (Option.some.inj h), fun h ↦ z.2 (Option.some.inj h))
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  apply restricts_of_reindex e
  intro x
  rfl

section Field

variable {k : Type u} [Field k]

/-- Rank bound for the contraction matrix of the two dyadic bundles. -/
theorem rank_splitMatrix_le (a b : J) (u v : ℕ)
    (ξ : (splitWires (k := k) a b (Fin (2 ^ u)) (Fin (2 ^ v))).Basis none → k) :
    (splitMatrix a b (Fin (2 ^ u)) (Fin (2 ^ v)) ξ).rank ≤ 2 ^ min u v := by
  rcases le_total u v with h | h
  · rw [min_eq_left h]
    exact Matrix.rank_le_height _
  · rw [min_eq_right h]
    exact Matrix.rank_le_width _

namespace SpectralPoint

variable [Fintype J]
variable (F : SpectralPoint k J)

/-- An extension on all old tensors restricts to the original wire pseudometric
at every pair of old parties. -/
theorem wireDistance_extension (H : SpectralPoint k (Option J))
    (extendsOld : ∀ T, H.value (embedOld T) = F.value T) (a b : J) :
    H.wireDistance (some a) (some b) = F.wireDistance a b := by
  apply congrArg (fun z : NNReal ↦ Real.log (z : ℝ) / Real.log 2)
  exact (H.value_eq_of_mutual (embedOld_wire_mutual a b (Fin 2))).symm.trans (extendsOld _)

private theorem dyadic_wire_value (a b : J) (n : ℕ) :
    (F.value (wire a b (Fin (2 ^ n))) : ℝ) = (2 : ℝ) ^ ((n : ℝ) * F.wireDistance a b) := by
  rw [F.value_wire_eq_rpow a b (by positivity), Real.rpow_natCast_mul (by norm_num)]
  norm_cast

/-- The contracted value is bounded by the wire with the smaller dimension. -/
theorem value_splitWires_le_min (a b : J) (u v : ℕ)
    (ξ : (splitWires (k := k) a b (Fin (2 ^ u)) (Fin (2 ^ v))).Basis none → k) :
    (F.value (contractCenter (splitWires a b (Fin (2 ^ u)) (Fin (2 ^ v))) ξ) : ℝ) ≤
      (2 : ℝ) ^ ((min u v : ℕ) * F.wireDistance a b) := by
  let M := splitMatrix a b (Fin (2 ^ u)) (Fin (2 ^ v)) ξ
  have hm := (splitWires_matrix_mutual a b (Fin (2 ^ u)) (Fin (2 ^ v)) ξ).2
  rcases le_total u v with h | h
  · rw [min_eq_left h, ← F.dyadic_wire_value]
    exact_mod_cast F.monotone ((wire_restricts_matrixTensor_left a b M).trans hm)
  · rw [min_eq_right h, ← F.dyadic_wire_value]
    exact_mod_cast F.monotone ((wire_restricts_matrixTensor_right a b M).trans hm)

/-- Every joint center covector obeys the split target for arbitrary prescribed
nonnegative lengths whose sum equals the old wire distance. -/
theorem value_splitWires_le (a b : J) (u v : ℕ) {l₁ l₂ : ℝ}
    (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂) (hs : l₁ + l₂ = F.wireDistance a b)
    (ξ : (splitWires (k := k) a b (Fin (2 ^ u)) (Fin (2 ^ v))).Basis none → k) :
    (F.value (contractCenter (splitWires a b (Fin (2 ^ u)) (Fin (2 ^ v))) ξ) : ℝ) ≤
      (2 : ℝ) ^ ((u : ℝ) * l₁ + (v : ℝ) * l₂) := by
  apply (F.value_splitWires_le_min a b u v ξ).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [← hs, mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_left u v) h₁)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right u v) h₂)

/-- With equal bundle widths the identity covector attains the split target. -/
theorem exists_splitWires_value_eq (a b : J) (n : ℕ) {l₁ l₂ : ℝ}
    (hs : l₁ + l₂ = F.wireDistance a b) :
    ∃ ξ, (F.value (contractCenter (splitWires a b (Fin (2 ^ n)) (Fin (2 ^ n))) ξ) : ℝ) =
      (2 : ℝ) ^ ((n : ℝ) * l₁ + (n : ℝ) * l₂) := by
  obtain ⟨ξ, h⟩ := exists_splitWires_matrix a b (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) k)
  rw [matrixTensor_one] at h
  rw [← mul_add, hs, ← F.dyadic_wire_value]
  exact ⟨ξ, congrArg (fun z : NNReal ↦ (z : ℝ)) (F.value_eq_of_mutual h)⟩

/-- The same bound for a monomial in the original binary wire generators times any
embedded old tensor. The covector can couple all binary indices. -/
theorem value_binarySplit_monomial_le (T : Tensor.{u,v,0} k J) (a b : J) (u v : ℕ) {l₁ l₂ : ℝ}
    (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂) (hs : l₁ + l₂ = F.wireDistance a b)
    (ξ : (tensorProduct (embedOld T) (binarySplit a b u v)).Basis none → k) :
    (F.value (contractCenter (tensorProduct (embedOld T) (binarySplit a b u v)) ξ) : ℝ) ≤
      (F.value T : ℝ) * (2 : ℝ) ^ ((u : ℝ) * l₁ + (v : ℝ) * l₂) := by
  rw [contractCenter_old_product, F.value_tensorProduct, NNReal.coe_mul]
  apply mul_le_mul_of_nonneg_left _ (F.value T).coe_nonneg
  obtain ⟨η, hη⟩ := contractCenter_restricts (binary_splitWires_mutual (k := k) a b u v).1
    (fun y ↦ ξ (PUnit.unit, y))
  exact (NNReal.coe_le_coe.mpr (F.monotone hη)).trans (F.value_splitWires_le a b u v h₁ h₂ hs η)

/-- Equal multiplicities attain the monomial target, with the embedded old factor
passing through the contraction. -/
theorem exists_binarySplit_monomial_eq (T : Tensor.{u,v,0} k J) (a b : J) (n : ℕ) {l₁ l₂ : ℝ}
    (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂) (hs : l₁ + l₂ = F.wireDistance a b) :
    ∃ ξ, (F.value (contractCenter (tensorProduct (embedOld T) (binarySplit a b n n)) ξ) : ℝ) =
      (F.value T : ℝ) * (2 : ℝ) ^ ((n : ℝ) * l₁ + (n : ℝ) * l₂) := by
  obtain ⟨η, hη⟩ := F.exists_splitWires_value_eq a b n hs
  obtain ⟨ξ, hξ⟩ := contractCenter_restricts (binary_splitWires_mutual (k := k) a b n n).2 η
  refine ⟨fun y ↦ ξ y.2, le_antisymm (F.value_binarySplit_monomial_le T a b n n h₁ h₂ hs _) ?_⟩
  rw [contractCenter_old_product, F.value_tensorProduct, NNReal.coe_mul, ← hη]
  exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (F.monotone hξ)) (F.value T).coe_nonneg

/-- The upper bound holds for the supremum of all joint contractions. -/
theorem contractionValue_binarySplit_monomial_le [Nonempty J]
    (T : Tensor.{u,v,0} k J) (a b : J) (u v : ℕ) {l₁ l₂ : ℝ}
    (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂) (hs : l₁ + l₂ = F.wireDistance a b) :
    (F.contractionValue (tensorProduct (embedOld T) (binarySplit a b u v)) : ℝ) ≤
      (F.value T : ℝ) * (2 : ℝ) ^ ((u : ℝ) * l₁ + (v : ℝ) * l₂) := by
  apply (F.isLUB_contractionValue _).2
  rintro _ ⟨ξ, rfl⟩
  exact F.value_binarySplit_monomial_le T a b u v h₁ h₂ hs ξ

/-- The supremum for equal multiplicities is the target itself. -/
theorem contractionValue_binarySplit_monomial_eq [Nonempty J]
    (T : Tensor.{u,v,0} k J) (a b : J) (n : ℕ) {l₁ l₂ : ℝ}
    (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂) (hs : l₁ + l₂ = F.wireDistance a b) :
    (F.contractionValue (tensorProduct (embedOld T) (binarySplit a b n n)) : ℝ) =
      (F.value T : ℝ) * (2 : ℝ) ^ ((n : ℝ) * l₁ + (n : ℝ) * l₂) := by
  apply le_antisymm (F.contractionValue_binarySplit_monomial_le T a b n n h₁ h₂ hs)
  obtain ⟨ξ, hξ⟩ := F.exists_binarySplit_monomial_eq T a b n h₁ h₂ hs
  rw [← hξ]
  exact NNReal.coe_le_coe.mpr (F.value_le_contractionValue _ ξ)

end SpectralPoint

namespace RestrictionClass

variable [Fintype J]

/-- On restriction classes the two bundles are the corresponding monomial
in the two added generators. -/
@[simp] theorem ofTensor_binarySplit (a b : J) (u v : ℕ) :
    ofTensor (binarySplit (k := k) a b u v) =
      (ofTensor (wire none (some a) (Fin 2))) ^ u * (ofTensor (wire none (some b) (Fin 2))) ^ v := by
  simp only [binarySplit, ofTensor_tensorProduct, ofTensor_tensorPowerFin]

end RestrictionClass

end Field

end WireTensor

end VPVNP
end Computability
end OAI
