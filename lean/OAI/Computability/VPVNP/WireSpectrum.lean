import OAI.Computability.VPVNP.WireTensor
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Spectral points on finite multipartite tensors

A spectral point of Section 2 of *VP and VNP differ over every field* is a
nonnegative, normalized, additive and multiplicative function that is monotone
under local linear restriction. This presentation uses coefficient arrays and
derives invariance under mutual restrictions from monotonicity.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v
open scoped NNReal

namespace WireTensor

/-- A spectral point on finite multipartite tensors over `k`. -/
structure SpectralPoint (k : Type u) (J : Type v) [Field k] [Fintype J] where
  /-- The nonnegative real value assigned to each tensor by this point of the asymptotic
  spectrum. -/
  value : Tensor.{u,v,0} k J → ℝ≥0
  monotone {Y X} : Restricts Y X → value X ≤ value Y
  value_unit : value unit = 1
  value_zero (T) : T.coeff = 0 → value T = 0
  value_directSum (T U) : value (directSum T U) = value T + value U
  value_tensorProduct (T U) : value (tensorProduct T U) = value T * value U

section Diagonals

variable {k : Type u} {J : Type v} [Field k] [Fintype J]

/-- A bijection of labels gives mutual restrictions between the diagonals. -/
theorem diagonal_reindex_mutual {I K : Type} [Fintype I] [Fintype K] (e : I ≃ K) :
    Restricts (diagonal (k := k) (J := J) I) (diagonal K) ∧
      Restricts (diagonal (k := k) (J := J) K) (diagonal I) := by
  apply restricts_of_reindex (fun _ ↦ e.symm)
  intro x
  change J → K at x
  have h : (∃ i : K, ∀ j, x j = i) ↔ (∃ i : I, ∀ j, e.symm (x j) = i) := by
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, fun j ↦ congrArg e.symm (hi j)⟩
    · rintro ⟨i, hi⟩
      exact ⟨e i, fun j ↦ (e.apply_symm_apply (x j)).symm.trans (congrArg e (hi j))⟩
  simp only [diagonal]
  split_ifs <;> tauto

private theorem diagonal_sum_coeff [Nonempty J] {I K : Type} [Fintype I] [Fintype K]
    (x : J → I ⊕ K) :
    (directSum (diagonal I) (diagonal K)).coeff x = (diagonal (k := k) (I ⊕ K)).coeff x := by
  classical
  by_cases h : ∃ i, ∀ j, x j = i
  · obtain ⟨i | i, hi⟩ := h
    · have hx : x = fun _ ↦ Sum.inl i := funext hi
      rw [hx]
      exact (directSum_coeff_inl (diagonal I) (diagonal K) (fun _ ↦ i)).trans (by simp [diagonal])
    · have hx : x = fun _ ↦ Sum.inr i := funext hi
      rw [hx]
      exact (directSum_coeff_inr (diagonal I) (diagonal K) (fun _ ↦ i)).trans (by simp [diagonal])
  · simp only [directSum, Pi.add_apply, applyLocal, diagonal, Fintype.prod_boole, h, ↓reduceIte]
    calc
      _ = (0 : k) + 0 := by
        apply congrArg₂ (· + ·)
        all_goals
          apply Finset.sum_eq_zero
          intro y _
          split_ifs with hy ha
          · obtain ⟨a, ha⟩ := ha
            exact False.elim (h ⟨_, fun j ↦ by rw [hy j, ha j]⟩)
          all_goals simp
      _ = _ := by simp

/-- The diagonal on a disjoint union and the direct sum of the diagonals have
the same coefficients in the sum basis. -/
theorem diagonal_sum_mutual [Nonempty J] (I K : Type) [Fintype I] [Fintype K] :
    Restricts (diagonal (k := k) (J := J) (I ⊕ K)) (directSum (diagonal I) (diagonal K)) ∧
      Restricts (directSum (diagonal (k := k) (J := J) I) (diagonal K)) (diagonal (I ⊕ K)) :=
  restricts_of_reindex (fun _ ↦ Equiv.refl _) diagonal_sum_coeff

/-- A one-dimensional diagonal is mutually restrictable with the unit. -/
theorem diagonal_unit_mutual :
    Restricts (diagonal (k := k) (J := J) (Fin 1)) unit.{u,v,0} ∧
      Restricts (unit.{u,v,0} (k := k) (J := J)) (diagonal (Fin 1)) := by
  apply restricts_of_reindex (fun _ ↦ Equiv.ofUnique PUnit (Fin 1))
  intro x
  have h : ∃ i : Fin 1, ∀ j : J, Equiv.ofUnique PUnit (Fin 1) (x j) = i :=
    ⟨0, fun _ ↦ Subsingleton.elim _ _⟩
  simp only [unit, diagonal]
  split_ifs <;> tauto

end Diagonals

namespace SpectralPoint

variable {k : Type u} {J : Type v} [Field k] [Fintype J] (F : SpectralPoint k J)

/-- Mutual restrictions give equal spectral values. -/
theorem value_eq_of_mutual {T U : Tensor.{u,v,0} k J} (h : Restricts T U ∧ Restricts U T) :
    F.value T = F.value U := le_antisymm (F.monotone h.2) (F.monotone h.1)

/-- Ordinary addition of arrays in common bases is subadditive at a spectral point. -/
theorem value_add_le {B : J → Type} [b : ∀ j, Fintype (B j)] (T U : Array k B) :
    F.value (.mk B b (T + U)) ≤ F.value (.mk B b T) + F.value (.mk B b U) :=
  (F.monotone (directSum_restricts_add T U)).trans_eq (F.value_directSum _ _)

/-- The unit restriction bounds each nonzero tensor's spectral value from below. -/
theorem one_le_value [Nonempty J] (T : Tensor.{u,v,0} k J) (hT : T.coeff ≠ 0) :
    1 ≤ F.value T := F.value_unit.symm.le.trans (F.monotone (restricts_unit_of_ne_zero T hT))


/-- Subadditivity for finite ordinary sums in common bases. -/
theorem value_sum_le {B : J → Type} [b : ∀ j, Fintype (B j)] {ι : Type*}
    (s : Finset ι) (T : ι → Array k B) :
    F.value (.mk B b (∑ i ∈ s, T i)) ≤ ∑ i ∈ s, F.value (.mk B b (T i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (F.value_zero _ rfl).le
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (F.value_add_le _ _).trans (add_le_add_right ih _)

/-- Changing the finite index set of a diagonal by a bijection preserves its value. -/
theorem value_diagonal_congr {I K : Type} [Fintype I] [Fintype K] (e : I ≃ K) :
    F.value (diagonal I) = F.value (diagonal K) :=
  F.value_eq_of_mutual (diagonal_reindex_mutual e)

/-- The diagonal indexed by a disjoint union is the direct sum of its two diagonals. -/
theorem value_diagonal_sum [Nonempty J] (I K : Type) [Fintype I] [Fintype K] :
    F.value (diagonal (I ⊕ K)) = F.value (diagonal I) + F.value (diagonal K) :=
  (F.value_eq_of_mutual (diagonal_sum_mutual I K)).trans (F.value_directSum _ _)

private theorem value_diagonal_one : F.value (diagonal (Fin 1)) = 1 :=
  (F.value_eq_of_mutual diagonal_unit_mutual).trans F.value_unit

/-- Every spectral point has value `n` on the `n`-dimensional all-parties diagonal. -/
theorem value_diagonal_fin [Nonempty J] (n : ℕ) : F.value (diagonal (Fin n)) = n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    apply F.value_zero
    funext x
    simp [diagonal]
  | succ n ih =>
    calc
      F.value (diagonal (Fin (n + 1))) = F.value (diagonal (Fin n ⊕ Fin 1)) :=
        (F.value_diagonal_congr finSumFinEquiv).symm
      _ = F.value (diagonal (Fin n)) + F.value (diagonal (Fin 1)) := F.value_diagonal_sum _ _
      _ = _ := by rw [ih, F.value_diagonal_one, Nat.cast_succ]

/-- The diagonal value counts its finite index set. -/
theorem value_diagonal [Nonempty J] (I : Type) [Fintype I] :
    F.value (diagonal I) = Fintype.card I :=
  (F.value_diagonal_congr (Fintype.equivFin I)).trans (F.value_diagonal_fin _)

/-- The coordinate rank bound controls the spectral value of every tensor. -/
theorem value_le_basis_product [Nonempty J] (T : Tensor.{u,v,0} k J) :
    F.value T ≤ (∏ j, Fintype.card (T.Basis j) : ℕ) :=
  (F.monotone (diagonal_restricts_of_card T)).trans_eq (F.value_diagonal_fin _)

end SpectralPoint


variable {k : Type u} {J : Type v} [Field k] [Fintype J]

/-- Product of a finite family of tensors, regrouping all factors at each party. -/
noncomputable def tensorFamilyProduct {E : Type} [Fintype E] (T : E → Tensor.{u,v,0} k J) :
    Tensor.{u,v,0} k J where
  Basis j := (e : E) → (T e).Basis j
  finiteBasis _ := by classical exact inferInstance
  coeff x := ∏ e, (T e).coeff (fun j ↦ x j e)

namespace SpectralPoint

variable (F : SpectralPoint k J)

private theorem value_finProduct (n : ℕ) (T : Fin n → Tensor.{u,v,0} k J) :
    F.value (tensorFamilyProduct T) = ∏ i, F.value (T i) := by
  classical
  induction n with
  | zero =>
    have h : Restricts unit (tensorFamilyProduct T) ∧ Restricts (tensorFamilyProduct T) unit := by
      apply restricts_of_reindex (fun j ↦ Equiv.equivPUnit ((i : Fin 0) → (T i).Basis j))
      intro c
      simp [tensorFamilyProduct, unit]
    simpa using (F.value_eq_of_mutual h).symm.trans F.value_unit
  | succ n ih =>
    let rest := tensorFamilyProduct (fun i : Fin n ↦ T i.succ)
    have h : Restricts (tensorProduct (T 0) rest) (tensorFamilyProduct T) ∧
        Restricts (tensorFamilyProduct T) (tensorProduct (T 0) rest) := by
      apply restricts_of_reindex (fun j ↦ (Fin.consEquiv (fun i ↦ (T i).Basis j)).symm)
      intro c
      change (∏ e, (T e).coeff (fun j ↦ c j e)) = _
      rw [Fin.prod_univ_succ]
      rfl
    rw [← F.value_eq_of_mutual h, F.value_tensorProduct, Fin.prod_univ_succ]
    exact congrArg (F.value (T 0) * ·) (ih _)

/-- Finite multiplicativity, including the empty product. -/
theorem value_tensorFamilyProduct {E : Type} [Fintype E] (T : E → Tensor.{u,v,0} k J) :
    F.value (tensorFamilyProduct T) = ∏ e, F.value (T e) := by
  classical
  let e := (Fintype.equivFin E).symm
  let Ts (i : Fin (Fintype.card E)) := T (e i)
  have h : Restricts (tensorFamilyProduct Ts) (tensorFamilyProduct T) ∧
      Restricts (tensorFamilyProduct T) (tensorFamilyProduct Ts) := by
    apply restricts_of_reindex (fun j ↦ (Equiv.piCongrLeft (fun i ↦ (T i).Basis j) e).symm)
    intro c
    change (∏ i, (T i).coeff (fun j ↦ c j i)) = _
    rw [← e.prod_comp (fun i ↦ (T i).coeff (fun j ↦ c j i))]
    rfl
  rw [← F.value_eq_of_mutual h, value_finProduct]
  exact e.prod_comp (fun i ↦ F.value (T i))

/-- The value of an equality-wire network is the product of the values of its individual
edges, even if endpoints repeat or different wires have different index types. -/
theorem value_wireNetwork {E : Type} [Fintype E] (a b : E → J) (I : E → Type)
    [∀ e, Fintype (I e)] : F.value (wireNetwork a b I) =
      ∏ e, F.value (wire (a e) (b e) (I e)) := by
  classical
  let T (e : E) : Tensor k J := wire (a e) (b e) (I e)
  have h : Restricts (wireNetwork a b I) (tensorFamilyProduct T) ∧
      Restricts (tensorFamilyProduct T) (wireNetwork a b I) := by
    apply restricts_of_reindex (fun j ↦ Equiv.arrowProdEquivProdArrow E
      (fun e ↦ j = a e → I e) (fun e ↦ j = b e → I e))
    intro c
    rfl
  exact (F.value_eq_of_mutual h).trans (F.value_tensorFamilyProduct T)

end SpectralPoint

namespace SpectralPoint

variable {k : Type u} {J : Type v} [Field k] [Fintype J] (F : SpectralPoint k J)

/-- Equal wire index cardinalities give equal spectral values. -/
theorem value_wire_equiv (a b : J) {I K : Type} [Fintype I] [Fintype K] (e : I ≃ K) :
    F.value (wire a b I) = F.value (wire a b K) :=
  F.value_eq_of_mutual ⟨wire_restricts_of_embedding _ _ e.symm.toEmbedding,
    wire_restricts_of_embedding _ _ e.toEmbedding⟩

/-- The spectral value of a wire as a multiplicative function of its dimension. -/
noncomputable def wireDimension (a b : J) : ℕ →* ℝ where
  toFun q := F.value (wire a b (Fin q))
  map_one' := by
    exact_mod_cast (F.value_eq_of_mutual (wire_one a b)).symm.trans F.value_unit
  map_mul' m n := by
    have h := F.value_wire_equiv a b (finProdFinEquiv (m := m) (n := n))
    rw [F.value_eq_of_mutual (wire_tensorProduct a b (Fin m) (Fin n)),
      F.value_tensorProduct] at h
    exact_mod_cast h.symm

theorem wireDimension_monotone (a b : J) : Monotone (F.wireDimension a b) :=
  fun _ _ h ↦ NNReal.coe_le_coe.mpr (F.monotone (wire_restricts_of_le a b h))

theorem one_le_wireDimension (a b : J) {q : ℕ} (hq : 0 < q) : 1 ≤ F.wireDimension a b q := by
  simpa using F.wireDimension_monotone a b (show 1 ≤ q from hq)

/-- Base-two logarithm of the two-dimensional wire value, as in Section 2.1. -/
noncomputable def wireDistance (a b : J) : ℝ :=
  Real.log (F.wireDimension a b 2) / Real.log 2

theorem wireDistance_nonneg (a b : J) : 0 ≤ F.wireDistance a b :=
  div_nonneg (Real.log_nonneg (F.one_le_wireDimension a b (by decide))) (Real.log_pos (by norm_num)).le

theorem wireDistance_self (a : J) : F.wireDistance a a = 0 := by
  have hle := (F.monotone (unit_restricts_loop a (Fin 2))).trans_eq F.value_unit
  have heq := le_antisymm (show F.wireDimension a a 2 ≤ 1 by exact_mod_cast hle)
    (F.one_le_wireDimension a a (by decide))
  simp [wireDistance, heq]

theorem wireDistance_comm (a b : J) : F.wireDistance a b = F.wireDistance b a := by
  exact congrArg (fun x : ℝ≥0 ↦ Real.log x / Real.log 2)
    (F.value_eq_of_mutual (wire_swap a b (Fin 2)))

theorem wireDistance_triangle (a b c : J) :
    F.wireDistance a c ≤ F.wireDistance a b + F.wireDistance b c := by
  have h := F.monotone (restricts_wire_triangle a b c (Fin 2))
  rw [F.value_tensorProduct] at h
  have hval : F.wireDimension a c 2 ≤ F.wireDimension a b 2 * F.wireDimension b c 2 := by
    exact_mod_cast h
  have hp (i j : J) : 0 < F.wireDimension i j 2 := zero_lt_one.trans_le
    (F.one_le_wireDimension i j (by decide))
  have hlog := Real.log_le_log (hp a c) hval
  rw [Real.log_mul (hp a b).ne' (hp b c).ne'] at hlog
  simpa only [wireDistance, ← add_div] using
    div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- The wire pseudometric induced by a spectral point on the party set. -/
@[instance_reducible] noncomputable def wirePseudoMetric : PseudoMetricSpace J where
  dist := F.wireDistance
  dist_self := F.wireDistance_self
  dist_comm := F.wireDistance_comm
  dist_triangle := F.wireDistance_triangle

theorem wireDistance_le_one (a b : J) : F.wireDistance a b ≤ 1 := by
  have : Nonempty J := ⟨a⟩
  have h := (F.monotone (diagonal_restricts_wire a b (Fin 2))).trans_eq (F.value_diagonal_fin 2)
  have hle : F.wireDimension a b 2 ≤ 2 := by exact_mod_cast h
  have hp := zero_lt_one.trans_le (F.one_le_wireDimension a b (by decide : 0 < 2))
  exact (div_le_one (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr (Real.log_le_log hp hle)

/-- Every positive-dimensional wire follows the same power law at this spectral point. -/
theorem value_wire_eq_rpow (a b : J) {q : ℕ} (hq : 0 < q) :
    (F.value (wire a b (Fin q)) : ℝ) = (q : ℝ) ^ F.wireDistance a b :=
  monotone_dimension_power_law (F.wireDimension a b) (F.wireDimension_monotone a b) hq

/-- The spectral value of a matrix factorization is bounded by the product of the
wire values between terminals and centers and the wire between centers. -/
theorem value_cutFactorization_le {R : Type} [Fintype R]
    (place : R → J) (side : R → Bool) (center : Bool → J)
    (B : R → Type) [∀ r, Fintype (B r)] (K : Type) [Fintype K]
    (L : ((r : R) → side r = false → B r) → K → k)
    (M : ((r : R) → side r = true → B r) → K → k) :
    F.value (placedTensor place B (fun x ↦ ∑ z, L (fun r _ ↦ x r) z * M (fun r _ ↦ x r) z)) ≤
      F.value (wire (center false) (center true) K) *
        ∏ r, F.value (wire (place r) (center (side r)) (B r)) := by
  have h := F.monotone (cutFactorization_restricts place side center B K L M)
  rw [F.value_wireNetwork, Fintype.prod_option] at h
  exact h


/-- Each edge contributes its index cardinality raised to the distance between
its endpoints. This includes parallel edges and loops. -/
theorem value_wireNetwork_eq_prod_rpow {E : Type} [Fintype E] (a b : E → J) (I : E → Type)
    [∀ e, Fintype (I e)] (hI : ∀ e, 0 < Fintype.card (I e)) :
    (F.value (wireNetwork a b I) : ℝ) =
      ∏ e, (Fintype.card (I e) : ℝ) ^ F.wireDistance (a e) (b e) := by
  rw [F.value_wireNetwork, NNReal.coe_prod]
  apply Finset.prod_congr rfl
  intro e _
  rw [F.value_wire_equiv _ _ (Fintype.equivFin (I e))]
  exact F.value_wire_eq_rpow _ _ (hI e)

/-- The value of binary wires with varying bit widths, as used in Section 6. -/
theorem value_binary_wireNetwork {E : Type} [Fintype E] (a b : E → J) (width : E → ℕ) :
    (F.value (wireNetwork a b (fun e ↦ Fin (2 ^ width e))) : ℝ) =
      (2 : ℝ) ^ ∑ e, (width e : ℝ) * F.wireDistance (a e) (b e) := by
  rw [F.value_wireNetwork_eq_prod_rpow _ _ _ (fun e ↦ by simp)]
  rw [Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- The base-two logarithm of a binary wire network's spectral value is the
sum of edge widths weighted by wire distances. -/
theorem log2_value_binary_wireNetwork {E : Type} [Fintype E] (a b : E → J) (width : E → ℕ) :
    Real.log (F.value (wireNetwork a b (fun e ↦ Fin (2 ^ width e)))) / Real.log 2 =
      ∑ e, (width e : ℝ) * F.wireDistance (a e) (b e) := by
  rw [F.value_binary_wireNetwork, Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    mul_div_cancel_right₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

end SpectralPoint

end WireTensor

end VPVNP
end Computability
end OAI
