import OAI.Computability.BorderVNP.CrossingNetworkSplit
import OAI.Computability.BorderVNP.CrossingIdentity
import OAI.Computability.BorderVNP.CrossingFusionTables

/-!
# The border identity with a strict wire saving

For a fixed width, the orientation sum of the two explicitly numbered integral side
tables is the antipodal tensor. Replacing its first sides by independent balanced
approximations yields fixed, affordable three-junction networks. Border interpolation
and the selector charge then give an exact paid identity at a positive multiple of
the original width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

variable {D p m r : ℕ} {K : Type*} [Field K]

/-- A pair of integer side tensors with `D` terminal groups and `p` bridge groups.
The orientation selects one terminal from each antipodal pair. -/
abbrev SidePair (D p m : ℕ) :=
  Bool → (Fin D → Bool) → (Fin D → Fin (2^m)) → (Fin p → Fin (2^m)) → ℤ

/-- Extend the integer entries to a field and collect the two types of ports into one tensor. -/
def fieldSide (K : Type*) [Field K] (B : SidePair D p m)
    (left : Bool) (o : Fin D → Bool) (labels : (Fin D ⊕ Fin p) → Fin (2^m)) : K :=
  B left o (fun i ↦ labels (.inl i)) (fun i ↦ labels (.inr i))

/-- An exact sum of fused two-side integer contractions, before extension to a field. -/
def IsAntipodalDecomposition (B : SidePair D p m) : Prop :=
  ∀ x y, (∑ o, ∑ j, B true o (sideInputs o x y) j * B false o (sideInputs o y x) j) =
    ∏ i, if x i = y i then 1 else 0

/-- The integral mixed-radix side as a field-valued tensor on the terminal and bridge parties. -/
noncomputable abbrev scalarSide (K : Type*) [Field K] (w : WireStates (leastEnergy m) (2 ^ m))
    (num : StateNumbering) (D : ℕ) :=
  fieldSide K (fun left ↦ sideTable w num left D)

/-- Contracting the integral fused sides on bit-word ports gives the antipodal tensor
after any change of characteristic. -/
theorem sidesContraction_fieldSide (B : SidePair D p m) (hB : IsAntipodalDecomposition B) :
    sidesContraction (fieldSide K B true) (fieldSide K B false) =
      antipodalTensor K D m := by
  classical
  funext x
  let X (i : Fin D) := cableLabels m (x (i,true))
  let Y (i : Fin D) := cableLabels m (x (i,false))
  have h := congrArg (Int.castRingHom K) (hB X Y)
  simp only [map_sum, map_mul, map_prod, apply_ite, map_one, map_zero] at h
  have hL (o : Fin D → Bool) (j : Fin p → Fin (2^m)) :
      fieldSide K B true o (junctionLabels m o x j) =
        (B true o (sideInputs o X Y) j : ℤ) := by
    unfold fieldSide
    congr 2
    funext i
    cases ho : o i <;> simp [X, Y, junctionLabels, sideLabels, sideInputs, ho] <;> rw [ho]
  have hR (o : Fin D → Bool) (j : Fin p → Fin (2^m)) :
      fieldSide K B false o (junctionLabels m (fun i ↦ !o i) x j) =
        (B false o (sideInputs o Y X) j : ℤ) := by
    unfold fieldSide
    congr 2
    funext i
    cases ho : o i <;> simp [X, Y, junctionLabels, sideLabels, sideInputs, ho] <;> rw [ho] <;> rfl
  unfold sidesContraction
  simp_rw [hL, hR]
  have heq : (∏ i, if X i = Y i then (1 : K) else 0) = antipodalTensor K D m x := by
    rw [Fintype.prod_boole]
    simp only [X, Y, Equiv.apply_eq_iff_eq, antipodalTensor, eq_comm]
  rw [← heq, ← h]
  apply Finset.sum_congr rfl
  intro o _
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- Section 4.4, including the actual fixed topologies, the finite term count,
antipodal placement and bit-cable cost. The hypothesis is exactly the balanced
border approximation (4.3) of each of the first sides. -/
theorem antipodal_border_networks_of_decomposition (B : SidePair D p m) (hB : IsAntipodalDecomposition B)
    (hD : 441 ≤ D) (hp : (p : ℝ) ≤ 21/20 * Real.sqrt D)
    (hlarge : 100 ≤ (m : ℝ) * Real.sqrt D)
    (hrank : (r : ℝ) ≤ (2 : ℝ) ^ (1/50 * m * Real.sqrt D))
    (hA : ∀ o, fieldSide K B true o ∈
      imageClosure (balancedCutSums (Fin D ⊕ Fin (p)) (Fin (2^m)) K r)) :
    ∃ L : ℕ, 0 < L ∧ L ≤ 2 ^ (D + (D + p)) ∧
      ∃ N : Fin L → Network D (Fin D × Bool) (fun _ ↦ m),
        (∀ i, (N i).PlacedAt antipodalPosition) ∧
        (∀ i, (N i).cost ≤ 2 * D * m - m/500) ∧
        antipodalTensor K D m ∈ imageClosure
          (Set.range fun T : ∀ i, (N i).Tables K ↦ ∑ i, (N i).value (T i)) := by
  classical
  obtain ⟨g, hcost⟩ := exists_balancedPlacements hD hp hlarge hrank
  let e := (Fintype.equivFin (LayoutIndex D p)).symm
  let N (i : Fin (Fintype.card (LayoutIndex D p))) := g.net m r (e i)
  have h := split_contraction_mem_closure (fieldSide K B true)
    (fieldSide K B false) hA g
  rw [sidesContraction_fieldSide B hB] at h
  refine ⟨_, card_layoutIndex_pos (D := D) (p := p) (by omega), card_layoutIndex_le D p,
    N, fun _ _ ↦ rfl, fun i ↦ hcost (e i), imageClosure_mono ?_ h⟩
  rintro _ ⟨tab, rfl⟩
  refine ⟨fun i ↦ tab (e i), ?_⟩
  funext x
  simp only [Finset.sum_apply]
  exact e.sum_comp fun i ↦ (g.net m r i).value (tab i) x

/-- Choosing the dimension constant as on page 14 pays for the broadcast selector.
The resulting finite identity is exact over the same field as the approximations. -/
theorem paidIdentity_of_decomposition (hm : 0 < m) (B : SidePair D p m) (hB : IsAntipodalDecomposition B)
    (hD : 441 ≤ D) (hp : (p : ℝ) ≤ 21/20 * Real.sqrt D)
    (hlarge : 100 ≤ (m : ℝ) * Real.sqrt D)
    (hrank : (r : ℝ) ≤ (2 : ℝ) ^ (1/50 * m * Real.sqrt D))
    (hA : ∀ o, fieldSide K B true o ∈
      imageClosure (balancedCutSums (Fin D ⊕ Fin (p)) (Fin (2^m)) K r))
    {c₀ : ℝ} (hc : 6 * c₀ ^ 2 < 1/500) (hdir : (D : ℝ) ≤ c₀ * Real.sqrt m) :
    ∃ t : ℕ, 0 < t ∧ Nonempty (PaidIdentity K D (t*m)) := by
  obtain ⟨L, hL, hcount, N, hplace, hcost, hclosure⟩ :=
    antipodal_border_networks_of_decomposition B hB hD hp hlarge hrank hA
  exact paidIdentity_of_border (by omega) hL N (fun T ↦ T) hclosure hplace hcost
    (strict_selector_budget hm hD hp hc hdir hcount hL le_rfl)

/-- Application to the manuscript’s mixed-radix encoding of the integral side tables. -/
theorem paidIdentity_of_balanced_sides (hm : 0 < m) (w : WireStates (leastEnergy m) (2 ^ m))
    (num : StateNumbering) (hD : 441 ≤ D) (hp : (bridgePorts m D : ℝ) ≤ 21/20 * Real.sqrt D)
    (hlarge : 100 ≤ (m : ℝ) * Real.sqrt D)
    (hrank : (r : ℝ) ≤ (2 : ℝ) ^ (1/50 * m * Real.sqrt D))
    (hA : ∀ o, scalarSide K w num D true o ∈
      imageClosure (balancedCutSums (Fin D ⊕ Fin (bridgePorts m D)) (Fin (2^m)) K r))
    {c₀ : ℝ} (hc : 6 * c₀ ^ 2 < 1/500) (hdir : (D : ℝ) ≤ c₀ * Real.sqrt m) :
    ∃ t : ℕ, 0 < t ∧ Nonempty (PaidIdentity K D (t*m)) :=
  paidIdentity_of_decomposition hm (fun left ↦ sideTable w num left D)
    (sideTable_identity hm w num D) hD hp hlarge hrank hA hc hdir

end Crossing

end BorderVNP
end Computability
end OAI
