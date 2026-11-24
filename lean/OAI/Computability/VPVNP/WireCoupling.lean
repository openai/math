import OAI.Computability.VPVNP.CouplingAmplification
import OAI.Computability.VPVNP.RealizedTransport
import OAI.Computability.VPVNP.TwoMarkedSplitBounds

/-!
# Coupling the endpoint choices of two spectral wire intervals

The recursive split in Appendix A.3 keeps the two marked legs open at every
node. Dividing by the product of the ancestor diagonal-wire values gives a
subadditive binary tree, whose endpoint values obey the shrinking cost tables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor.SpectralPoint

open SpectralGeometry

variable {k J : Type*} [Field k] [Fintype J] (F : SpectralPoint k J)

/-- The four pairwise distances between the endpoint choices. -/
noncomputable def wireEndpointTable (A B : Bool → J) : EndpointTable :=
  fun i j => F.wireDistance (A i) (B j)

theorem wireEndpointTable_gap (A B : Bool → J) (j : Bool) :
    |columnGap (F.wireEndpointTable A B) j| ≤ F.wireDistance (A false) (A true) := by
  apply abs_le.mpr
  change -F.wireDistance (A false) (A true) ≤
      F.wireDistance (A false) (B j) - F.wireDistance (A true) (B j) ∧
      F.wireDistance (A false) (B j) - F.wireDistance (A true) (B j) ≤
      F.wireDistance (A false) (A true)
  have h₀ := F.wireDistance_triangle (A true) (A false) (B j)
  rw [F.wireDistance_comm (A true) (A false)] at h₀
  have h₁ := F.wireDistance_triangle (A false) (A true) (B j)
  constructor <;> linarith

private theorem endpoint_cost_eq_of_zero {u v : ℝ} (A B : Bool → J)
    (ht : F.wireDistance (A false) (A true) = 0) (ρ π : EndpointCoupling u v) :
    ρ.cost (F.wireEndpointTable A B) = π.cost (F.wireEndpointTable A B) := by
  have hgap (j) : columnGap (F.wireEndpointTable A B) j = 0 :=
    abs_nonpos_iff.mp (ht ▸ F.wireEndpointTable_gap A B j)
  apply sub_eq_zero.mp
  simp only [coupling_cost_sub, hgap, sub_self, mul_zero]

/-- The two-mark tensor at a path in the exterior split tree. Each level is
chosen from the endpoint table *before* the new branch is taken. -/
private noncomputable def couplingNode (q : ℕ) (t : ℝ) (A : Bool → J) (M : EndpointTable)
    (p : List Bool) : TwoMarkedNode k J (Fin q) (Fin q) :=
  p.reverseRecOn (TwoMarkedNode.wire q) fun pre branch W =>
    W.exteriorChild (A false) (A true) (couplingLevel q t (leafTable M pre)) branch

/-- Product of the values of the exterior-level wires along the ancestry. -/
private noncomputable def ancestry (q : ℕ) (t : ℝ) (M : EndpointTable) (p : List Bool) : ℝ :=
  p.reverseRecOn 1 fun pre _ D => D * (q.choose (couplingLevel q t (leafTable M pre)) : ℝ) ^ t

private theorem ancestry_pos {q : ℕ} (hq : 2 ≤ q) {t : ℝ} (ht : 0 < t)
    {M : EndpointTable} (hgap : ∀ j, |columnGap M j| ≤ t) (p : List Bool) :
    0 < ancestry q t M p := by
  induction p using List.reverseRecOn with
  | nil => simp [ancestry]
  | append_singleton p b ih =>
    have hlev := couplingLevel_bounds hq ht (leafTable_columnGap_mem M p hgap)
    have hn := Nat.choose_pos hlev.2.1.le
    simpa only [ancestry, List.reverseRecOn_concat] using mul_pos ih
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) t)

private theorem level_wire_value (A : Bool → J) {q b : ℕ} (hb : b ≤ q) :
    (F.value (WireTensor.wire (A false) (A true) (ExteriorLevels.Level q b)) : ℝ) =
    (q.choose b : ℝ) ^ F.wireDistance (A false) (A true) := by
  rw [F.value_wire_equiv _ _ (Fintype.equivFin _), ExteriorLevels.card_level]
  exact F.value_wire_eq_rpow _ _ (Nat.choose_pos hb)

private theorem normalized_same {x y D H : ℝ} (hD : 0 < D) (hH : 0 < H)
    (h : x ≤ H*y) : x / (D*H) ≤ y/D := by
  apply (div_le_div_iff₀ (mul_pos hD hH) hD).2
  simpa only [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_right h hD.le

private theorem normalized_cross {x y D H C t : ℝ} (hD : 0 < D) (hH : 0 < H) (hC : 0 ≤ C)
    (h : x ≤ C ^ t * y) : x / (D * H ^ t) ≤ (C/H) ^ t * (y/D) := by
  have ht := Real.rpow_pos_of_pos hH t
  rw [Real.div_rpow hC hH.le, div_mul_div_comm, mul_comm (H ^ t) D]
  exact div_le_div_of_nonneg_right h (mul_pos hD ht).le

private theorem normalized_split {x y z D H : ℝ} (hD : 0 < D) (hH : 0 < H)
    (h : x*H ≤ y+z) : x/D ≤ y/(D*H) + z/(D*H) := by
  rw [← add_div, div_le_div_iff₀ hD (mul_pos hD hH)]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_right h hD.le

private theorem coupling_wire_power_bound {q : ℕ} (hq : 2 ≤ q)
    (A B : Bool → J) (c x : J) {u v : ℝ} (ρ π : EndpointCoupling u v)
    (ht : 0 < F.wireDistance (A false) (A true))
    (independent : ∀ W : TwoMarkedNode k J (Fin q) (Fin q), (F.value (W.place c x) : ℝ) ≤
      ∏ i, ∏ j, (F.value (W.place (A i) (B j)) : ℝ) ^ ρ.mass i j)
    (a : ℕ) :
    (q : ℝ) ^ F.wireDistance c x ≤ (2 : ℝ) ^ a *
      (q : ℝ) ^ (π.cost (F.wireEndpointTable A B) + 2 * F.wireDistance (A false) (A true) * (1/2)^a) := by
  let t := F.wireDistance (A false) (A true)
  let M := F.wireEndpointTable A B
  let W (p : List Bool) := couplingNode (k := k) q t A M p
  let D (p : List Bool) := ancestry q t M p
  let b (p : List Bool) := couplingLevel q t (leafTable M p)
  let H (p : List Bool) := (q.choose (b p) : ℝ) ^ t
  let V (p : List Bool) (i j : J) := (F.value ((W p).place i j) : ℝ) / D p
  have hgap : ∀ j, |columnGap M j| ≤ t := F.wireEndpointTable_gap A B
  have hD (p) : 0 < D p := ancestry_pos hq ht hgap p
  have hb (p) : 1 ≤ b p ∧ b p < q := by
    obtain ⟨h₁, h₂, _⟩ := couplingLevel_bounds hq ht (leafTable_columnGap_mem M p hgap)
    exact ⟨h₁, h₂⟩
  have hdim (p) : 0 < (q.choose (b p) : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (hb p).2.le)
  have hH (p) : 0 < H p := Real.rpow_pos_of_pos (hdim p) t
  have hV (p : List Bool) (s : Bool) (i j : J) : V (p ++ [s]) i j =
      (F.value (((W p).exteriorChild (A false) (A true) (b p) s).place i j) : ℝ) / (D p * H p) := by
    simp only [V, W, D, H, b, couplingNode, ancestry, List.reverseRecOn_concat]
  have hroot (i j : J) : V [] i j = (q : ℝ) ^ F.wireDistance i j := by
    simp only [V, W, D, couplingNode, ancestry, List.reverseRecOn_nil, div_one, TwoMarkedNode.value_wire]
    exact F.value_wire_eq_rpow _ _ (by omega)
  have hend := endpoint_tree_bounds hq ht a M hgap (fun p i j => V p (A i) (B j))
    (fun p i j => div_nonneg (NNReal.coe_nonneg _) (hD p).le) (fun i j => (hroot (A i) (B j)).le)
    (fun p _ s i j => by
      rw [hV]
      exact normalized_same (hD p) (hH p) ((W p).value_exteriorChild_same_le F A B (b p) (hb p).2 s i j))
    (fun p _ j => by
      rw [hV]
      exact normalized_cross (hD p) (hdim p) (Nat.cast_nonneg _)
        ((W p).value_exteriorChild_plus_le F A B (b p) (hb p).2 j))
    (fun p _ j => by
      rw [hV]
      exact normalized_cross (hD p) (hdim p) (Nat.cast_nonneg _)
        ((W p).value_exteriorChild_minus_le F A B (b p) (hb p).2 j))
  rw [← hroot c x]
  apply coupling_tree_bound ρ π M hgap (by exact_mod_cast (show 1 ≤ q by omega)) a (fun p => V p c x)
  · intro p _
    rw [hV, hV]
    apply normalized_split (hD p) (hH p)
    have h := TwoMarkedNode.value_exterior_split F (W p) (A false) (A true) c x (b p)
    have h' := NNReal.coe_le_coe.mpr h
    rw [NNReal.coe_mul, NNReal.coe_add, F.level_wire_value A (hb p).2.le] at h'
    exact h'
  · intro p hp
    exact normalized_endpoint_product_bound ρ (by exact_mod_cast (show 0 < q by omega)) (hD p)
      (fun _ _ => NNReal.coe_nonneg _) (independent (W p)) (hend p hp.le)

/-- The two-mark independent product inequality implies the bound for every endpoint coupling. -/
theorem wireDistance_endpointCoupling_of_product_bound (A B : Bool → J) (c x : J)
    {u v : ℝ} (ρ π : EndpointCoupling u v)
    (independent : ∀ q : ℕ, 2 ≤ q → ∀ W : TwoMarkedNode k J (Fin q) (Fin q),
      (F.value (W.place c x) : ℝ) ≤
      ∏ i, ∏ j, (F.value (W.place (A i) (B j)) : ℝ) ^ ρ.mass i j) :
    F.wireDistance c x ≤ π.cost (F.wireEndpointTable A B) := by
  rcases (F.wireDistance_nonneg (A false) (A true)).eq_or_lt with hzero | ht
  · have val (i j : J) : (F.value ((TwoMarkedNode.wire 2).place i j) : ℝ) = (2 : ℝ) ^ F.wireDistance i j := by
      rw [TwoMarkedNode.value_wire]
      exact F.value_wire_eq_rpow _ _ (by decide : 0 < 2)
    have h := normalized_endpoint_product_bound (N := F.wireEndpointTable A B) (D := 1)
      ρ (by norm_num : (0 : ℝ) < 2) (by norm_num) (fun _ _ => NNReal.coe_nonneg _)
      (independent 2 (by decide) (TwoMarkedNode.wire 2))
      (fun i j => by simp only [div_one, val, wireEndpointTable]; rfl)
    rw [div_one, val, F.endpoint_cost_eq_of_zero A B hzero.symm ρ π] at h
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).1 h
  · apply le_of_dyadic_amplification
    intro a n hn
    have hq : 2 ≤ (2:ℕ)^n := (le_refl 2).trans
      (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      F.coupling_wire_power_bound hq A B c x ρ π ht (independent _ hq) a

/-- Equation (A.3). Every coupling of the endpoint choices bounds the
distance between the two fractional points. -/
theorem wireDistance_endpointCoupling (A B : Bool → J) (c x : J) {u v : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1)
    (hc : @WireGeometry.AtFraction J F.wirePseudoMetric (A false) (A true) u c)
    (hx : @WireGeometry.AtFraction J F.wirePseudoMetric (B false) (B true) v x)
    (π : EndpointCoupling u v) :
    F.wireDistance c x ≤ π.cost (F.wireEndpointTable A B) := by
  apply F.wireDistance_endpointCoupling_of_product_bound A B c x (independentCoupling hu hv) π
  intro q _ W
  exact F.value_twoMarked_atFraction_le W.Basis (Fin q) (Fin q) W.coeff A B c x hu hv hc hx

/-- Pair the first endpoints and the second endpoints with equal interval parameter. -/
private def diagonalCoupling {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) : EndpointCoupling u u where
  mass i j := if i = j then (if i then u else 1-u) else 0
  nonneg i j := by cases i <;> cases j <;> simp [hu.1, hu.2]
  row₀ := by simp
  row₁ := by simp
  col₀ := by simp
  col₁ := by simp

/-- Lemma 2.2. Interpolating at the same fraction on two wire intervals
bounds the distance by the correspondingly weighted endpoint distances. -/
theorem fractionTransport :
    @WireGeometry.FractionTransport J F.wirePseudoMetric := by
  intro a b c d x y t ht₀ ht₁ hx hy
  let A (i : Bool) := if i then b else a
  let B (i : Bool) := if i then d else c
  have ht := And.intro ht₀ ht₁
  have e := F.wireDistance_endpointCoupling A B x y ht ht hx hy (diagonalCoupling ht)
  change F.wireDistance x y ≤ (1-t) * F.wireDistance a c + t * F.wireDistance b d
  simpa only [EndpointCoupling.cost, wireEndpointTable, A, B, diagonalCoupling,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, zero_mul, add_zero] using e

end WireTensor.SpectralPoint

namespace WireGeometry

/-- The spectral transport inequality passes to every jointly realizable
finite configuration by cancellation of the realization's positive scale. -/
theorem realizable_fractionTransport {k X : Type*} [Field k] [PseudoMetricSpace X]
    (hX : RealizableConfigurations k X) : FractionTransport X :=
  fractionTransport_of_realizable (fun _ _ _ F => F.fractionTransport) hX

end WireGeometry

end VPVNP
end Computability
end OAI
