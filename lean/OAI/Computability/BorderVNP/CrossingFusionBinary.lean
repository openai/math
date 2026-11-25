import OAI.Computability.BorderVNP.CrossingFusionTables
import OAI.Computability.BorderVNP.CrossingStateIndex
import OAI.Computability.VPVNP.LiveHeaderBits

/-!
# Binary fields for a uniformly checkable fused cut

Each mode and the final occupation rank get their own fixed-width binary
field. This costs at most two extra base-`2^m` ports when `D ≤ m`, and each
field bit can then be checked at a single fixed position on a bridge port.
The exact mixed-radix encoding is given in `CrossingFusionTables`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open VPVNP VPVNP.Crossing Filter
open scoped Topology

/-- The actual dynamic-programming numbering used in the checkable side tables. -/
def rankedStates : StateNumbering := fun E => (StateIndex.energyStateEquiv E).symm

/-- One bit position for a mode label or for the final occupation-state rank. -/
abbrev CutBit (d M s : ℕ) := (Fin d × Fin (Nat.clog 2 M)) ⊕ Fin (Nat.clog 2 s)

private theorem clog_lt (a : ℕ) (ha : 0 < a) :
    (Nat.clog 2 a : ℝ) < Real.logb 2 a + 1 := by
  rw [← Real.natCeil_logb_natCast]
  exact Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) (by exact_mod_cast ha))

/-- At the manuscript's direction count the field-wise padding requires at
most two extra bridge ports. -/
theorem binary_capacity {m d : ℕ} (hm : 0 < m) (hd : d ≤ m) :
    d * Nat.clog 2 (2*leastEnergy m) + Nat.clog 2 (stateCountAt (d*leastEnergy m)) ≤
      (bridgePorts m d + 2)*m := by
  let H := leastEnergy m
  have hH : 0 < H := (leastEnergy_spec m).1
  have h₁ := (clog_lt (2*H) (by omega)).le
  have h₂ := (clog_lt (stateCountAt (d*H)) (VPVNP.Crossing.cutoffCount_pos _)).le
  have h₃ := Nat.le_ceil (((d:ℝ)*Real.logb 2 (2*(H:ℝ))+Real.logb 2 (stateCountAt (d*H)))/m)
  have h₄ := (div_le_iff₀ (show (0:ℝ)<m by exact_mod_cast hm)).mp h₃
  change _ ≤ (bridgePorts m d : ℝ) * m at h₄
  push_cast at h₁
  have hdm : (d:ℝ) ≤ m := by exact_mod_cast hd
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  exact_mod_cast (show (d:ℝ)*(Nat.clog 2 (2*H):ℝ) + Nat.clog 2 (stateCountAt (d*H)) ≤
      (bridgePorts m d+2:ℝ)*m by nlinarith only [mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg d),
        h₂, h₄, hdm, hm1])

/-- Contiguous placement of the individual fields across the bridge ports. -/
def cutBitAddress {d M s p m : ℕ} (fits : d * Nat.clog 2 M + Nat.clog 2 s ≤ p*m) :
    CutBit d M s ↪ Fin p × Fin m :=
  ((((finProdFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv).toEmbedding).trans
    (Fin.castLEEmb fits)).trans finProdFinEquiv.symm.toEmbedding

/-- The bit selected by a field coordinate in the modes and the occupation rank. -/
def cutValueBit {d M s : ℕ} (v : (Fin d → Fin M) × Fin s) : CutBit d M s → Bool
  | .inl (i,b) => (v.1 i).val.testBit b.val
  | .inr b => v.2.val.testBit b.val

private theorem fin_testBits_injective (t : ℕ) :
    Function.Injective (fun a : Fin t => fun b : Fin (Nat.clog 2 t) => a.val.testBit b.val) := by
  intro i j hij
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < Nat.clog 2 t
  · exact congrFun hij ⟨b,hb⟩
  · have h := (Nat.le_pow_clog Nat.one_lt_two t).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hb))
    rw [Nat.testBit_eq_false_of_lt (i.isLt.trans_le h), Nat.testBit_eq_false_of_lt (j.isLt.trans_le h)]

private theorem cutValueBit_injective {d M s : ℕ} :
    Function.Injective (cutValueBit (d := d) (M := M) (s := s)) := by
  intro u v h
  apply Prod.ext
  · funext i
    apply fin_testBits_injective M
    exact funext (fun b => congrFun h (.inl (i,b)))
  · apply fin_testBits_injective s
    exact funext (fun b => congrFun h (.inr b))

/-- The bridge tuple seen by the two tensors, with zeroes at all unused bit
positions. The embedding is fixed before either tensor is evaluated. -/
noncomputable def binaryBridge {d M s p m : ℕ} (addr : CutBit d M s ↪ Fin p × Fin m)
    (v : (Fin d → Fin M) × Fin s) : Fin p → Fin (2^m) := fun a =>
  (RAMSerialization.wordBits m).symm (fun b => Function.extend addr (cutValueBit v) (fun _ => false) (a,b))

/-- Checking an occupied bridge position reads exactly its original bit. -/
theorem binaryBridge_bit {d M s p m : ℕ} (addr : CutBit d M s ↪ Fin p × Fin m)
    (v : (Fin d → Fin M) × Fin s) (b : CutBit d M s) :
    ((binaryBridge addr v (addr b).1).val).testBit (addr b).2.val = cutValueBit v b := by
  rw [LiveHeader.testBit_wordBits, binaryBridge, Equiv.apply_symm_apply, Prod.mk.eta]
  exact addr.injective.extend_apply _ _ _

/-- Bits outside the fields are zero and do not supply extra encodings. -/
theorem binaryBridge_unused {d M s p m : ℕ} (addr : CutBit d M s ↪ Fin p × Fin m)
    (v : (Fin d → Fin M) × Fin s) (a : Fin p × Fin m) (h : a ∉ Set.range addr) :
    ((binaryBridge addr v a.1).val).testBit a.2.val = false := by
  rw [LiveHeader.testBit_wordBits, binaryBridge, Equiv.apply_symm_apply, Prod.mk.eta]
  exact Function.extend_apply' _ _ _ h

/-- There is at most one internal mode sequence and occupation rank for a given bridge word. -/
theorem binaryBridge_injective {d M s p m : ℕ} (addr : CutBit d M s ↪ Fin p × Fin m) :
    Function.Injective (binaryBridge addr) := by
  intro u v huv
  apply cutValueBit_injective
  funext b
  rw [← binaryBridge_bit addr u b, ← binaryBridge_bit addr v b, huv]

/-- Sum of a product of two zero-padded tables along a common injective port encoding. -/
theorem sum_padded_tables {I J : Type*} [Fintype I] [Fintype J] (e : I ↪ J) (a b : I → ℤ) :
    (∑ j, Function.extend e a (fun _ => 0) j * Function.extend e b (fun _ => 0) j) =
      ∑ i, a i * b i := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)),
    Finset.sum_image e.injective.injOn]
  · simp only [e.injective.extend_apply]
  · intro j _ hj
    have h : ¬ ∃ i, e i = j := by simpa using hj
    simp only [Function.extend_apply' _ _ _ h, zero_mul]

/-- The side table with bit fields, expressed directly on the canonical state
numbering and padded by zero on unavailable bridge words. -/
noncomputable def binarySide {m d p : ℕ} (w : WireStates (leastEnergy m) (2^m))
    (addr : CutBit d (2*leastEnergy m) (stateCountAt (d*leastEnergy m)) ↪ Fin p × Fin m)
    (left : Bool) (b : Fin d → Bool) (x : Fin d → Fin (2^m)) (u : Fin p → Fin (2^m)) : ℤ :=
  Function.extend (binaryBridge addr) (fun v =>
    fusedSide (numberedStep w rankedStates) left d b x v.1 v.2) (fun _ => 0) u

/-- The cut tensor identity with the explicit state-ranking algorithm and binary fields. -/
theorem binarySide_identity {m d p : ℕ} (w : WireStates (leastEnergy m) (2^m))
    (addr : CutBit d (2*leastEnergy m) (stateCountAt (d*leastEnergy m)) ↪ Fin p × Fin m)
    (x y : Fin d → Fin (2^m)) :
    (∑ b, ∑ u, binarySide w addr true b (sideInputs b x y) u *
      binarySide w addr false b (sideInputs b y x) u) = ∏ i, if x i = y i then 1 else 0 := by
  have vacuum : stateCountAt (0 * leastEnergy m) = 1 := by
    simp [stateCountAt, cutoffCount, Lemmata.FockCircuits.partitionDimension_zero]
  rw [← fusedSides_identity vacuum (numberedStep w rankedStates)]
  apply Finset.sum_congr rfl
  intro b _
  let e := Function.Embedding.mk _ (binaryBridge_injective addr)
  change (∑ u, Function.extend e _ _ u * Function.extend e _ _ u) = _
  rw [sum_padded_tables, Fintype.sum_prod_type]

/-- Two extra ports still leave the displacement margin from §4.4 at every
sufficiently large width. -/
theorem binary_bridge_eventual {c₀ : ℝ} (hc : 0 < c₀) :
    ∀ᶠ m : ℕ in atTop, directions c₀ m ≤ m ∧
      ((bridgePorts m (directions c₀ m) + 2 : ℕ):ℝ) ≤ 21/20 * Real.sqrt (directions c₀ m) := by
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hd : Tendsto (directions c₀) atTop atTop := tendsto_nat_floor_atTop.comp (hs.const_mul_atTop hc)
  have hm : ∀ᶠ m : ℕ in atTop, directions c₀ m ≤ m := by
    filter_upwards [hs.eventually_ge_atTop c₀] with m h
    apply (Nat.cast_le (α := ℝ)).mp
    calc
      (directions c₀ m:ℝ) ≤ c₀ * Real.sqrt m := Nat.floor_le (mul_nonneg hc.le (Real.sqrt_nonneg _))
      _ ≤ _ := by simpa only [Function.comp_apply, Real.mul_self_sqrt (Nat.cast_nonneg m)] using
        mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg (m:ℝ))
  have htwo : Tendsto (fun m : ℕ => (2:ℝ) / Real.sqrt (directions c₀ m)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_iff (R := ℝ)).mpr hd))
  have h := (bridgePorts_limit hd hm).add htwo
  rw [add_zero] at h
  filter_upwards [hm, h.eventually_lt_const (by norm_num : (1:ℝ)<21/20), hd.eventually_gt_atTop 0]
    with m hdm hlim hdpos
  rw [← add_div] at hlim
  refine ⟨hdm, ?_⟩
  push_cast
  exact ((div_lt_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hdpos))).mp hlim).le

end Crossing

end BorderVNP
end Computability
end OAI
