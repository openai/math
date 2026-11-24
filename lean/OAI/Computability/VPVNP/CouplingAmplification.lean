import OAI.Computability.VPVNP.ExteriorLevelRates
import OAI.Computability.VPVNP.SpectralGeometry

/-!
# Amplification of the endpoint-coupling estimate

Appendix A.3 of *VP and VNP differ over every field* bounds a wire value by a
binary tree of exterior decompositions. The finite exterior level estimate
controls each child's table with no asymptotic error. After summing the leaves,
the wire dimension tends to infinity at fixed depth, and then the depth tends
to infinity.
-/

namespace OAI
namespace Computability
namespace VPVNP

open Filter
open scoped Topology

namespace SpectralGeometry

/-- Exterior level used for a split with wire length `t` and current endpoint exponents `N`. -/
noncomputable def couplingLevel (q : ℕ) (t : ℝ) (N : EndpointTable) : ℕ :=
  ExteriorLevelRates.level q ((q : ℝ) ^ (gapMidpoint N / t))

/-- At the chosen level both normalized crossing factors obey their target bounds for
each finite wire dimension `q ≥ 2`. -/
theorem couplingLevel_bounds {q : ℕ} (hq : 2 ≤ q) {t : ℝ} (ht : 0 < t)
    {N : EndpointTable} (hgap : ∀ j, |columnGap N j| ≤ t) :
    let b := couplingLevel q t N
    1 ≤ b ∧ b < q ∧
      ((q.choose (b + 1) : ℝ) / q.choose b) ^ t ≤ (q : ℝ) ^ gapMidpoint N ∧
      ((q.choose (b - 1) : ℝ) / q.choose b) ^ t ≤ (q : ℝ) ^ (-gapMidpoint N) := by
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hq₀ := zero_le_one.trans hq₁
  have hmid : -t ≤ gapMidpoint N ∧ gapMidpoint N ≤ t := by
    obtain ⟨h₀, h₁⟩ := abs_le.mp (hgap false)
    obtain ⟨h₂, h₃⟩ := abs_le.mp (hgap true)
    unfold gapMidpoint
    constructor <;> linarith
  have hlo := Real.rpow_le_rpow_of_exponent_le hq₁
    ((le_div_iff₀ ht).2 (by simpa only [neg_one_mul] using hmid.1) :
      (-1 : ℝ) ≤ gapMidpoint N / t)
  have hhi := Real.rpow_le_rpow_of_exponent_le hq₁
    ((div_le_iff₀ ht).2 (by simpa only [one_mul] using hmid.2) : gapMidpoint N / t ≤ 1)
  rw [Real.rpow_neg hq₀, Real.rpow_one, ← one_div] at hlo
  rw [Real.rpow_one] at hhi
  obtain ⟨hb, hbq, hu, hd⟩ := ExteriorLevelRates.level_bounds hq hlo hhi
  refine ⟨hb, hbq, ?_, ?_⟩
  · have h := Real.rpow_le_rpow (by positivity) hu.2 ht.le
    rwa [← Real.rpow_mul hq₀, div_mul_cancel₀ _ ht.ne'] at h
  · rw [← Real.rpow_neg hq₀] at hd
    have h := Real.rpow_le_rpow (by positivity) hd.2 ht.le
    rwa [← Real.rpow_mul hq₀, neg_mul, div_mul_cancel₀ _ ht.ne'] at h

/-- The normalized endpoint bounds at both children of an Appendix A.3 split. -/
theorem split_endpoint_bounds {q : ℕ} (hq : 2 ≤ q) {t : ℝ} (ht : 0 < t)
    {N F : EndpointTable} (hgap : ∀ j, |columnGap N j| ≤ t)
    (hF₀ : ∀ i j, 0 ≤ F i j) (hF : ∀ i j, F i j ≤ (q : ℝ) ^ N i j)
    {G : Bool → EndpointTable} (hG : ∀ branch i j, G branch i j ≤ F i j)
    (hplus : ∀ j, G true false j ≤
      ((q.choose (couplingLevel q t N + 1) : ℝ) / q.choose (couplingLevel q t N)) ^ t * F true j)
    (hminus : ∀ j, G false true j ≤
      ((q.choose (couplingLevel q t N - 1) : ℝ) / q.choose (couplingLevel q t N)) ^ t * F false j)
    (branch i j : Bool) : G branch i j ≤ (q : ℝ) ^ splitTable N branch i j := by
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hq₀ := zero_lt_one.trans_le hq₁
  have hm : Monotone (fun r : ℝ ↦ (q : ℝ) ^ r) :=
    fun _ _ h ↦ Real.rpow_le_rpow_of_exponent_le hq₁ h
  obtain ⟨_, _, hup, hdown⟩ := couplingLevel_bounds hq ht hgap
  have hsame := (hG branch i j).trans (hF i j)
  cases branch <;> cases i
  · exact hsame
  · change G false true j ≤ (q : ℝ) ^ min (N true j) (N false j - gapMidpoint N)
    rw [hm.map_min]
    refine le_min hsame ?_
    rw [sub_eq_add_neg, Real.rpow_add hq₀, mul_comm]
    exact (hminus j).trans (mul_le_mul hdown (hF false j) (hF₀ false j) (by positivity))
  · change G true false j ≤ (q : ℝ) ^ min (N false j) (N true j + gapMidpoint N)
    rw [hm.map_min]
    refine le_min hsame ?_
    rw [Real.rpow_add hq₀, mul_comm]
    exact (hplus j).trans (mul_le_mul hup (hF true j) (hF₀ true j) (by positivity))
  · exact hsame

/-- The cost table at an appended child agrees with one more split of the current table. -/
theorem leafTable_append_child (M : EndpointTable) (p : List Bool) (b : Bool) :
    leafTable M (p ++ [b]) = splitTable (leafTable M p) b := by
  induction p generalizing M with
  | nil => rfl
  | cons c p ih => exact ih (splitTable M c)

/-- Propagating normalized endpoint estimates from the root to any path of the given depth. -/
theorem endpoint_tree_bounds {q : ℕ} (hq : 2 ≤ q) {t : ℝ} (ht : 0 < t) (a : ℕ)
    (M : EndpointTable) (hgap : ∀ j, |columnGap M j| ≤ t) (F : List Bool → EndpointTable)
    (hF₀ : ∀ p i j, 0 ≤ F p i j) (hroot : ∀ i j, F [] i j ≤ (q : ℝ) ^ M i j)
    (hsame : ∀ p : List Bool, p.length < a → ∀ b i j, F (p ++ [b]) i j ≤ F p i j)
    (hplus : ∀ p : List Bool, p.length < a → ∀ j,
      let b := couplingLevel q t (leafTable M p)
      F (p ++ [true]) false j ≤ ((q.choose (b + 1) : ℝ) / q.choose b) ^ t * F p true j)
    (hminus : ∀ p : List Bool, p.length < a → ∀ j,
      let b := couplingLevel q t (leafTable M p)
      F (p ++ [false]) true j ≤ ((q.choose (b - 1) : ℝ) / q.choose b) ^ t * F p false j) :
    ∀ p : List Bool, p.length ≤ a → ∀ i j, F p i j ≤ (q : ℝ) ^ leafTable M p i j := by
  intro p
  induction p using List.reverseRecOn with
  | nil => exact fun _ ↦ hroot
  | append_singleton p b ih =>
    intro hp i j
    have hp' : p.length < a := by simpa using hp
    rw [leafTable_append_child]
    exact split_endpoint_bounds hq ht (leafTable_columnGap_mem M p hgap) (hF₀ p) (ih hp'.le)
      (G := fun b ↦ F (p ++ [b])) (hsame p hp') (hplus p hp') (hminus p hp') b i j

/-- The independent endpoint estimate (A.4) passes to normalized values because
its exponents sum to one. Applies to any coupling with these marginals. -/
theorem normalized_endpoint_product_bound {u v q D W : ℝ} (ρ : EndpointCoupling u v)
    {F N : EndpointTable} (hq : 0 < q) (hD : 0 < D) (hF₀ : ∀ i j, 0 ≤ F i j)
    (hW : W ≤ ∏ i, ∏ j, (F i j) ^ ρ.mass i j) (hF : ∀ i j, F i j / D ≤ q ^ N i j) :
    W / D ≤ q ^ ρ.cost N := by
  have hmass : (∑ i, ∑ j, ρ.mass i j) = 1 := by
    simp only [Fintype.sum_bool]
    linarith only [ρ.row₀, ρ.row₁]
  have hcost : (∑ i, ∑ j, N i j * ρ.mass i j) = ρ.cost N := by
    simp only [Fintype.sum_bool, EndpointCoupling.cost]; ring
  have hprod (x : ℝ) (hx : 0 < x) (p : EndpointTable) :
      (∏ i, ∏ j, x ^ p i j) = x ^ (∑ i, ∑ j, p i j) := by
    simp_rw [Real.rpow_sum_of_pos hx]
  calc W / D ≤ (∏ i, ∏ j, (F i j) ^ ρ.mass i j) / D := div_le_div_of_nonneg_right hW hD.le
       _ = ∏ i, ∏ j, (F i j / D) ^ ρ.mass i j := by
         simp_rw [Real.div_rpow (hF₀ _ _) hD.le, Finset.prod_div_distrib]
         rw [hprod D hD, hmass, Real.rpow_one]
       _ ≤ ∏ i, ∏ j, (q ^ N i j) ^ ρ.mass i j := by
         apply Finset.prod_le_prod₀
         · exact fun i _ ↦ Finset.prod_nonneg fun j _ ↦
             Real.rpow_nonneg (div_nonneg (hF₀ i j) hD.le) _
         · intro i _
           apply Finset.prod_le_prod₀
           · exact fun j _ ↦ Real.rpow_nonneg (div_nonneg (hF₀ i j) hD.le) _
           · exact fun j _ ↦ Real.rpow_le_rpow (div_nonneg (hF₀ i j) hD.le) (hF i j) (ρ.nonneg i j)
       _ = q ^ ρ.cost N := by
         simp_rw [← Real.rpow_mul hq.le]
         rw [hprod q hq, hcost]

/-- A depth-`a` tree with subadditive parent values and uniformly bounded leaf values. -/
private theorem binary_tree_bound (a : ℕ) (E : List Bool → ℝ) (B : ℝ)
    (hsplit : ∀ p : List Bool, p.length < a → E p ≤ E (p ++ [true]) + E (p ++ [false]))
    (hleaf : ∀ p : List Bool, p.length = a → E p ≤ B) : E [] ≤ (2 : ℝ) ^ a * B := by
  have descend (r : ℕ) (p : List Bool) (h : p.length + r = a) : E p ≤ (2 : ℝ) ^ r * B := by
    induction r generalizing p with
    | zero => simpa only [pow_zero, one_mul] using hleaf p (by omega)
    | succ r ih =>
      have hchild (b : Bool) : E (p ++ [b]) ≤ (2 : ℝ) ^ r * B :=
        ih _ (by simp only [List.length_append, List.length_singleton]; omega)
      calc E p ≤ E (p ++ [true]) + E (p ++ [false]) := hsplit p (by omega)
           _ ≤ (2 : ℝ) ^ r * B + 2 ^ r * B := add_le_add (hchild true) (hchild false)
           _ = (2 : ℝ) ^ (r + 1) * B := by rw [pow_succ]; ring
  exact descend a [] (by simp)

/-- The root is at most `2 ^ a` times the common coupling bound for the leaves. -/
theorem coupling_tree_bound {u v t q : ℝ} (ρ π : EndpointCoupling u v) (M : EndpointTable)
    (hgap : ∀ j, |columnGap M j| ≤ t) (hq : 1 ≤ q) (a : ℕ) (E : List Bool → ℝ)
    (hsplit : ∀ p : List Bool, p.length < a → E p ≤ E (p ++ [true]) + E (p ++ [false]))
    (hleaf : ∀ p : List Bool, p.length = a → E p ≤ q ^ ρ.cost (leafTable M p)) :
    E [] ≤ (2 : ℝ) ^ a * q ^ (π.cost M + 2 * t * (1 / 2) ^ a) := by
  apply binary_tree_bound a E _ hsplit
  intro p hp
  apply (hleaf p hp).trans (Real.rpow_le_rpow_of_exponent_le hq ?_)
  simpa only [hp] using coupling_leaf_bound ρ π M hgap p

/-- A fixed dyadic prefactor vanishes from the exponential rate as the power tends to infinity.
The remaining error tends to zero as the precision index increases. -/
theorem le_of_dyadic_amplification {d cost t : ℝ}
    (h : ∀ a n : ℕ, 1 ≤ n → ((2 : ℝ) ^ n) ^ d ≤
      (2 : ℝ) ^ a * ((2 : ℝ) ^ n) ^ (cost + 2 * t * (1 / 2) ^ a)) :
    d ≤ cost := by
  let rate (a : ℕ) := cost + 2 * t * (1 / 2 : ℝ) ^ a
  have hfixed (a : ℕ) : d ≤ rate a := by
    have hlim : Tendsto (fun n : ℕ ↦ (a : ℝ) / n + rate a) atTop (𝓝 (rate a)) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (a : ℝ)).add_const (rate a)
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from hn)
    have hpow : ((2 : ℝ) ^ n) ^ d ≤ (2 : ℝ) ^ a * ((2 : ℝ) ^ n) ^ rate a := h a n hn
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast 2 a,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_le_rpow_left_iff (by norm_num)] at hpow
    apply (mul_le_mul_iff_right₀ hn_pos).mp
    rw [mul_add, mul_comm _ (_ / _), div_mul_cancel₀ _ hn_pos.ne']
    exact hpow
  have hlim : Tendsto rate atTop (𝓝 cost) := by
    have hhalf := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    simpa [rate] using (hhalf.const_mul (2 * t)).const_add cost
  exact ge_of_tendsto' hlim hfixed

end SpectralGeometry

end VPVNP
end Computability
end OAI
