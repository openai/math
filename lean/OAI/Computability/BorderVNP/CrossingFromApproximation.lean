import OAI.Computability.BorderVNP.CrossingBinaryBorderNetwork
import OAI.Computability.BorderVNP.CrossingInputFit
import OAI.Computability.BorderVNP.CrossingSplitProjection

/-!
# From an exceptional border approximation to a fixed shortening

All wire-width, dimension, group and rank estimates hold simultaneously from
one absolute length threshold. At any such length where the fused signed
programs are projections of the universal polynomial, a circuit meeting
(4.2) supplies a fixed paid antipodal identity.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing
universe u

open Filter MvPolynomial VPVNP

/-- The two-padded-port encoding of the side programs, specialized by honest
variable-or-scalar projections of the signed universal source. -/
def HasBinarySideProjections (K : Type*) [Field K] (n m D : ℕ) : Prop :=
  let p := bridgePorts m D + 2
  ∃ (w : WireStates (leastEnergy m) (2^m))
      (addr : CutBit D (2*leastEnergy m) (stateCountAt (D*leastEnergy m)) ↪ Fin p × Fin m),
    ∀ o : Fin D → Bool, ∃ φ : Projection K (Fin n × Bool) ((Fin D ⊕ Fin p) × Fin (2^m)),
      φ.hom (map (Int.castRingHom K) (Pstar n)) = sidePolynomial (fieldSide K (binarySide w addr) true o)

private theorem alphabet_le_source {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) {n : ℕ} (hn : 0 < n) :
    2 ^ width c n ≤ n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hn'
  have hm : (width c n : ℝ) ≤ Real.logb 2 n :=
    (Nat.floor_le (mul_nonneg hc.le hl)).trans (mul_le_of_le_one_left hl hc1)
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hm
  rw [Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hn)] at hp
  exact_mod_cast hp

private theorem group_count_le_alphabet {D p m : ℕ} (hD : 441 ≤ D) (hdm : D ≤ m)
    (hp : (p : ℝ) ≤ 21/20 * Real.sqrt D) : D + p ≤ 2^m := by
  have hr : 21 ≤ Real.sqrt D := Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast hD)
  have hpr : (p : ℝ) ≤ D := by
    nlinarith only [hp, mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg (D:ℝ)),
      Real.mul_self_sqrt (Nat.cast_nonneg D), Real.sqrt_nonneg (D:ℝ)]
  have hpd : p ≤ D := by exact_mod_cast hpr
  have hm : 2 * m ≤ 2^m := by
    cases m with
    | zero => norm_num
    | succ k => rw [pow_succ]; have h := Nat.lt_two_pow_self (n := k); omega
  omega

/-- Numerical estimates needed for the placement, valid at every sufficiently large
input length and with the same bounds for all orientations and scalar fields. -/
theorem eventual_layout_dimensions {c₀ c₁ : ℝ} (h₀ : 0 < c₀) (h₁ : 0 < c₁) (hc₁ : c₁ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, let m := width c₁ n
      let D := directions c₀ m
      let p := bridgePorts m D + 2
      0 < m ∧ 441 ≤ D ∧ D ≤ m ∧ (p : ℝ) ≤ 21/20 * Real.sqrt D ∧
        100 ≤ (m : ℝ) * Real.sqrt D ∧ D + p ≤ n ∧ 2^m ≤ n := by
  have hm := tendsto_width h₁
  have hroot := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hd : Tendsto (directions c₀) atTop atTop :=
    tendsto_nat_floor_atTop.comp (hroot.const_mul_atTop h₀)
  filter_upwards [hm.eventually (binary_bridge_eventual h₀),
    (hd.comp hm).eventually_ge_atTop 441, hm.eventually_ge_atTop 100,
    eventually_gt_atTop (0 : ℕ)] with n hcap hD hm' hn
  let m := width c₁ n
  let D := directions c₀ m
  let p := bridgePorts m D + 2
  change D ≤ m ∧ (p : ℝ) ≤ 21/20 * Real.sqrt D at hcap
  change 441 ≤ D at hD
  change 100 ≤ m at hm'
  have hq := alphabet_le_source h₁ hc₁ hn
  refine ⟨by omega, hD, hcap.1, hcap.2, ?_, (group_count_le_alphabet hD hcap.1 hcap.2).trans hq, hq⟩
  have hrootD : 1 ≤ Real.sqrt D := Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast (show 1 ≤ D by omega))
  exact (show (100:ℝ) ≤ m by exact_mod_cast hm').trans (le_mul_of_one_le_right (Nat.cast_nonneg m) hrootD)

/-- Applying degree-component approximation, (4.3), the actual rank-bounded networks
and their selector charge at the same length. In particular, all three parameters
`m,D,t` of the resulting fixed shortening are positive and `D≥2`. -/
theorem eventually_paidIdentity_of_small_approximation {c₀ c₁ : ℝ}
    (h₀ : 0 < c₀) (h₁ : 0 < c₁) (hc₁ : c₁ ≤ 1) (hc₀ : 6 * c₀ ^ 2 < 1/500) :
    ∀ᶠ n : ℕ in atTop, let m := width c₁ n
      let D := directions c₀ m
      ∀ (K : Type u) [Field K], HasBinarySideProjections K n m D → ∀ s : ℕ,
        (s : ℝ) ≤ (2 : ℝ) ^ (1/100 * (m * Real.sqrt D)) →
        geometricApprox n s (map (Int.castRingHom K) (Pstar n)) →
        2 ≤ D ∧ ∃ t : ℕ, 0 < t*m ∧ Nonempty (PaidIdentity K D (t*m)) := by
  filter_upwards [eventual_layout_dimensions h₀ h₁ hc₁, eventually_splitWidth_le h₀ h₁] with n hg hr
  let m := width c₁ n
  let D := directions c₀ m
  let p := bridgePorts m D + 2
  obtain ⟨hm, hD, _, hp, hlarge, hℓ, hq⟩ := hg
  change 441 ≤ D at hD
  change (p : ℝ) ≤ 21/20 * Real.sqrt D at hp
  change ∀ (K : Type u) [Field K], HasBinarySideProjections K n m D → ∀ s : ℕ,
    (s : ℝ) ≤ (2 : ℝ) ^ (1/100 * (m * Real.sqrt D)) →
    geometricApprox n s (map (Int.castRingHom K) (Pstar n)) →
    2 ≤ D ∧ ∃ t : ℕ, 0 < t*m ∧ Nonempty (PaidIdentity K D (t*m))
  intro K _ hprojection s hs happrox
  obtain ⟨w, addr, hproj⟩ := hprojection
  let r := splitWidth n (D+p) (2^m) s
  have hR : (r : ℝ) ≤ (2:ℝ)^(1/50 * m * Real.sqrt D) := by
    have h := hr (D+p) (2^m) s hℓ hq (show (s : ℝ) ≤ (2:ℝ)^((m * Real.sqrt D)/100) by
      convert hs using 2; ring)
    convert h using 2; ring
  have hA (o : Fin D → Bool) : fieldSide K (binarySide w addr) true o ∈
      imageClosure (balancedCutSums (Fin D ⊕ Fin p) (Fin (2^m)) K r) := by
    obtain ⟨φ, hφ⟩ := hproj o
    have hcard : 3 ≤ Fintype.card (Fin D ⊕ Fin p) := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    simpa only [r, Fintype.card_sum, Fintype.card_fin] using
      Pstar_projection_balancedCutSums _ φ hφ hcard happrox
  have hdir : (D : ℝ) ≤ c₀ * Real.sqrt m :=
    Nat.floor_le (mul_nonneg h₀.le (Real.sqrt_nonneg _))
  obtain ⟨t, ht, he⟩ := paidIdentity_of_binary_sides hm w addr hD hp hlarge hR hA hc₀ hdir
  exact ⟨by omega, t, Nat.mul_pos ht hm, he⟩

end Crossing

end BorderVNP
end Computability
end OAI
