import OAI.LinearAlgebra.FiniteFourier.PrimeWindowRepair
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Choosing finite parameters for the prime tensor kernel

The label length is fixed before fixing the alphabet. With alphabet size
`q = 2^b`, take `m = ℓ * q^(L - L/ℓ) + 1`. This guarantees the required
congruence and bounds the charged-rectangle cost per label. Choosing
`L` to be an even multiple of `ℓ` makes the square-root exponent integral.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter
open scoped Topology

private theorem exists_bit_width (L : ℕ) (M : ℝ) :
    ∃ b : ℕ, 1 ≤ b ∧ M ≤ (2 : ℝ)^b ∧ (1 + b)^L ≤ 2^b := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt L (by norm_num : (1 : ℝ) < 2)
  have hpow := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  obtain ⟨b, hb, hM, hL⟩ := ((eventually_ge_atTop 1).and
    ((hpow.eventually_ge_atTop M).and (hlim.eventually_lt_const
      (by positivity : (0 : ℝ) < 1 / 2^L)))).exists
  refine ⟨b, hb, hM, ?_⟩
  have hbr : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hl' : (b : ℝ)^L * 2^L < 2^b := by
    exact (div_lt_div_iff₀ (by positivity) (by positivity)).mp hL |>.trans_eq (one_mul _)
  have ht : (1+(b:ℝ))^L ≤ (2:ℝ)^b := calc
    (1+(b:ℝ))^L ≤ (b * 2 : ℝ)^L := pow_le_pow_left₀ (by positivity) (by linarith) _
    _ ≤ _ := by rw [mul_pow]; exact hl'.le
  exact_mod_cast ht

private theorem cost_exponents {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {θ : ℝ} (hθ : 1/2 < θ) :
    ∃ L v : ℕ, ℓ ≤ L ∧ L - L / ℓ = 2*v ∧
      ((v + 3*(ℓ-1) + 14 : ℕ) : ℝ) < ((2*v : ℕ) : ℝ) * θ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (((3*(ℓ-1) + 14 : ℕ) : ℝ) / (2*θ - 1))
  have hpos : 0 < 2*θ - 1 := by linarith
  have hh := (div_lt_iff₀ hpos).mp hn
  have hn' : 0 < n := by
    by_contra! he
    simp [Nat.eq_zero_of_le_zero he] at hh
    linarith [Nat.cast_nonneg (α := ℝ) (ℓ-1)]
  let v := (ℓ-1)*n
  have hv : n ≤ v := Nat.le_mul_of_pos_left _ (by omega)
  have hreal : (n : ℝ) ≤ v := by exact_mod_cast hv
  refine ⟨(2*n)*ℓ, v, Nat.le_mul_of_pos_left _ (by positivity), ?_, ?_⟩
  · rw [Nat.mul_div_cancel _ (by omega : 0 < ℓ)]
    have he : ℓ = (ℓ-1)+1 := by omega
    conv_lhs => lhs; rhs; rw [he]
    rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
    dsimp [v]
    ac_rfl
  · push_cast at hh ⊢
    nlinarith only [hh, mul_le_mul_of_nonneg_right hreal hpos.le]

private theorem stage_bound {ℓ m q v : ℕ} (hℓ : 2 ≤ ℓ) (hm : 2 ≤ m)
    (hq : 10 ≤ q) (hℓq : ℓ+2 ≤ q) (hvq : 2*v+2 ≤ q)
    (hmq : m = ℓ*q^(2*v)+1) :
    ((ℓ : ℝ)+2) * countPencilOrder ℓ m ≤ (q : ℝ)^(v+7) := by
  let Q : ℝ := q
  have hQ : 10 ≤ Q := by dsimp [Q]; exact_mod_cast hq
  have hQ₁ : 1 ≤ Q := by linarith
  have hQ₀ : 0 < Q := by linarith
  have hℓQ : (ℓ : ℝ) + 2 ≤ Q := by dsimp [Q]; exact_mod_cast hℓq
  have hQpow : 1 ≤ Q^(2*v) := one_le_pow₀ hQ₁
  have hmeq : (m : ℝ) = ℓ * Q^(2*v) + 1 := by dsimp [Q]; exact_mod_cast hmq
  have hml : (m : ℝ) ≤ Q^(2*v+1) := by
    rw [pow_succ, hmeq]
    nlinarith only [mul_le_mul_of_nonneg_right hℓQ (zero_le_one.trans hQpow), hQpow]
  have hlog : Real.log (2*(m:ℝ)) ≤ Q^2 := calc
    _ ≤ Real.log (Q^(2*v+2)) := by
      apply Real.log_le_log (by positivity)
      rw [show 2*v+2 = (2*v+1)+1 by omega, pow_succ]
      nlinarith only [mul_le_mul_of_nonneg_left hml (by norm_num : (0:ℝ) ≤ 2),
        mul_le_mul_of_nonneg_left (show 2 ≤ Q by linarith) (pow_nonneg hQ₀.le (2*v+1))]
    _ = ((2*v+2 : ℕ) : ℝ) * Real.log Q := Real.log_pow Q _
    _ ≤ Q * Q := by
      apply mul_le_mul (by dsimp [Q]; exact_mod_cast hvq) (Real.log_le_self hQ₀.le)
        (Real.log_nonneg hQ₁) hQ₀.le
    _ = _ := (sq Q).symm
  have hs : Real.sqrt ((m : ℝ) * Real.log (2*m)) ≤ Q^(v+2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ Q^(2*v+1) * Q^2 := mul_le_mul_of_nonneg_right hml
          (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2*m))) |>.trans
          (mul_le_mul_of_nonneg_left hlog (by positivity))
      _ = Q^(2*v+3) := (pow_add ..).symm
      _ ≤ Q^((v+2)*2) := pow_le_pow_right₀ hQ₁ (by omega)
      _ = _ := pow_mul ..
  have hstage := countRepair_stages_le hℓ hm
  have hpart : 8*((ℓ:ℝ)-1)*Real.sqrt ((m:ℝ)*Real.log (2*m)) + 2 ≤ Q^3 * Q^(v+2) := by
    have h8 : 8*((ℓ:ℝ)-1) ≤ Q*Q := by nlinarith [sq_nonneg (Q-8)]
    have hmain := mul_le_mul h8 hs (Real.sqrt_nonneg _) (mul_self_nonneg Q)
    have hh := one_le_pow₀ hQ₁ (n := v+2)
    have hgap : 2 ≤ Q^3-Q*Q := by nlinarith [mul_nonneg (sq_nonneg Q) (show 0 ≤ Q-2 by linarith)]
    nlinarith only [hmain, mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ Q^3-Q*Q), hgap]
  calc
    _ ≤ _ := hstage
    _ ≤ (Q * Q) * (Q^3 * Q^(v+2)) := by
      apply mul_le_mul _ hpart _ (mul_self_nonneg Q)
      · exact mul_le_mul hℓQ (by linarith) (Nat.cast_nonneg _) hQ₀.le
      · have hr : (2:ℝ) ≤ ℓ := by exact_mod_cast hℓ
        nlinarith [mul_nonneg (show 0 ≤ 8*((ℓ:ℝ)-1) by linarith) (Real.sqrt_nonneg ((m:ℝ)*Real.log (2*m)))]
    _ = Q^(v+7) := by ring

/-- For any constants depending only on the radix and label length, one finite
choice of query count and alphabet gives the strict recursion saving. The same
choice works for every auxiliary dimension within the Gram feature bound. -/
theorem exists_primeKernel_strict_saving {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {θ : ℝ}
    (hθ : 1/2 < θ) (C : ℕ → ℝ) :
    ∃ L b m : ℕ, ℓ ≤ L ∧ 1 ≤ b ∧ 2 ≤ m ∧ m ≡ 1 [MOD ℓ] ∧
      ∀ D : ℕ, 1 ≤ D → D ≤ 1 + (1 + L*2^b)^(ℓ-1) →
        let q : ℝ := 2^b
        C L * (((ℓ : ℝ)+2) * countPencilOrder ℓ m * D *
          ((1+(b:ℝ))^L + (m:ℝ)/q^(L-L/ℓ)) + ((m:ℝ)+D)/(m:ℝ)^3) <
          ((2*(m+D-1) : ℕ) : ℝ)^θ := by
  obtain ⟨L, v, hL, hv, hgap⟩ := cost_exponents hℓ hθ
  obtain ⟨b, hb, hbig, hinc⟩ := exists_bit_width L
    (max (C L) ((10 + ℓ + 2 + L + 2*v + 2 : ℕ) : ℝ))
  let q : ℕ := 2^b
  have hqbig : 10 + ℓ + 2 + L + 2*v + 2 ≤ q := by
    have h := (le_max_right _ _).trans hbig
    dsimp [q]
    exact_mod_cast h
  have hq : 10 ≤ q := by omega
  let m := ℓ*q^(2*v)+1
  have hqp : 0 < q^(2*v) := pow_pos (by omega) _
  have hm : 2 ≤ m := by dsimp [m]; nlinarith
  refine ⟨L, b, m, hL, hb, hm, ?_, ?_⟩
  · simp [m, Nat.ModEq]
  intro D hD hDrank
  let Q : ℝ := q
  have hQeq : Q = (2:ℝ)^b := by simp [Q,q]
  change C L * (_ + _) < _
  have hQ : 10 ≤ Q := by dsimp [Q]; exact_mod_cast hq
  have hQ₁ : 1 ≤ Q := by linarith
  have hQ₀ : 0 < Q := by linarith
  have hsmall (i : ℕ) : 1 ≤ Q^i := one_le_pow₀ hQ₁
  have hℓQ : (ℓ:ℝ)+2 ≤ Q := by dsimp [Q]; exact_mod_cast (by omega : ℓ+2 ≤ q)
  have hLQ : (L:ℝ) ≤ Q := by dsimp [Q]; exact_mod_cast (by omega : L ≤ q)
  have hcQ : C L ≤ Q := by rw [hQeq]; exact (le_max_left ..).trans hbig
  have hmeq : (m:ℝ) = ℓ * Q^(2*v) + 1 := by simp [m,Q]
  have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hstage := stage_bound hℓ hm hq (by omega : ℓ+2 ≤ q) (by omega : 2*v+2 ≤ q) rfl
  have hinc' : (1+(b:ℝ))^L ≤ Q := by dsimp [Q]; exact_mod_cast hinc
  have hcharged : (m:ℝ) / Q^(L-L/ℓ) ≤ Q := by
    rw [hv, div_le_iff₀ (pow_pos hQ₀ _), hmeq]
    nlinarith only [mul_le_mul_of_nonneg_right hℓQ (pow_nonneg hQ₀.le (2*v)), hsmall (2*v)]
  let a := 3*(ℓ-1)
  have haux : (D:ℝ) ≤ Q^(a+1) := by
    have hr : (D:ℝ) ≤ 1+(1 + L*Q)^(ℓ-1) := by dsimp [Q,q]; exact_mod_cast hDrank
    have hpoly : 1+(L:ℝ)*Q ≤ Q^3 := by
      nlinarith [mul_le_mul_of_nonneg_right hLQ hQ₀.le,
        mul_nonneg (show 0 ≤ Q-2 by linarith) (sq_nonneg Q), sq_nonneg (Q-1)]
    have hs := pow_le_pow_left₀ (show 0 ≤ 1+(L:ℝ)*Q by positivity) hpoly (ℓ-1)
    rw [← pow_mul] at hs
    rw [pow_succ]
    nlinarith only [hr, hs, hsmall a, mul_le_mul_of_nonneg_right
      (show 2 ≤ Q by linarith) (pow_nonneg hQ₀.le a)]
  have hhalf : ((ℓ:ℝ)+2) * countPencilOrder ℓ m * D *
      ((1+(b:ℝ))^L + (m:ℝ)/Q^(L-L/ℓ)) ≤ Q^(v+a+10) := calc
    _ ≤ (Q^(v+7) * Q^(a+1)) * Q^2 := by
      apply mul_le_mul _ (by nlinarith [sq_nonneg (Q-1)]) (by positivity) (by positivity)
      exact mul_le_mul hstage haux (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring
  have hrep : ((m:ℝ)+D)/(m:ℝ)^3 ≤ Q^(a+2) := by
    have hmon : (m:ℝ) ≤ (m:ℝ)^3 := by nlinarith [mul_nonneg (show 0 ≤ (m:ℝ)-1 by linarith) (sq_nonneg (m:ℝ))]
    calc
      _ = (m:ℝ)/(m:ℝ)^3 + (D:ℝ)/(m:ℝ)^3 := add_div ..
      _ ≤ 1 + (D:ℝ) := add_le_add ((div_le_one₀ (by positivity)).mpr hmon)
        (div_le_self (by positivity) (by linarith))
      _ ≤ Q^(a+2) := by
        rw [show a+2 = (a+1)+1 by omega, pow_succ]
        nlinarith only [haux, hsmall (a+1), mul_le_mul_of_nonneg_right
          (show 2 ≤ Q by linarith) (pow_nonneg hQ₀.le (a+1))]
  have hupper : C L * (((ℓ:ℝ)+2) * countPencilOrder ℓ m * D *
      ((1+(b:ℝ))^L + (m:ℝ)/Q^(L-L/ℓ)) + ((m:ℝ)+D)/(m:ℝ)^3) ≤
      Q^(v+a+14) := calc
    _ ≤ Q * (Q^(v+a+10) + Q^(v+a+10)) := by
      apply mul_le_mul hcQ _ (by positivity) hQ₀.le
      exact add_le_add hhalf (hrep.trans (pow_le_pow_right₀ hQ₁ (by omega)))
    _ ≤ Q^(v+a+12) := by
      rw [show v+a+12 = (v+a+10)+2 by omega, pow_add Q (v+a+10) 2]
      nlinarith only [mul_le_mul_of_nonneg_right (show 2*Q ≤ Q^2 by nlinarith [sq_nonneg (Q-1)])
        (pow_nonneg hQ₀.le (v+a+10))]
    _ ≤ Q^(v+a+14) := pow_le_pow_right₀ hQ₁ (by omega)
  have harity : Q^(2*v) ≤ ((2*(m+D-1):ℕ):ℝ) := by
    have hbase : q^(2*v) ≤ m := by
      dsimp [m]
      exact (Nat.le_mul_of_pos_left _ (by omega)).trans (Nat.le_add_right _ _)
    dsimp [Q]
    exact_mod_cast (by omega : q^(2*v) ≤ 2*(m+D-1))
  rw [← hQeq]
  apply lt_of_le_of_lt hupper
  calc
    Q^(v+a+14) = Q^((v+a+14:ℕ):ℝ) := (Real.rpow_natCast ..).symm
    _ < Q^(((2*v : ℕ):ℝ)*θ) := Real.rpow_lt_rpow_of_exponent_lt (by linarith) hgap
    _ = (Q^(2*v))^θ := by rw [Real.rpow_mul hQ₀.le, Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) harity (by linarith)

/-- Number of axis calls allocated to a full repair on `R` rows per label.
There are two endpoint incidence lists for the free rectangles, and one
common transform for each charged rectangle and query. -/
noncomputable def primeKernelCallBudget (ℓ L b m D R : ℕ) : ℕ :=
  let q := 2^b
  let N := q^L
  let stages := (ℓ+2) * countPencilOrder ℓ m
  stages * (2*ℓ*D*R) * (2*N*(1+b)^L + m*(2^L*q^(L/ℓ))) +
    4 * (R/(2*m^3)) * (2*(m+D-1)) * N

/-- The predicted call budget divided by the number of independent inputs
falls strictly below the recursion threshold. Expanding every row in a
scalar-extension basis of positive size `H` preserves this ratio. -/
theorem exists_primeKernelCallBudget_lt {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {θ : ℝ} (hθ : 1/2 < θ) :
    ∃ L b m : ℕ, ℓ ≤ L ∧ 1 ≤ b ∧ 2 ≤ m ∧ m ≡ 1 [MOD ℓ] ∧
      ∀ D : ℕ, 1 ≤ D → D ≤ 1 + (1+L*2^b)^(ℓ-1) →
        ∀ R H : ℕ, 0 < R → 0 < H →
          ((H * primeKernelCallBudget ℓ L b m D R : ℕ) : ℝ) /
            ((H * R * (2^b)^L : ℕ) : ℝ) < ((2*(m+D-1) : ℕ) : ℝ)^θ := by
  let C (L : ℕ) := 8 * (ℓ:ℝ) * (2:ℝ)^L
  obtain ⟨L,b,m,hL,hb,hm,hcong,hcost⟩ := exists_primeKernel_strict_saving hℓ hθ C
  refine ⟨L,b,m,hL,hb,hm,hcong,?_⟩
  intro D hD hDr R H hR hH
  let q : ℝ := 2^b
  let U : ℝ := ((ℓ:ℝ)+2)*countPencilOrder ℓ m*D
  let S : ℝ := (R/(2*m^3) : ℕ)
  let I : ℝ := (1+(b:ℝ))^L
  let X : ℝ := (m:ℝ)/q^(L-L/ℓ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hI : 0 ≤ I := by dsimp [I]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hR' : (0:ℝ) < R := by exact_mod_cast hR
  have hH' : (0:ℝ) < H := by exact_mod_cast hH
  have hℓ' : (2:ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hqt : q^(L/ℓ) * q^(L-L/ℓ) = q^L := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self ..)]
  have hXeq : X * q^L = m * q^(L/ℓ) := by
    rw [← hqt]
    dsimp [X]
    field_simp
  have hS : S * (2*m^3) ≤ R := by
    dsimp [S]
    exact_mod_cast Nat.div_mul_le_self R (2*m^3)
  have hA : ((2*(m+D-1) : ℕ):ℝ) ≤ 2*((m:ℝ)+D) := by
    exact_mod_cast Nat.mul_le_mul_left 2 (Nat.sub_le (m+D) 1)
  have hlb : 1 ≤ (2:ℝ)^L := one_le_pow₀ (by norm_num)
  have hCoef₁ : 4*(ℓ:ℝ) ≤ C L := by dsimp [C]; nlinarith only [hℓ', mul_le_mul_of_nonneg_left hlb (Nat.cast_nonneg (α:=ℝ) ℓ)]
  have hCoef₂ : 2*(ℓ:ℝ)*2^L ≤ C L := by dsimp [C]; nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) ℓ) (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) L)]
  have hCoef₃ : 4 ≤ C L := by linarith
  have hpencil : U * (2*(ℓ:ℝ)) * (2*I + 2^L * X) ≤ C L * (U*(I+X)) := by
    nlinarith only [mul_le_mul_of_nonneg_right hCoef₁ (mul_nonneg hU hI),
      mul_le_mul_of_nonneg_right hCoef₂ (mul_nonneg hU hX)]
  have hconv : 4*S*((2*(m+D-1):ℕ):ℝ)/(R:ℝ) ≤ C L * (((m:ℝ)+D)/m^3) := by
    have hSc : 0 ≤ S := Nat.cast_nonneg _
    calc
      _ ≤ 4*S*(2*((m:ℝ)+D))/(R:ℝ) := by gcongr
      _ ≤ 4 * (((m:ℝ)+D)/m^3) := by
        rw [mul_div_assoc', div_le_div_iff₀ hR' (by positivity)]
        nlinarith only [mul_le_mul_of_nonneg_right hS (show 0 ≤ 4*((m:ℝ)+D) by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hCoef₃ (by positivity)
  apply lt_of_le_of_lt _ (hcost D hD hDr)
  calc
    _ = U * (2*(ℓ:ℝ)) * (2*I + 2^L*X) + 4*S*((2*(m+D-1):ℕ):ℝ)/R := by
      simp only [primeKernelCallBudget, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
        Nat.cast_ofNat, Nat.cast_one]
      change (H:ℝ) * (((ℓ+2)*countPencilOrder ℓ m) * (2*ℓ*D*R) *
        (2*q^L*I + m*(2^L*q^(L/ℓ))) + 4*S*(2*((m+D-1:ℕ):ℝ))*q^L) /
          (H*R*q^L) = _
      rw [show (m:ℝ)*(2^L*q^(L/ℓ)) = 2^L*(X*q^L) by rw [hXeq]; ring]
      dsimp [U]
      field_simp
    _ ≤ _ := by linarith only [hpencil, hconv]

end FiniteFourier
end LinearAlgebra
end OAI
