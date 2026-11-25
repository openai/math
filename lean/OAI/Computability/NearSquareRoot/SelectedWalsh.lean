import OAI.Computability.NearSquareRoot.WalshPieces
import OAI.Computability.NearSquareRoot.WalshPadding
import Mathlib.Tactic.Linarith

/-!
# Resource recurrences for a selected-bit Walsh piece

At level `j` the transform acts on `2 * A^j` bits. A recursive node makes
`σ` calls, each on one stream of volume `V/W`. Setup is charged at every
node. The time bound uses all the children, while the space bound accounts
for a single active path with parked parent streams.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open Filter Finset

/-- Cost inequalities for one recursive Walsh piece on bit volume `V`.
`L` is the scan overhead and `P` the additive setup cost per node. -/
structure WalshPieceRecurrence (A W σ : ℕ) (ρ C L P : ℝ) (T : ℕ → ℝ → ℝ) : Prop where
  base : ∀ V, 0 ≤ V → T 0 V ≤ C * L * V * (1 + (2 : ℝ)^ρ) + P
  step : ∀ j V, 0 ≤ V →
    T (j+1) V ≤ C * L * V * (1 + ((2 : ℝ) * (A : ℝ)^(j+1))^ρ)
      + P + σ * T j (V/W)

theorem walsh_piece_time_bound {A W σ : ℕ} {ρ C : ℝ}
    (hA : 1 ≤ A) (hW : 0 < W) (hρ : 0 ≤ ρ) (hC : 0 ≤ C)
    (hsaving : (σ : ℝ) / W < (A : ℝ) ^ ρ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (L P : ℝ), 0 ≤ L → 0 ≤ P → ∀ T : ℕ → ℝ → ℝ,
    WalshPieceRecurrence A W σ ρ C L P T →
    ∀ j V, 0 ≤ V →
      T j V ≤ B * L * V * ((2 : ℝ) * (A : ℝ)^j)^ρ + P * (σ + 1 : ℝ)^j := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  let r := (A : ℝ) ^ ρ
  let b := (σ : ℝ) / W
  have hr : 1 ≤ r := Real.one_le_rpow hA' hρ
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hgap : 0 < r - b := sub_pos.mpr hsaving
  let B := 2 * C * r / (r - b)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have heq : B * (r - b) = 2 * C * r := (div_mul_cancel₀ _ hgap.ne')
  have hBlarge : 2 * C ≤ B := by nlinarith [mul_nonneg hB hb]
  refine ⟨B, hB, ?_⟩
  intro L P hL hP T hT j
  induction j with
  | zero =>
    intro V hV
    simp only [pow_zero, mul_one]
    have htwo : 1 ≤ (2 : ℝ)^ρ := Real.one_le_rpow (by norm_num) hρ
    calc
      T 0 V ≤ C * L * V * (1 + (2 : ℝ)^ρ) + P := hT.base V hV
      _ ≤ C * L * V * (2 * (2 : ℝ)^ρ) + P := by gcongr; linarith
      _ ≤ B * L * V * (2 : ℝ)^ρ + P := by
        rw [show C * L * V * (2 * (2 : ℝ)^ρ) = (2*C) * L * V * (2 : ℝ)^ρ by ring]
        gcongr
  | succ j ih =>
    intro V hV
    let a := ((2 : ℝ) * (A : ℝ)^j)^ρ
    have ha : 1 ≤ a := Real.one_le_rpow
      (by nlinarith [one_le_pow₀ hA' (n := j)] : 1 ≤ (2 : ℝ) * (A : ℝ)^j) hρ
    have hnext : ((2 : ℝ) * (A : ℝ)^(j+1))^ρ = a*r := by
      rw [pow_succ, ← mul_assoc, Real.mul_rpow (by positivity) (Nat.cast_nonneg _)]
    have hchild := ih (V / W) (div_nonneg hV hW'.le)
    have hlocal : 1 + a*r ≤ 2 * (a*r) := by nlinarith [one_le_mul_of_one_le_of_one_le ha hr]
    have hvolume : (σ : ℝ) * (B * L * (V / W) * a) = b * B * L * V * a := by
      dsimp [b]
      ring
    have hscale : 2*C*r + b*B = B*r := by linarith only [heq]
    calc
      T (j+1) V ≤ C * L * V * (1 + a*r) + P + σ * T j (V / W) := by
        simpa only [hnext] using hT.step j V hV
      _ ≤ C * L * V * (2 * (a*r)) + P +
          σ * (B * L * (V / W) * a + P * (σ + 1 : ℝ)^j) := by gcongr
      _ = (2*C*r + b*B) * L * V * a + P + σ * (P * (σ + 1 : ℝ)^j) := by
        rw [mul_add, hvolume]
        ring
      _ ≤ B * L * V * ((2 : ℝ) * (A : ℝ)^(j+1))^ρ + P * (σ + 1 : ℝ)^(j+1) := by
        rw [hscale, hnext, pow_succ]
        nlinarith [mul_le_mul_of_nonneg_left
          (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) σ] : 1 ≤ (σ + 1 : ℝ)) (n := j)) hP]

/-- The parent keeps auxiliary streams of total volume at most `C*V`.
Sibling calls reuse the same cells, so space recurses on one child. -/
theorem walsh_piece_space_bound {W : ℕ} {C P : ℝ}
    (hW : 2 ≤ W) (hC : 0 ≤ C)
    (S : ℕ → ℝ → ℝ)
    (base : ∀ V, 0 ≤ V → S 0 V ≤ C*V + P)
    (step : ∀ j V, 0 ≤ V → S (j+1) V ≤ C*V + P + S j (V/W)) :
    ∀ j V, 0 ≤ V → S j V ≤ 2*C*V + (j+1 : ℝ)*P := by
  have hW' : (2 : ℝ) ≤ W := by exact_mod_cast hW
  intro j
  induction j with
  | zero =>
    intro V hV
    simp only [Nat.cast_zero, zero_add, one_mul]
    exact (base V hV).trans (by nlinarith)
  | succ j ih =>
    intro V hV
    have hwpos : 0 < (W : ℝ) := by linarith
    have hchild := ih (V/W) (div_nonneg hV hwpos.le)
    have hhalf : V/W ≤ V/2 := div_le_div_of_nonneg_left hV (by norm_num) hW'
    calc
      S (j+1) V ≤ C*V + P + S j (V/W) := step j V hV
      _ ≤ C*V + P + (2*C*(V/2) + (j+1 : ℝ)*P) := by
        gcongr
        exact hchild.trans (by gcongr)
      _ = 2*C*V + (↑(j+1) + 1 : ℝ)*P := by push_cast; ring

/-- Total time of the even pieces before absorbing the polynomial setup into
the record volume. The constants are uniform in the width, the selected bits,
and the shape of the array. -/
theorem walsh_pieces_time_bound {A W σ : ℕ} {ρ C : ℝ}
    (hA : 1 < A) (hW : 0 < W) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hsaving : (σ : ℝ) / W < (A : ℝ) ^ ρ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (L P : ℝ), 0 ≤ L → 0 ≤ P → ∀ T : ℕ → ℝ → ℝ,
      WalshPieceRecurrence A W σ ρ C L P T → ∀ s V, 0 ≤ V →
      (∑ j : Fin (walshPieceDigits A s).length, ((walshPieceDigits A s).get j : ℝ) * T j V)
        ≤ B * L * V * (s : ℝ)^ρ + P * (s : ℝ)^(σ+1) := by
  obtain ⟨B, hB, hpiece⟩ := walsh_piece_time_bound hA.le hW hρ.le hC hsaving
  obtain ⟨D, hD, hdigits⟩ := walsh_piece_cost_bound hA hρ
  refine ⟨B*D, mul_nonneg hB hD, ?_⟩
  intro L P hL hP T hT s V hV
  let digit (j : Fin (walshPieceDigits A s).length) : ℝ := (walshPieceDigits A s).get j
  calc
    _ ≤ ∑ j, digit j * (B*L*V*((2 : ℝ)*(A : ℝ)^(j : ℕ))^ρ + P*(σ+1 : ℝ)^(j : ℕ)) := by
      exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
        (hpiece L P hL hP T hT j V hV) (Nat.cast_nonneg _)
    _ = B*L*V * (∑ j, digit j * ((2 : ℝ)*(A : ℝ)^(j : ℕ))^ρ) +
          P * (∑ j, digit j * (σ+1 : ℝ)^(j : ℕ)) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun j _ => by ring
    _ ≤ B*L*V * (D*(s : ℝ)^ρ) + P*(s : ℝ)^(σ+1) := by
      gcongr
      · exact hdigits s
      · exact walsh_piece_setup_bound hA σ s
    _ = _ := by ring

/-- Bit volume after padding complete spectator rows. The record width is
`R*k`, as in a fixed-point format with linear component widths. -/
noncomputable def walshPaddedVolume (A W k s : ℕ) (R : ℝ) : ℝ :=
  (WalshPadding.paddedRows (2^(k-s)) W (WalshPadding.depth A s) * 2^s : ℕ) * (R*k)

/-- At sparse widths, the sum of all the even-piece runs satisfies the time
bound, including both padding and polynomial-per-node setup. -/
theorem eventually_walsh_pieces_time {A W σ d : ℕ} {ρ C c R Q : ℝ}
    (hA : 1 < A) (hW : 0 < W) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hc : 0 < c) (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (hsaving : (σ : ℝ) / W < (A : ℝ) ^ ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ k : ℕ in atTop, ∀ s : ℕ,
      (s : ℝ) ≤ c*k / Real.log (2+k) → ∀ T : ℕ → ℝ → ℝ,
      WalshPieceRecurrence A W σ ρ C (1 + Real.log (2+k)) (Q*(k : ℝ)^d) T →
      (∑ j : Fin (walshPieceDigits A s).length, ((walshPieceDigits A s).get j : ℝ) *
        T j (walshPaddedVolume A W k s R))
      ≤ K * (2:ℝ)^k * k * (1 + (k:ℝ))^ρ * (1 + Real.log (2+k)) := by
  obtain ⟨B, hB, hpieces⟩ := walsh_pieces_time_bound hA hW hρ hC hsaving
  refine ⟨B*(2*R)+Q, by positivity, ?_⟩
  filter_upwards [WalshPadding.eventually_paddedRows_bound hA hW c hc,
    WalshPadding.eventually_twice_selected_le c hc,
    WalshPadding.eventually_pow_le_two_pow_half (d+(σ+1)), eventually_ge_atTop 1]
      with k hpad hsparse hpoly hk
  intro s hs T hT
  let L : ℝ := 1 + Real.log (2+k)
  have hL : 1 ≤ L := by
    dsimp only [L]
    linarith [Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k] : 1 ≤ (2+k:ℝ))]
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hsk : s ≤ k := by have := hsparse s hs; omega
  have hpow := (hpad s hs).2.2.2.2
  have hvol : walshPaddedVolume A W k s R ≤ (2*(2:ℝ)^k) * (R*k) := by
    unfold walshPaddedVolume
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hpow) (by positivity)
  have hV : 0 ≤ walshPaddedVolume A W k s R := by unfold walshPaddedVolume; positivity
  have hsetup : (k:ℝ)^d * (s:ℝ)^(σ+1) ≤ (2:ℝ)^k := by
    have : k^(d+(σ+1)) ≤ 2^k :=
      hpoly.trans (Nat.pow_le_pow_right (by decide) (Nat.div_le_self k 2))
    have hcst : (k:ℝ)^(d+(σ+1)) ≤ (2:ℝ)^k := by exact_mod_cast this
    rw [pow_add] at hcst
    exact le_trans (by gcongr) hcst
  have hw : 1 ≤ (1 + (k:ℝ))^ρ := Real.one_le_rpow (by linarith) hρ.le
  have hweight : (s:ℝ)^ρ ≤ (1+(k:ℝ))^ρ := Real.rpow_le_rpow (Nat.cast_nonneg _)
    (by
      have : (s:ℝ) ≤ k := by exact_mod_cast hsk
      linarith) hρ.le
  calc
    _ ≤ B*L*walshPaddedVolume A W k s R*(s:ℝ)^ρ + (Q*(k:ℝ)^d)*(s:ℝ)^(σ+1) :=
      hpieces L _ (zero_le_one.trans hL) (by positivity) T hT s _ hV
    _ ≤ B*L*((2*(2:ℝ)^k)*(R*k))*(1+(k:ℝ))^ρ + Q*(2:ℝ)^k := by
      rw [mul_assoc Q]
      gcongr
    _ ≤ B*L*((2*(2:ℝ)^k)*(R*k))*(1+(k:ℝ))^ρ + Q*(2:ℝ)^k*k*(1+(k:ℝ))^ρ*L := by
      have hge : 1 ≤ (k:ℝ)*(1+(k:ℝ))^ρ*L :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hk' hw) hL
      nlinarith [mul_le_mul_of_nonneg_left hge (by positivity : 0 ≤ Q*(2:ℝ)^k)]
    _ = _ := by dsimp [L]; ring

/-- Each piece fits in the same linear arena: the bound is uniform over its
digit position, so the arena can be reused by all the sequential pieces. -/
theorem eventually_walsh_piece_space {A W d : ℕ} {C c R Q : ℝ}
    (hA : 1 < A) (hW : 2 ≤ W) (hC : 0 ≤ C)
    (hc : 0 < c) (hR : 0 ≤ R) (hQ : 0 ≤ Q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ k : ℕ in atTop, ∀ s : ℕ,
      (s : ℝ) ≤ c*k / Real.log (2+k) → ∀ S : ℕ → ℝ → ℝ,
      (∀ V, 0 ≤ V → S 0 V ≤ C*V + Q*(k : ℝ)^d) →
      (∀ j V, 0 ≤ V → S (j+1) V ≤ C*V + Q*(k : ℝ)^d + S j (V/W)) →
      ∀ j : Fin (walshPieceDigits A s).length,
      S j (walshPaddedVolume A W k s R) ≤ K*(2:ℝ)^k*k := by
  refine ⟨4*C*R+2*Q, by positivity, ?_⟩
  filter_upwards [WalshPadding.eventually_paddedRows_bound hA (by omega : 0 < W) c hc,
    WalshPadding.eventually_twice_selected_le c hc,
    WalshPadding.eventually_pow_le_two_pow_half d, eventually_ge_atTop 1]
      with k hpad hsparse hpoly hk
  intro s hs S base step j
  have hsk : s ≤ k := by have := hsparse s hs; omega
  have hj : (j : ℕ) ≤ k := by
    have hlen := j.isLt
    by_cases he : s / 2 = 0
    · simp [walshPieceDigits, he] at hlen
    · change (j : ℕ) < (A.digits (s/2)).length at hlen
      rw [Nat.length_digits A _ hA he] at hlen
      have := Nat.log_le_self A (s/2)
      omega
  have hP : (k:ℝ)^d ≤ (2:ℝ)^k := by
    exact_mod_cast hpoly.trans (Nat.pow_le_pow_right (by decide) (Nat.div_le_self k 2))
  have hv : walshPaddedVolume A W k s R ≤ (2*(2:ℝ)^k)*(R*k) := by
    unfold walshPaddedVolume
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (hpad s hs).2.2.2.2) (by positivity)
  have hV : 0 ≤ walshPaddedVolume A W k s R := by unfold walshPaddedVolume; positivity
  have hdepth : (j:ℝ)+1 ≤ 2*k := by
    have hj' : (j:ℝ) ≤ k := by exact_mod_cast hj
    have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  calc
    _ ≤ 2*C*walshPaddedVolume A W k s R + ((j:ℕ)+1:ℝ)*(Q*(k:ℝ)^d) :=
      walsh_piece_space_bound hW hC S base step j _ hV
    _ ≤ 2*C*((2*(2:ℝ)^k)*(R*k)) + (2*(k:ℝ))*(Q*(2:ℝ)^k) := by gcongr
    _ = _ := by ring

end NearSquareRoot
end Computability
end OAI
