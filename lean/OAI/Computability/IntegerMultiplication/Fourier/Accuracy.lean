import OAI.Computability.IntegerMultiplication.Fourier.RestoreTable
import OAI.Computability.IntegerMultiplication.Fourier.NumericalBound

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fourier
open Finset Real
variable {s t : ℕ} [NeZero s] [NeZero t]

theorem param_geom {d s : ℕ} (h : 2≤d) (hs : paramPrec d≤s) :
    2*paramL d<s ∧ 2*(paramK d*paramJ d)<s ∧ paramJ d ≤ 2*paramD d s ∧ s ≤ paramD d s := by
  have hd1 : 1 ≤ d := by omega
  have he :
      2*d^27 < d^32 := by
    rw [show 32=5+27 by norm_num,pow_add]
    have ha : 2<d^5 := lt_of_lt_of_le (by norm_num : 2<(2:ℕ)^5)
      (Nat.pow_le_pow_left h 5)
    exact Nat.mul_lt_mul_of_pos_right ha (Nat.pow_pos (by omega))
  have hL : 2*d^26 ≤ 2*d^27 :=
    Nat.mul_le_mul_left _ (pow_le_pow_right₀ hd1 (by omega))
  have hJ : d^9 ≤ d^32 := pow_le_pow_right₀ hd1 (by norm_num)
  have hhs := paramD_spec h hs
  change 2*d^26 < _ ∧ 2*(d^18*d^9)<_ ∧ d^9≤_ ∧ _
  rw [← pow_add, show 18+9=27 by norm_num]
  change d^32 ≤ s at hs
  omega

/-- The finite resampling maps approximate P_s F_s to any exponential target. This
completes the conditioning/identity part of the proposed variant for a single axis.
Nearest centers, K and B tables and sparsity for assembly are defined in companion modules
of this directory. -/
theorem accuracy {d s t : ℕ} [NeZero s] [NeZero t] {H : ℝ}
    (e : s≤t)
    (hH : 0 ≤ H)
    (hd : 64*(H+20)≤ (d:ℝ))
    (hs : paramPrec d ≤ s) (ht : t ≤ 2^paramPrec d)
    (hg : ((1:ℝ)+1/(8*d))*(s:ℕ)≤(t:ℝ))
    {B : ℝ} {f : Arr s ℂ} (h : Bound f B) (hb : 0≤B) :
    let P : ℝ := (paramPrec d : ℕ)
    let J := paramJ d
    let K := paramK d
    let L := paramL d
    let D := paramD d s
    Gap (restore e D J K (dft t (-(s:ℤ)) (sample s t D L f))) (dft s t f)
      (Real.exp (-H*P)*B) := by
  let P : ℝ := (paramPrec d : ℕ)
  let J := paramJ d
  let K := paramK d
  let L := paramL d
  let R := paramR d
  let D := paramD d s
  let q := Real.exp (-(d:ℝ)^15/32)
  let r := Real.exp (-(H+12)*P)
  let C := (2*(D:ℝ)+1)*Real.exp (R:ℝ)
  change Gap (restore e D J K _) _ (Real.exp (-H*P)*B)
  obtain ⟨hqB,hrB,hC,hq,hq',hr,hc,hk,hx,hx',hv,hu⟩ :=
    param_est hH hd hs ht hg
  change ∀ i, ∑ j ∈ nhood J, ratio t D _ j ≤ q at hqB
  change ∀ i, ∑ j ∈ _ \ nhood J, ratio t D _ j ≤ r at hrB
  change ∀ i, 1/_ ≤ C at hC  -- unknown type
  have ha : 2≤d := by
    by_contra! e
    have h : (d:ℝ)<2 := by exact_mod_cast e
    linarith
  obtain ⟨g₁,g₂,g₃,g₄⟩ := param_geom ha hs
  let cut := Real.exp (-(4:ℝ)*D*L^2/s^2)
  have he := line_est (k:=K) e g₁ g₄ g₃ hq hq' hc hr hC hqB hrB h hb
  refine he.mono ?_
  have hP : 4 ≤ P := by
    have hg : 4 ≤ paramPrec d :=
      calc
        _ ≤ d^2 := by nlinarith
        _ ≤ d^32 := pow_le_pow_right₀ (by omega) (by norm_num)
    dsimp [P]
    exact_mod_cast hg
  have hcomb := combine_errors H P C (t:ℝ) (s:ℝ) q (q^K) cut r
    hP hH hc (by positivity) (by positivity) hq (pow_nonneg hq _) (Real.exp_pos _).le hr
    hx' hu hv hq' hk hx (le_refl r)
  change 2*(C*((t:ℝ)*(s*cut*B)))+(q^K)*((q+r)*(s*B))+_ ≤ _
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hcomb hb)
  ring
end Fourier

end IntegerMultiplication
end Computability
end OAI
