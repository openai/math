import OAI.Hierarchy.ProbeLedger

namespace OAI
/-! # Integer copies and price-funded outstanding stock for a repair -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators Classical
noncomputable section

/-- Integer copies and integer bits withdrawn per demand. -/
def copied (K b w : ℕ) := w / (K*b)

theorem copied_bits {K b w : ℕ} (hK : 0 < K) (hb : 0 < b) (large : 2*(K*b) ≤ w) :
    (w:ℝ)/(2*K) ≤ b*copied K b w ∧ (b:ℝ)*copied K b w ≤ (w:ℝ)/K := by
  have h := Nat.div_add_mod w (K*b)
  have rem := Nat.mod_lt w (Nat.mul_pos hK hb)
  have hK' : 0 < (K:ℝ) := by exact_mod_cast hK
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 2*(K:ℝ))).2
    have natbound : w ≤ b*copied K b w*(2*K) := by
      dsimp [copied]
      nlinarith only [h,rem,large]
    exact_mod_cast natbound
  · apply (le_div_iff₀ hK').2
    have natbound : b*copied K b w*K ≤ w := by
      dsimp [copied]
      nlinarith only [h,Nat.zero_le (w%(K*b))]
    exact_mod_cast natbound

/-- Every accurate selected ordinary demand has enough outstanding integer stock,
even when the same commodity is demanded several times in the local format. -/
theorem adequate_stock {a bonus M s A γ quote : ℝ} {bits w b K multiplicity : ℕ}
    (ha : 0 < a) (hbonus : 0 ≤ bonus) (hM : 0 ≤ M) (hs : 0 < s) (hw : 0 < w)
    (hK : 0 < K) (hb : 0 < b) (large : 2*(K*b) ≤ w)
    (accurate : |quote-offer a bonus M s (bits/w) A| ≤ γ/2) (demand : γ ≤ quote)
    (rate : (multiplicity:ℝ)/K ≤ s*a*γ) :
    multiplicity*(b*copied K b w) ≤ bits := by
  have hw' : 0 < (w:ℝ) := by exact_mod_cast hw
  have hK' : 0 < (K:ℝ) := by exact_mod_cast hK
  have eqn := offer_stock (A:=A) ha hbonus hM hs (show 0 ≤ (bits:ℝ)/w by positivity)
  have level : γ/2 ≤ offer a bonus M s (bits/w) A := by linarith [(abs_le.mp accurate).2]
  have money : s*a*γ ≤ (bits:ℝ)/w := by nlinarith only [eqn,mul_le_mul_of_nonneg_left level (show 0 ≤ 2*s*a by positivity)]
  have units := (copied_bits hK hb large).2
  have supply := mul_le_mul_of_nonneg_left units (show 0 ≤ (multiplicity:ℝ) by positivity)
  have fit := (div_le_div_iff₀ hK' hw').1 (rate.trans money)
  have enough : (multiplicity:ℝ)*(b*copied K b w) ≤ bits := by
    calc
      _ ≤ _ := supply
      _ = ((multiplicity:ℝ)*w)/K := by ring
      _ ≤ _ := (div_le_iff₀ hK').2 fit
  exact_mod_cast enough

end
end Hierarchy.AdaptiveProbe

end OAI
