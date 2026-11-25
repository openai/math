import OAI.Hierarchy.DescentResetPrimeTariff
import OAI.Hierarchy.DescentResetIngressScale
import OAI.Hierarchy.DescentResetRemixTariff

namespace OAI
/-! The complete per-host root tariff admits a rate chosen before the tail,
the logarithmic height divisor and the shared-table saving are fixed. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentDatedAddressBook DescentCompiler TerminalScale Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

def selectedRootUnit (t f g reset τ B D ratio lead exponent J : ℕ) :=
  ingressUnit G t f g reset τ B (quota t) ratio J+PhysicalReset.primeUnit G t f g reset τ B D ratio J+
    remixFactor ratio*scale J (5*stencilRate G t f g reset)+lead*scale J exponent

def selectedRootRate (t f g reset exponent : ℕ) :=
  max (canvasRate G t f g reset) (max (5*stencilRate G t f g reset) exponent)+7

private theorem root_unit_bound (canvas remix exponent c₁ c₂ c₃ r lead τ B : ℕ) (den : 0 < B) :
    ∀ᶠ h : ℕ in atTop,
      let J := Nat.log 2 h / (2 * B)
      let p := tail τ J + 1
      scale J canvas * (c₁ * p^2) + (scale J canvas * (c₂ * p^4) + c₃ * p^6) +
        r * scale J remix + lead * scale J exponent ≤
        scale J (max canvas (max remix exponent) + 7) := by
  let m := max canvas (max remix exponent)
  let c := c₁ + c₂ + c₃ + r + lead
  let K := c * (τ + 1)^6
  filter_upwards [eventually_ge_atTop (2^(K*(2*B)))] with h late
  intro J p
  have enough : K ≤ J := (Nat.le_div_iff_mul_le (by omega : 0 < 2*B)).2
    (Nat.le_log_of_pow_le (by decide) late)
  have large : K ≤ 2^(J+1) := enough.trans ((Nat.le_succ _).trans (Nat.lt_two_pow_self (n := J+1)).le)
  have mono {x : ℕ} (bound : x ≤ m) : scale J x ≤ scale J m :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_right (J+1) bound)
  have pp : 0 < p := Nat.succ_pos _
  have pm : 0 < scale J m := Nat.two_pow_pos _
  have p₆ : 0 < p^6 := Nat.pow_pos pp
  have i₁ := Nat.mul_le_mul (mono (le_max_left canvas (max remix exponent)))
    (Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_right pp (by decide : 2 ≤ 6)))
  have i₂ := Nat.mul_le_mul (mono (le_max_left canvas (max remix exponent)))
    (Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_right pp (by decide : 4 ≤ 6)))
  have i₃ := Nat.le_mul_of_pos_left (c₃ * p^6) pm
  have ir : r * scale J remix ≤ scale J m * (r * p^6) := by
    rw [Nat.mul_comm r (scale J remix)]
    exact Nat.mul_le_mul (mono ((le_max_left remix exponent).trans (le_max_right canvas _)))
      (Nat.le_mul_of_pos_right r p₆)
  have il : lead * scale J exponent ≤ scale J m * (lead * p^6) := by
    rw [Nat.mul_comm lead (scale J exponent)]
    exact Nat.mul_le_mul (mono ((le_max_right remix exponent).trans (le_max_right canvas _)))
      (Nat.le_mul_of_pos_right lead p₆)
  calc
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add i₁ (Nat.add_le_add i₂ i₃)) ir) il
    _ = scale J m * (c*p^6) := by simp only [c, Nat.add_mul, Nat.mul_add, Nat.add_assoc]
    _ ≤ scale J m * scale J 7 := Nat.mul_le_mul_left _ (logarithmic c 6 τ J large)
    _ = _ := scale_mul J m 7

theorem selected_root_unit_scale (t f g reset τ B D ratio lead exponent : ℕ) (den : 0 < B) :
    ∀ᶠ h : ℕ in atTop,
      let J:=Nat.log 2 h/(2*B)
      selectedRootUnit G t f g reset τ B D ratio lead exponent J ≤ scale J (selectedRootRate G t f g reset exponent) := by
  exact root_unit_bound (canvasRate G t f g reset) (5 * stencilRate G t f g reset) exponent
    (2097152 * (ratio+1) * (localCoefficient G t f g reset (quota t) τ * (2*B+1)^2+1))
    (canvasFactor G t f g reset τ B (quota t) D ratio)
    (estimatorFactor G t f g reset τ B (quota t) D ratio) (remixFactor ratio) lead τ B den

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
