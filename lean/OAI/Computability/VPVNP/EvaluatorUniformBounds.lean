import OAI.Computability.VPVNP.EvaluatorLiteralResources

/-!
# Length-uniform bounds for the fixed evaluator table

All query, advice and scalar parameters can be bounded before the exponent
width is chosen. A single length envelope then bounds the physical clock,
advice length and tape window for every width, including widths selected by
the later diagonal construction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.MatrixCallbacks

open BinaryMachine SliceArithmetic EvaluatorProgramRawInput

/-- One numeric bound for the width-independent parameters at a length.
The entry query time is specified by its binary exponent. -/
def lengthEnvelope (t ℓ fields ports v e w extraSpace peak queryExponent : ℕ) :=
  let A := adviceCap fields t ℓ (WeightedStep.bankSpace v e w extraSpace)
  A + workspace v e w extraSpace peak + t + ℓ + ports + terminalTicks v w + queryExponent + 2

/-- Width and storage bounds may be chosen uniformly over all fields and
slice models at a given length. -/
theorem lengthEnvelope_mono {t t' ℓ ℓ' fields ports v v' e e' w w' h h' peak peak' q q' : ℕ}
    (ht : t ≤ t') (hl : ℓ ≤ ℓ') (hv : v ≤ v') (he : e ≤ e') (hw : w ≤ w')
    (hh : h ≤ h') (hp : peak ≤ peak') (hq : q ≤ q') :
    lengthEnvelope t ℓ fields ports v e w h peak q ≤ lengthEnvelope t' ℓ' fields ports v' e' w' h' peak' q' := by
  unfold lengthEnvelope adviceCap workspace WeightedStep.bankSpace WeightedStep.localTicks
    MultiplyCall.callCap HornerControl.digitCap terminalTicks
  dsimp only
  gcongr

theorem lengthEnvelope_polynomial (fields ports : ℕ) {t ℓ v e w h peak queryExponent : ℕ → ℕ}
    (ht : PolynomiallyBounded t) (hℓ : PolynomiallyBounded ℓ) (hv : PolynomiallyBounded v)
    (he : PolynomiallyBounded e) (hw : PolynomiallyBounded w) (hh : PolynomiallyBounded h)
    (hp : PolynomiallyBounded peak) (hq : PolynomiallyBounded queryExponent) :
    PolynomiallyBounded fun n ↦ lengthEnvelope (t n) (ℓ n) fields ports (v n) (e n) (w n) (h n) (peak n)
      (queryExponent n) := by
  have hb : PolynomiallyBounded fun n ↦ WeightedStep.bankSpace (v n) (e n) (w n) (h n) :=
    (((hv.add he).add hw).add (he.mul hw)).add hh
  have ha := adviceCap_polynomial fields ht hℓ hb
  have hs := workspace_polynomial hv he hw hh hp
  have hend : PolynomiallyBounded fun n ↦ terminalTicks (v n) (w n) :=
    ((((PolynomiallyBounded.const 3).mul hw).add (.const 3)).add hv)
  exact (((((((ha.add hs).add ht).add hℓ).add (.const ports)).add hend).add hq).add (.const 2))

theorem uniform_tape_clock (t Z ℓ fields ports v e w h peak queryExponent Q F L rawLength : ℕ)
    (hQ : Q ≤ 2^ℓ) (hF : F ≤ 2^queryExponent) (hL : L ≤ 2^queryExponent)
    (hraw : rawLength ≤ adviceCap fields t ℓ (WeightedStep.bankSpace v e w h)+(2*(t*Z)+6*Z+4)) :
    let A := adviceCap fields t ℓ (WeightedStep.bankSpace v e w h)
    let a := lengthEnvelope t ℓ fields ports v e w h peak queryExponent
    tapeTicks rawLength ports (fullTicks t Z ℓ Q A (WeightedStep.ticks v e w F)
      (WeightedStep.ticks v e w L) v w) ≤ 2^(6*a+23)*(Z+1)^4 := by
  intro A a
  have h₀ : a ≤ 2^a := Nat.lt_two_pow_self.le
  have hsum : WeightedStep.localTicks v e w + queryExponent + 1 ≤ a := by
    dsimp [a, lengthEnvelope, workspace]; omega
  have hcall (time : ℕ) (htime : time ≤ 2^queryExponent) : WeightedStep.ticks v e w time ≤ 2^a := by
    let m := WeightedStep.localTicks v e w + queryExponent
    have hm₁ : WeightedStep.localTicks v e w ≤ 2^m := (Nat.le_add_right ..).trans Nat.lt_two_pow_self.le
    have hm₂ : time ≤ 2^m := htime.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..))
    have hb : WeightedStep.ticks v e w time = WeightedStep.localTicks v e w + time := by
      unfold WeightedStep.ticks WeightedStep.localTicks; omega
    calc
      WeightedStep.ticks v e w time ≤ 2^m+2^m := hb ▸ Nat.add_le_add hm₁ hm₂
      _ = 2^(m+1) := by rw [pow_succ]; omega
      _ ≤ 2^a := Nat.pow_le_pow_right (by decide) hsum
  apply tapeTicks_le_exp_poly t Z ℓ Q A _ _ v w ports rawLength a
  · exact (by dsimp [a,A,lengthEnvelope]; omega : A ≤ a).trans h₀
  · exact (by dsimp [a,lengthEnvelope]; omega : t ≤ a).trans h₀
  · exact (by dsimp [a,lengthEnvelope]; omega : ℓ ≤ a).trans h₀
  · exact hQ.trans (Nat.pow_le_pow_right (by decide) (by dsimp [a,lengthEnvelope]; omega))
  · exact hcall F hF
  · exact hcall L hL
  · exact (by dsimp [a,lengthEnvelope]; omega : terminalTicks v w ≤ a).trans h₀
  · exact (by dsimp [a,lengthEnvelope]; omega : ports+1 ≤ a).trans h₀
  · exact hraw

/-- Bound the two physical tapes including the original raw input and both
possible directions of head movement. -/
theorem uniform_window (t Z ℓ fields ports v e w h peak queryExponent rawLength : ℕ)
    (hr : rawLength ≤ adviceCap fields t ℓ (WeightedStep.bankSpace v e w h)+(2*(t*Z)+6*Z+4)) :
    let A := adviceCap fields t ℓ (WeightedStep.bankSpace v e w h)
    let a := lengthEnvelope t ℓ fields ports v e w h peak queryExponent
    let radius := headRadius ports (fullSpace t Z ℓ (workspace v e w h peak) A v w)
    rawLength + radius + radius ≤ 2240*(ports+1)*(a+Z+1)^4 := by
  intro A a radius
  let n := a+Z+1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hparam : t+Z+ℓ+workspace v e w h peak+A+v+w+1 ≤ n := by
    dsimp [a,A,n,lengthEnvelope,terminalTicks]; omega
  have hRad : radius ≤ 1110*(ports+1)*n^4 :=
    (headRadius_le ..).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hparam _))
  have hs : t*Z ≤ n^2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have h₂ : n^2 ≤ n^4 := Nat.pow_le_pow_right hn (by decide)
  have h₁ : n ≤ n^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hn (by decide : 1 ≤ 4)
  have hA : A ≤ n := by omega
  change rawLength ≤ A+(2*(t*Z)+6*Z+4) at hr
  have hraw : rawLength ≤ 13*n^4 := by dsimp [n] at *; omega
  have hpos : n^4 ≤ (ports+1)*n^4 := by simpa only [Nat.succ_mul] using (Nat.le_add_left (n^4) (ports*n^4))
  change rawLength+radius+radius ≤ 2240*(ports+1)*n^4
  rw [Nat.mul_assoc] at hRad ⊢
  omega

/-- Extract a single exponent and threshold from a length envelope before
choosing the width. The polynomial degree in the width is fixed. -/
theorem exists_uniform_clock {a : ℕ → ℕ} (ha : PolynomiallyBounded a) :
    ∃ c N : ℕ, ∀ n ≥ N, ∀ Z : ℕ, 2^(6*a n+23)*(Z+1)^4 ≤ 2^(n^c)*(Z+1)^4 := by
  obtain ⟨m,d,N,hm⟩ := (((PolynomiallyBounded.const 6).mul ha).add (.const 23))
  refine ⟨d+1,max m N,fun n hn Z ↦ Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) ?_)⟩
  calc
    6*a n+23 ≤ m*n^d := hm n ((le_max_right ..).trans hn)
    _ ≤ n*n^d := Nat.mul_le_mul_right _ ((le_max_left ..).trans hn)
    _ = n^(d+1) := by rw [pow_succ, Nat.mul_comm]

end Evaluator.MatrixCallbacks

end VPVNP
end Computability
end OAI
