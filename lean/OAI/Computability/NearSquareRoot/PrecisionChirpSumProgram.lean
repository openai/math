import OAI.Computability.NearSquareRoot.PrecisionChirpTable
import OAI.Computability.NearSquareRoot.PrecisionInvSqrtWord
import OAI.Computability.NearSquareRoot.PrecisionChirpAccumulator

/-! # Summation and scaling of fixed-point chirp rows

The P192 regime supplies each local parameter on a descriptor tape. The setup
programs below enumerate all the root words for one coefficient, sum their
signed numerators, compute a reciprocal square root, and multiply and truncate
before storing a finite output record.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChirpTable

open IntegerMultiplication Code Strip Staff Carry Dusk Grid FixedPoint

attribute [local irreducible] Nat.clog

set_option maxHeartbeats 2000000

variable {J : Type} {s : Regime J} {a target : J → ℕ}

/-- All values in the Bluestein multiplier table have modulus at most 40.
Six integer bits suffice for its approximate coefficients and for the
unit-modulus spectrum. -/
def sumWidth (a target : ℕ) := sumPrecision a target + 6

theorem sumPrecision_realizes (A : Realizes s a) (P : Realizes s target) :
    Realizes s (fun i => sumPrecision (a i) (target i)) :=
  (P.plus (Figure.of_spoken A).short_log).plus (.fix 5)

theorem sumWidth_realizes (A : Realizes s a) (P : Realizes s target) :
    Realizes s (fun i => sumWidth (a i) (target i)) :=
  (sumPrecision_realizes A P).plus (.fix 6)

theorem root_headroom (a target : ℕ) :
    (2:ℝ)*2^sumPrecision a target+2 < 2^sumWidth a target := by
  unfold sumWidth
  rw [pow_add]
  have h : (1 : ℝ) ≤ 2^sumPrecision a target := one_le_pow₀ (by norm_num)
  nlinarith

attribute [local irreducible] sumWidth sumPrecision

private theorem packageWords {p w : J → ℕ} (W : Realizes s w)
    (x : J → Grid.Coef) (X : s.Has x) (z : J → ℂ) (δ : J → ℝ)
    (approx : ∀ i, ‖toC (content (x i)) / 2^p i - z i‖ ≤ δ i)
    (headroom : ∀ i, (‖z i‖ + δ i) * 2^p i < 2^w i) :
    ∃ v : (i : J) → Grain (w i), s.Has (fun i => mark (k := w i) (v i)) ∧
      ∀ i, ‖meaning (p i) (w i) (v i) - z i‖ ≤ δ i := by
  have hfit (i) : focus (w i) (content (x i)) := by
    apply short _ (into _)
    have h := norm_add_le (toC (content (x i)) / (2:ℂ)^p i - z i) (z i)
    rw [sub_add_cancel, norm_div, norm_pow, show ‖(2:ℂ)‖ = (2:ℝ) by norm_num] at h
    have hp : (0:ℝ) < 2^p i := by positivity
    apply lt_of_le_of_lt _ (headroom i)
    apply (div_le_iff₀ hp).mp
    linarith [approx i]
  have hfit' (i) : focus (w i + 1) (content (x i)) := by
    have h : (2 : ℤ)^w i ≤ 2^(w i+1) := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    exact ⟨(hfit i).1.trans_le h, (hfit i).2.trans_le h⟩
  let v (i : J) := wrapMap (w i) (content (x i))
  refine ⟨v, ?_, ?_⟩
  · have eq (i) : mark (v i) = Grid.spell (Grid.fit (tally (w i+1), x i)) := by
      rw [Grid.spellG _ (Grid.fit_r ..), Grid.fit_small _ _ (hfit' i)]
    simp_rw [eq]
    exact (Regime.Has.pair (g:=fun i=>tally (w i+1)) (W.plus (.fix 1)) X).ez
      (Grid.fit_easy.compose Grid.spell_easy)
  · intro i
    simpa [meaning, v, recovers _ (hfit i)] using approx i

/-- Compose the short root generator with exact signed summation and dyadic
inverse-square-root scaling. A single P192 `Has` witness computes every value
of the resulting family from its finite descriptor. -/
theorem prepareNormalizedSum {n : J → ℕ} (A : Realizes s a) (P : Realizes s target)
    (ha : ∀ i, 0 < a i)
    (B : (i : J) → Fin (n i) → Grain (sumWidth (a i) (target i)))
    (built : s.Has (fun i => List.ofFn fun j => mark (k := sumWidth (a i) (target i)) (B i j)))
    (z : J → ℂ) (zbound : ∀ i, ‖z i‖ ≤ 40)
    (recover : ∀ i (q : ℝ) (output : ℂ),
      |q - (Real.sqrt (a i))⁻¹| ≤ 1/(2:ℝ)^sumPrecision (a i) (target i) →
      ‖output - (q:ℂ) * ∑ j, meaning (sumPrecision (a i) (target i)) (sumWidth (a i) (target i)) (B i j)‖ ≤
        2/(2:ℝ)^sumPrecision (a i) (target i) →
      ‖output - z i‖ ≤ 1/(2:ℝ)^target i) :
    ∃ v : (i : J) → Grain (sumWidth (a i) (target i)), s.Has (fun i => mark (k := sumWidth (a i) (target i)) (v i)) ∧
      ∀ i, ‖meaning (sumPrecision (a i) (target i)) (sumWidth (a i) (target i)) (v i) - z i‖ ≤ 1/(2:ℝ)^target i := by
  let p i := sumPrecision (a i) (target i)
  let w i := sumWidth (a i) (target i)
  have hp : Realizes s p := sumPrecision_realizes A P
  have hw : Realizes s w := sumWidth_realizes A P
  obtain ⟨aw,haw,aeq⟩ := Figure.of_spoken A
  let sw i := invSqrtNumeratorWord (tally (p i), aw i)
  have hsw : s.Has sw := (Regime.Has.pair (g:=fun i => tally (p i)) hp haw).thenDo invSqrtNumeratorWord_poly
  have hsval (i) : Bits.value (sw i) = invSqrtNumerator (a i) (p i) := by
    simpa [sw,aeq] using (invSqrtNumeratorWord_spec (tally (p i)) (aw i)).2
  let out i := shiftedRootWords (tally (p i), sw i, List.ofFn (fun j => mark (k := sumWidth (a i) (target i)) (B i j)))
  have hout : s.Has out := (Regime.Has.pair (g:=fun i => tally (p i)) hp (hsw.pair built)).thenDo
    shiftedRootWords_poly
  have hacc (i) : ‖toC (content (out i)) / (2:ℂ)^p i - z i‖ ≤ 1/(2:ℝ)^target i := by
    refine recover i ((Bits.value (sw i):ℝ) / 2^p i) _ ?_ ?_
    · rw [hsval]
      exact (invSqrtNumerator_error (ha i) (p i)).le
    · have he := shiftedRootWords_error (p i) (p i) (sw i) (List.ofFn (B i))
      simpa [out, List.map_ofFn, List.sum_ofFn, Function.comp_def, Complex.ofReal_div] using he
  have room (i) : (‖z i‖ + 1/(2:ℝ)^target i) * (2:ℝ)^p i < 2^w i := by
    have hδ : (1:ℝ)/2^target i ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
    have he : ‖z i‖ + 1/(2:ℝ)^target i < 2^6 := by linarith [zbound i]
    rw [show w i = p i + 6 by unfold w sumWidth; rfl]
    rw [pow_add, mul_comm]
    exact mul_lt_mul_of_pos_left he (by positivity)
  exact packageWords (s:=s) (p := p) (w := w) hw out hout z (fun i => 1/(2:ℝ)^target i) hacc room

end ChirpTable

end NearSquareRoot
end Computability
end OAI
