import OAI.Computability.VPVNP.LiveEvaluatorAdviceDistribution
import OAI.Computability.VPVNP.EvaluatorNativeResources
import OAI.Computability.VPVNP.CursorBounds
import OAI.Computability.VPVNP.RAMClock

/-!
# Choosing the live advice exponents before the address multiplier

The raw evaluator prefix and the number of labels have bounds independent
of the processor geometry. For each fixed address multiplier the quartic
word width eventually fits in the input length. Thus one pair of exponents
suffices for the raw prefix capacity and the entire distributed advice
array for every later choice of multiplier.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.Advice

open Filter BurstRAM LiveEvaluatorAdviceBanks

theorem eventually_power {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    ∃ d : ℕ, ∀ᶠ n : ℕ in atTop, f n ≤ n^d := by
  obtain ⟨A, k, N, bound⟩ := hf
  refine ⟨k+1, ?_⟩
  filter_upwards [eventually_ge_atTop A, eventually_ge_atTop N] with n ha hn
  rw [pow_succ, Nat.mul_comm]
  exact (bound n hn).trans (Nat.mul_le_mul_right _ ha)

private theorem eventually_word_le (B : ℕ) : ∀ᶠ n : ℕ in atTop, CursorBounds.wordBits B n ≤ n := by
  filter_upwards [eventually_word_stage_le B 0] with n h
  exact (h (addressWidth B n) 0 (Nat.mul_le_mul_left B (clog_le_log2_succ n)) (by simp)).1

/-- The exponents are uniform in the address multiplier. The first capacity
bounds the actual raw input, and the second bounds the length word, the
padded raw region and the serialized ordinal table together. -/
theorem capacity_exponents {rawLength labels : ℕ → ℕ} (hr : PolynomiallyBounded rawLength)
    (ht : PolynomiallyBounded labels) :
    ∃ dA d₁ : ℕ, ∀ B : ℕ, ∀ᶠ n : ℕ in atTop,
      rawLength n ≤ n^dA ∧ CursorBounds.wordBits B n + n^dA + labels n * Nat.clog 2 (labels n) ≤ n^d₁ := by
  obtain ⟨dA, hA⟩ := eventually_power hr
  have hc : PolynomiallyBounded (fun n => Nat.clog 2 (labels n)) :=
    ht.of_le fun _ => Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  obtain ⟨d₁, h₁⟩ := eventually_power ((PolynomiallyBounded.id.add (PolynomiallyBounded.id.pow dA)).add (ht.mul hc))
  refine ⟨dA, d₁, fun B => ?_⟩
  filter_upwards [hA, h₁, eventually_word_le B] with n raw total width
  exact ⟨raw, (Nat.add_le_add_right (Nat.add_le_add_right width _) _).trans total⟩

/-- The canonical distributed tape includes exactly the remaining number
of zero padding cells after the ordinal table. -/
def adviceTape {t ordW : ℕ} (w cap size : ℕ) (raw : List Bool) (values : Fin t → Word ordW) : Fin size → Bool :=
  let padding := size - (w + cap + t*ordW)
  fun i => (distribution w cap raw values padding)[i.val]?.getD false

theorem adviceTape_words {t ordW : ℕ} (w cap size : ℕ) (raw : List Bool) (values : Fin t → Word ordW)
    (hr : raw.length ≤ cap) (hs : w + cap + t*ordW ≤ size) :
    List.ofFn (adviceTape w cap size raw values) =
      distribution w cap raw values (size - (w + cap + t*ordW)) := by
  have hlen : (distribution w cap raw values (size - (w + cap + t*ordW))).length = size := by
    rw [distribution_length cap _ raw values hr]
    omega
  apply List.ext_getElem (by rw [List.length_ofFn, hlen])
  intro i hi hj
  simp [adviceTape, List.getElem?_eq_getElem hj]

/-- The same exponents also give a canonical advice tape of exactly the
prescribed size for every possible raw string and ordinal table within
the uniform bounds. -/
theorem adviceTape_eventually {bound labels : ℕ → ℕ} (hb : PolynomiallyBounded bound)
    (ht : PolynomiallyBounded labels) :
    ∃ dA d₁ : ℕ, ∀ B : ℕ, ∀ᶠ n : ℕ in atTop,
      let w := CursorBounds.wordBits B n
      let t := labels n
      let o := Nat.clog 2 t
      ∀ (raw : List Bool) (values : Fin t → Word o), raw.length ≤ bound n →
        raw.length ≤ n^dA ∧ w + n^dA + t*o ≤ n^d₁ ∧
        List.ofFn (adviceTape w (n^dA) (n^d₁) raw values) =
          distribution w (n^dA) raw values (n^d₁ - (w + n^dA + t*o)) := by
  obtain ⟨dA, d₁, h⟩ := capacity_exponents hb ht
  refine ⟨dA, d₁, fun B => ?_⟩
  filter_upwards [h B] with n hn
  intro w t o raw values hr
  exact ⟨hr.trans hn.1, hn.2, adviceTape_words w _ _ raw values (hr.trans hn.1) hn.2⟩

/-- The raw capacity can be chosen once for the native evaluator's actual
bit-stack advice, uniformly over its endpoint, stack contents and divisor
whenever the divisor length and the payload bank satisfy the stated envelopes. -/
theorem native_capacity_exponents (fields : ℕ) {labels divisorBits footprint : ℕ → ℕ}
    (ht : PolynomiallyBounded labels) (hd : PolynomiallyBounded divisorBits)
    (hf : PolynomiallyBounded footprint) :
    ∃ dA d₁ : ℕ, ∀ B : ℕ, ∀ᶠ n : ℕ in atTop,
      Evaluator.MatrixCallbacks.adviceCap fields (labels n) (divisorBits n) (footprint n) ≤ n^dA ∧
      CursorBounds.wordBits B n + n^dA + labels n * Nat.clog 2 (labels n) ≤ n^d₁ :=
  capacity_exponents (Evaluator.MatrixCallbacks.adviceCap_polynomial fields ht hd hf) ht

open Evaluator RAMTape SliceArithmetic

/-- Applying a single native capacity bound to the concrete advice payload.
The field, basis coordinates and endpoint may vary without changing the bound. -/
theorem native_raw_fits {P : Type} {p e ew v t fields divisorBits footprint cap : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Algebra (ZMod p) K] {c : Vector p e}
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (dim : Word v) (extra : Stacks P) (d : List Bool)
    (extraSpace : ℕ) (hextra : ∀ k, (extra k).length ≤ extraSpace) (ps : List (WeightedStep.Port P))
    (s : Fin dim.val × K) (hps : ps.length ≤ fields) (hd : d.length ≤ divisorBits)
    (hroom : WeightedStep.bankSpace v e ew extraSpace ≤ footprint)
    (hcap : MatrixCallbacks.adviceCap fields t divisorBits footprint ≤ cap) :
    (EvaluatorProgramRawInput.advice ps t d (MatrixCallbacks.payload φ dim extra ew s)).length ≤ cap := by
  apply (MatrixCallbacks.advice_le (w := ew) (t := t) φ dim extra d extraSpace hextra ps s).trans
  apply le_trans _ hcap
  unfold MatrixCallbacks.adviceCap
  gcongr

end LiveProgram.Advice

end VPVNP
end Computability
end OAI
