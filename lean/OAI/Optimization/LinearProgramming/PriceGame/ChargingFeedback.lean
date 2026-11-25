import OAI.Optimization.LinearProgramming.PriceGame.StatesOracle
import OAI.Optimization.LinearProgramming.PriceGame.ChargingTrial

/-! # Feedback from a successful child at a trial probe

The inherited state controls every nonnegative surplus. A strictly positive pivot
controls every surplus at least as large as its own. Inputs to the query at a tie
are the mapped prices and the designated coordinate. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging

open States

/-- Signed baseline shortfall before changing the shift. -/
def probeSurplus {I : Type*} (P y : I → ℚ) (h : Bool) (t : ℚ) (i : I) : ℚ :=
  P i - t - signed h (y i)

/-- The new shift depends on the selected pivot and the actual probe prices. -/
def pivotShift {I : Type*} (P y : I → ℚ) (h : Bool) (i : I) : ℚ := P i - signed h (y i)

/-- Trial misses use the price threshold expressed in the price's original sign. -/
theorem misses_iff_positive_surplus {I : Type*} (P y : I → ℚ) (h : Bool) (t : ℚ) (i : I) :
    misses h (signed h (P i - t)) (y i) = true ↔ 0 < probeSurplus P y h t i := by
  cases h <;> simp [misses, probeSurplus, signed]
  constructor <;> intro hlt <;> linarith

/-- An active child state's description in the charging proof, with public
baseline `y`. There are no extra obligations on inactive parent coordinates. -/
def childPass {I : Type*} (S : I → Prop) (P y : I → ℚ) (h : Bool)
    (shift : ℚ) (x : I × Bool → ℚ) : Prop :=
  Succeeds (childActive S P y h shift) (fun q => P q.1) x h shift

/-- The feedback labels actually supplied by the two comparisons and any
designated tie answer. -/
def probeFeedback {I : Type*} (y : I → ℚ) (x : I × Bool → ℚ) (answer : I → Bool)
    (i : I) : Bool := feedback (y i) (parentPrices y x i) (answer i)

private theorem eligible_feedback {I : Type*} {S : I → Prop} {P y : I → ℚ} {h : Bool}
    {t t' : ℚ} {x : I × Bool → ℚ} {answer : I → Bool}
    (hs : t ≤ t') (win : childPass S P y h t' x)
    (valid : ∀ i, y i = parentPrices y x i → Extreme S P (parentPrices y x) h t i → answer i = h)
    {i : I} (hi : S i) (good : signed h (y i) ≤ P i - t') : probeFeedback y x answer i = h := by
  let a (j : I) := if y j = parentPrices y x j then answer j else h
  have hc := (succeeds_feedback hs win a (fun j hext => by
    by_cases heq : y j = parentPrices y x j
    · simpa [a, heq] using valid j heq hext
    · simp [a, heq])).2 i hi good
  rcases lt_trichotomy (y i) (parentPrices y x i) with hlt | heq | hgt
  · simpa [probeFeedback, feedback, hlt] using hc
  · simpa [probeFeedback, a, heq] using hc
  · simpa [probeFeedback, feedback, hgt, not_lt_of_gt hgt] using hc

/-- Success with the inherited shift passes all mapped prices at their original
thresholds and supplies the true label at every nonnegative baseline surplus. -/
theorem inherited_feedback {I : Type*} {S : I → Prop} {P y : I → ℚ} {h : Bool}
    {t : ℚ} {x : I × Bool → ℚ} {answer : I → Bool}
    (win : childPass S P y h t x)
    (valid : ∀ i, y i = parentPrices y x i → Extreme S P (parentPrices y x) h t i → answer i = h) :
    Succeeds S P (parentPrices y x) h t ∧
      ∀ i, S i → 0 ≤ probeSurplus P y h t i → probeFeedback y x answer i = h := by
  refine ⟨succeeds_parent win, ?_⟩
  intro i hi hsur
  exact eligible_feedback le_rfl win valid hi (sub_nonneg.mp hsur)

/-- Success for a sampled pivot gives correct feedback on the entire upper
surplus set, including ties with the pivot. -/
theorem pivot_feedback {I : Type*} {S : I → Prop} {P y : I → ℚ} {h : Bool}
    {t : ℚ} {x : I × Bool → ℚ} {answer : I → Bool} {k : I}
    (hk : 0 ≤ probeSurplus P y h t k) (win : childPass S P y h (pivotShift P y h k) x)
    (valid : ∀ i, y i = parentPrices y x i → Extreme S P (parentPrices y x) h t i → answer i = h) :
    Succeeds S P (parentPrices y x) h (pivotShift P y h k) ∧
      ∀ i, S i → probeSurplus P y h t k ≤ probeSurplus P y h t i → probeFeedback y x answer i = h := by
  have hs : t ≤ pivotShift P y h k := by dsimp [pivotShift, probeSurplus] at *; linarith
  refine ⟨succeeds_parent win, ?_⟩
  intro i hi hsur
  apply eligible_feedback hs win valid hi
  dsimp only [pivotShift, probeSurplus] at *
  linarith

/-- The inherited success condition in the Boolean form used by the final-call
median count, with the threshold sign reversed at a negative hidden sign. -/
theorem inherited_mapped_prices_do_not_miss {I : Type*} {S : I → Prop} {P y : I → ℚ}
    {h : Bool} {t : ℚ} {x : I × Bool → ℚ} (win : childPass S P y h t x)
    {i : I} (hi : S i) : misses h (signed h (P i - t)) (parentPrices y x i) = false := by
  have hm := succeeds_parent win i hi
  cases h <;> simp [misses, signed] at hm ⊢ <;> linarith

/-- A transcript of the public one-designation queries yields the exact tie
premise used by `inherited_feedback` and `pivot_feedback`. -/
theorem designated_tie_valid {N R : ℕ} {anchor : Fin N} (hidden : Hidden N R anchor)
    {I : Type} {p : Path (Fin N) I} {S : I → Prop} {P y : I → ℚ} {t : ℚ}
    (reach : Reachable hidden.positive (priority hidden) (· ∈ hidden.active) p P S t)
    (x : I × Bool → ℚ) (a : I → Bool)
    (run : ∀ i, y i = parentPrices y x i →
      Tree.Reaches hidden (readDesignated p (parentPrices y x) i) (a i)) :
    ∀ i, y i = parentPrices y x i → Extreme S P (parentPrices y x) hidden.positive t i →
      a i = hidden.positive := by
  intro i heq hext
  exact readDesignated_correct hidden reach _ _ hext _ (run i heq)

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI
