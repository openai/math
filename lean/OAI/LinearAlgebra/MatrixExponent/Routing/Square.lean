import OAI.LinearAlgebra.MatrixExponent.Routing.Dual
import OAI.LinearAlgebra.MatrixExponent.Valued.Shared

/-! # Stable sorting under a strict square saving -/

namespace OAI.LinearAlgebra.MatrixExponent

variable {F : Type} [Field F] [Finite F]

theorem wide_of_saving (h : omega F < 9 / 4) : Radix.WideTag F :=
  Routing.wide_of_shared_price (shared_of_saving h)

theorem short_of_saving (h : omega F < 9 / 4) :
    ∃ p : ℝ, 1 < p ∧ p < 2 ∧ Lookup.ShortTag F p :=
  Radix.short_of_wide (wide_of_saving h)

theorem sorting_of_saving (h : omega F < 9 / 4) :
    ∃ p : ℝ, 1 < p ∧ p < 2 ∧ Lookup.Sorting F p :=
  Routing.sorting_of_shared_price (shared_of_saving h)

namespace Routing

omit [Finite F] in
private theorem SortingBound.mono {h w : ℕ} {a b : ℝ}
    (ha : SortingBound F h w a) (hab : a ≤ b) : SortingBound F h w b := by
  obtain ⟨⟨m, ht, hm⟩, h⟩ := ha
  refine ⟨⟨m, ht, hm.trans hab⟩, fun k e => ?_⟩
  obtain ⟨n, hs, hn⟩ := h k e
  exact ⟨n, hs, hn.trans hab⟩

/-- Theorem 3.1 for a fixed finite field, including stable ties, arbitrary
ordered key bits, all bounded multiples of the height, and wide records. -/
theorem conditional_sorting (F : Type) [Field F] [Finite F] (hs : omega F < 9 / 4) :
    (∃ p : ℝ, 1 < p ∧ p < 2 ∧ ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ h w : ℕ, 1 ≤ h → w ≤ k * h → SortingBound F h w (C * (2 : ℝ) ^ h * (h : ℝ) ^ p)) ∧
    (∀ ζ : ℝ, 0 < ζ → ∃ A : ℕ, 1 < A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ h w : ℕ, 1 ≤ h → h ^ A ≤ w → SortingBound F h w (C * (2 : ℝ) ^ h * w * (h : ℝ) ^ ζ)) := by
  constructor
  · obtain ⟨p, hp, hp', C, ht⟩ := short_of_saving hs
    refine ⟨p, hp, hp', fun k => ?_⟩
    let K := 2 + 2 * k
    have hk : 1 ≤ K := by unfold K; omega
    refine ⟨(8*|C|+3000400) * K, by positivity, fun h w hh hw => ?_⟩
    obtain ⟨m, hm, hcost⟩ := ht h hh
    obtain ⟨n, hn, hb⟩ := Radix.widen hh le_rfl (show h ≤ K * h by nlinarith) hm
    have hW : 1 + h + 2 * w ≤ K * h := by unfold K; linarith
    have hN : n ≤ 2 * K * m + 100 * 2 ^ h * (K * h) := by
      refine Nat.le_of_mul_le_mul_right ?_ hh
      convert hb using 1
      ring
    have hn' : (n : ℝ) ≤ 2 * K * m + 100 * (2 : ℝ) ^ h * (K * h) := by exact_mod_cast hN
    have hh' : (h : ℝ) ≤ (h : ℝ) ^ p := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hh : 1 ≤ (h : ℝ)) hp.le
    have hcost' : (m : ℝ) ≤ |C| * (2 : ℝ) ^ h * (h : ℝ) ^ p := by
      refine hcost.trans ?_
      gcongr
      exact le_abs_self _
    refine (sorting_bound hn hW).mono ?_
    push_cast
    linarith only [hn', mul_le_mul_of_nonneg_left hcost' (Nat.cast_nonneg K),
      mul_le_mul_of_nonneg_left hh' (show 0 ≤ (K : ℝ) * (2 : ℝ) ^ h by positivity)]
  · intro ζ hζ
    obtain ⟨A, hA, C, ht⟩ := wide_of_saving hs ζ hζ
    refine ⟨A, hA, 16*|C|+12000000, by positivity, fun h w hh hw => ?_⟩
    have hl := (Nat.le_self_pow (by omega : A ≠ 0) h).trans hw
    obtain ⟨m, hm, hcost⟩ := ht h (4 * w) hh (by omega)
    refine (sorting_bound hm (by omega : 1 + h + 2 * w ≤ 4 * w)).mono ?_
    have hh' : 1 ≤ (h : ℝ) ^ ζ := Real.one_le_rpow (by exact_mod_cast hh) hζ.le
    have hcost' : (m : ℝ) ≤ |C| * (2 : ℝ) ^ h * (4 * w) * (h : ℝ) ^ ζ := by
      push_cast at hcost
      refine hcost.trans ?_
      gcongr
      exact le_abs_self _
    push_cast
    linarith only [hcost', mul_le_mul_of_nonneg_left hh' (show 0 ≤ (2 : ℝ) ^ h * w by positivity)]

end Routing
end OAI.LinearAlgebra.MatrixExponent
