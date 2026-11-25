import OAI.LinearAlgebra.SpectralBooks.SpectralExtension
import OAI.LinearAlgebra.SpectralBooks.ContractionPrice

/-!
# Price interpolation with two wires to a new site

A formal product records an old tensor, the numbers of copies of the two
new wires, and the number of copies of the full binary diagonal. Equal wire
counts give the products on which the contraction bound must be sharp.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace SiteTensor

variable {O T : Type*} [AddCommMonoid O] [AddCommMonoid T]

/-- Tensor product on the old tensors, with three independent copy counts. -/
abbrev IntervalMonomial (O : Type*) := O × ℕ × ℕ × ℕ

/-- Evaluate a formal product of an old tensor, two wires and a full diagonal. -/
def intervalEval (embed : O →+ T) (A B D : T) : IntervalMonomial O →+ T where
  toFun x := embed x.1 + x.2.1 • A + x.2.2.1 • B + x.2.2.2 • D
  map_zero' := by simp
  map_add' := by
    rintro ⟨x, m, n, k⟩ ⟨y, p, q, r⟩
    simp [add_nsmul]
    abel

/-- The target is additive, with prescribed prices on both new wires. -/
def intervalTarget (old : O →+ ℝ) (la lb : ℝ) : IntervalMonomial O →+ ℝ where
  toFun x := old x.1 + (x.2.1 : ℝ) * la + (x.2.2.1 : ℝ) * lb + (x.2.2.2 : ℝ)
  map_zero' := by simp
  map_add' := by
    rintro ⟨x, m, n, k⟩ ⟨y, p, q, r⟩
    simp [add_mul]
    ring

/-- Balanced products have the same number of copies of each wire. -/
def intervalBalanced (O : Type*) [AddCommMonoid O] : AddSubmonoid (IntervalMonomial O) where
  carrier := {x | x.2.1 = x.2.2.1}
  zero_mem' := rfl
  add_mem' := by
    rintro x y (hx : x.2.1 = x.2.2.1) (hy : y.2.1 = y.2.2.1)
    exact congrArg₂ (· + ·) hx hy

/-- Individual upper bounds and equality on balanced products determine both
wire prices, as well as the price on every embedded old tensor. -/
theorem interval_prices_of_balanced (embed : O →+ T) (A B D : T)
    (old : O →+ ℝ) (la lb : ℝ) (price : T →+ ℝ)
    (upper : ∀ x, price (intervalEval embed A B D x) ≤ intervalTarget old la lb x)
    (exactOn : ∀ x ∈ intervalBalanced O,
      price (intervalEval embed A B D x) = intervalTarget old la lb x) :
    (∀ X, price (embed X) = old X) ∧ price A = la ∧ price B = lb := by
  refine ⟨fun X ↦ ?_, ?_⟩
  · simpa [intervalEval, intervalTarget] using exactOn (X, 0, 0, 0) rfl
  have ha : price A ≤ la := by
    simpa [intervalEval, intervalTarget] using upper (0, 1, 0, 0)
  have hb : price B ≤ lb := by
    simpa [intervalEval, intervalTarget] using upper (0, 0, 1, 0)
  have hab : price A + price B = la + lb := by
    simpa [intervalEval, intervalTarget] using exactOn (0, 1, 1, 0) rfl
  constructor <;> linarith

universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]

/-- If the maximum old price obtained by contracting a product is bounded by
the smaller wire supply and is attained for equal supplies, a single normalized
spectral point preserves the old prices and splits the wire price in the
prescribed proportions. The full binary diagonal fixes its scale. -/
theorem spectral_interval_of_contraction_formula
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
    (embed : NonzeroProduct.{v} I K →+ NonzeroProduct.{v} (Option I) K)
    (A B D : NonzeroProduct.{v} (Option I) K) (hD : classOfProduct D = 2)
    (la lb : ℝ) (ha : 0 ≤ la) (hb : 0 ≤ lb)
    (upper : ∀ X (m n k : ℕ),
      classContractionPrice φ (classOfProduct (intervalEval embed A B D (X, m, n, k))) ≤
        logPoint φ X + (min m n : ℕ) * (la + lb) + (k : ℝ))
    (sharp : ∀ X (m k : ℕ),
      logPoint φ X + (m : ℝ) * (la + lb) + (k : ℝ) ≤
        classContractionPrice φ (classOfProduct (intervalEval embed A B D (X, m, m, k)))) :
    ∃ f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} (Option I) K → _ → Prop),
      (∀ X, logPoint f (embed X) = logPoint φ X) ∧ logPoint f A = la ∧ logPoint f B = lb := by
  let eval := intervalEval embed A B D
  let target := intervalTarget (logPoint φ) la lb
  let G := intervalBalanced (NonzeroProduct.{v} I K)
  let u : IntervalMonomial (NonzeroProduct.{v} I K) := (0, 0, 0, 1)
  have upper' (x) : classContractionPrice φ (classOfProduct (eval x)) ≤ target x := by
    obtain ⟨X, m, n, k⟩ := x
    refine (upper X m n k).trans ?_
    have hm : ((min m n : ℕ) : ℝ) ≤ m := by exact_mod_cast min_le_left m n
    have hn : ((min m n : ℕ) : ℝ) ≤ n := by exact_mod_cast min_le_right m n
    change _ ≤ logPoint φ X + (m : ℝ) * la + (n : ℝ) * lb + (k : ℝ)
    rw [mul_add]
    linarith [mul_le_mul_of_nonneg_right hm ha, mul_le_mul_of_nonneg_right hn hb]
  have sharp' (x) (hx : x ∈ G) : target x ≤ classContractionPrice φ (classOfProduct (eval x)) := by
    obtain ⟨X, m, n, k⟩ := x
    change m = n at hx
    subst n
    simpa [target, intervalTarget, eval, mul_add, add_assoc] using sharp X m k
  have nneg (x) : 0 ≤ target x := by
    change 0 ≤ logPoint φ x.1 + _ * la + _ * lb + _
    have := spectralLogHom_nonneg unit_le_nonzeroClass φ x.1
    positivity
  have normalized (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} (Option I) K → _ → Prop)) :
      logPoint f (eval u) = 1 := by
    have h : eval u = D := by simp [eval, u, intervalEval]
    rw [h]
    change Real.logb 2 (f.val (classOfProduct D) : ℝ) = 1
    rw [hD, show f.val 2 = 2 from map_ofNat (normalizedSpectrum.toRingHom f) 2]
    exact Real.logb_self_eq_one (by norm_num)
  obtain ⟨f, hf, hG⟩ := spectral_extension_of_contraction_bounds eval target G
    (fun x ↦ classContractionPrice φ (classOfProduct x))
    (fun h ↦ classContractionPrice_mono φ h) upper' sharp' nneg
    (classContractionPrice_ordinary_sum φ) u rfl (by simp [target, intervalTarget, u]) normalized
  exact ⟨f, interval_prices_of_balanced embed A B D (logPoint φ) la lb (logPoint f) hf hG⟩

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
