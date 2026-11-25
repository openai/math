import OAI.LinearAlgebra.SpectralBooks.DivisionModel
import OAI.LinearAlgebra.SpectralBooks.RationalDerivative

/-! # Tensor rank from straight-line circuits with division

Formal mixed partial derivatives of all registers lie in one shared span of products
of first derivatives. For a quotient register `h = p / q`, we differentiate `h * q = p`.
Since the divisor is nonzero as a rational function, we can solve for the mixed partial
of `h` over the fraction field, adding two products.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic Foundation MvPolynomial
open scoped BigOperators

noncomputable section

variable {K A B : Type*} [Field K]

/-- All coefficients of a mixed derivative are obtained by recombining a common
family of products indexed by the nonlinear gates seen so far. -/
private def HasExpansion {n : ℕ} (u : Fin n → A → K) (v : Fin n → B → K)
    (H : A → B → K) : Prop :=
  ∃ c : Fin n → K, ∀ x y, H x y = ∑ t, u t x * v t y * c t

private theorem hasExpansion_zero {n : ℕ} (u : Fin n → A → K) (v : Fin n → B → K) :
    HasExpansion u v 0 :=
  ⟨0, by simp⟩

private theorem hasExpansion_add {n : ℕ} {u : Fin n → A → K} {v : Fin n → B → K}
    {H G : A → B → K} (hH : HasExpansion u v H) (hG : HasExpansion u v G) :
    HasExpansion u v (H + G) := by
  obtain ⟨c, hc⟩ := hH
  obtain ⟨d, hd⟩ := hG
  exact ⟨c + d, by simp [Pi.add_apply, mul_add, Finset.sum_add_distrib, hc, hd]⟩

private theorem hasExpansion_sub {n : ℕ} {u : Fin n → A → K} {v : Fin n → B → K}
    {H G : A → B → K} (hH : HasExpansion u v H) (hG : HasExpansion u v G) :
    HasExpansion u v (H - G) := by
  obtain ⟨c, hc⟩ := hH
  obtain ⟨d, hd⟩ := hG
  exact ⟨c - d, by simp [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, hc, hd]⟩

private theorem hasExpansion_insert {n : ℕ} {u : Fin n → A → K} {v : Fin n → B → K}
    {H : A → B → K} (hH : HasExpansion u v H) (a : A → K) (b : B → K) :
    HasExpansion (Fin.cons a u) (Fin.cons b v) H := by
  obtain ⟨c, hc⟩ := hH
  exact ⟨Fin.cons 0 c, by simp [Fin.sum_univ_succ, hc]⟩

private theorem hasExpansion_twoProducts {n : ℕ} {u : Fin n → A → K} {v : Fin n → B → K}
    {H G T : A → B → K} (hH : HasExpansion u v H) (hG : HasExpansion u v G)
    (a a' : A → K) (b b' : B → K) (s t w : K)
    (h : ∀ x y, T x y = s * H x y + t * G x y + w * (a x * b y + a' x * b' y)) :
    HasExpansion (Fin.cons a (Fin.cons a' u)) (Fin.cons b (Fin.cons b' v)) T := by
  obtain ⟨c, hc⟩ := hH
  obtain ⟨d, hd⟩ := hG
  refine ⟨Fin.cons w (Fin.cons w (fun j => s * c j + t * d j)), fun x y => ?_⟩
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, h, hc, hd, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf

variable {F : Type*} [Field F]

private abbrev RatInputs (F A B : Type*) [Field F] := FractionRing (MvPolynomial (A ⊕ B) F)

private def leftDerivative (p : RatInputs F A B) (x : A) := ratPartial (.inl x) p

private def rightDerivative (p : RatInputs F A B) (y : B) := ratPartial (.inr y) p

private theorem expansion_mul {n : ℕ} {u : Fin n → A → RatInputs F A B}
    {v : Fin n → B → RatInputs F A B} {p q : RatInputs F A B}
    (hp : HasExpansion u v (ratMixed p)) (hq : HasExpansion u v (ratMixed q)) :
    HasExpansion (Fin.cons (leftDerivative p) (Fin.cons (leftDerivative q) u))
      (Fin.cons (rightDerivative q) (Fin.cons (rightDerivative p) v)) (ratMixed (p * q)) := by
  apply hasExpansion_twoProducts hp hq _ _ _ _ q p 1
  intro x y
  rw [ratMixed_mul]
  simp only [leftDerivative, rightDerivative, one_mul]
  abel

private theorem expansion_quot {n : ℕ} {u : Fin n → A → RatInputs F A B}
    {v : Fin n → B → RatInputs F A B} {p q : RatInputs F A B}
    (hp : HasExpansion u v (ratMixed p)) (hq : HasExpansion u v (ratMixed q)) (hne : q ≠ 0) :
    HasExpansion (Fin.cons (leftDerivative (p / q)) (Fin.cons (leftDerivative q) u))
      (Fin.cons (rightDerivative q) (Fin.cons (rightDerivative (p / q)) v)) (ratMixed (p / q)) := by
  apply hasExpansion_twoProducts hp hq _ _ _ _ q⁻¹ (-(q⁻¹ * (p / q))) (-q⁻¹)
  intro x y
  have h := ratMixed_mul (p / q) q x y
  rw [div_mul_cancel₀ _ hne] at h
  rw [h]
  simp only [leftDerivative, rightDerivative]
  field_simp
  ring

private theorem rationalRegisterProducts {r : ℕ} (p : RationalProgram F (A ⊕ B) r)
    (h : p.Valid) :
    ∃ (u : Fin (2 * p.productQuotientCount) → A → RatInputs F A B)
      (v : Fin (2 * p.productQuotientCount) → B → RatInputs F A B),
      ∀ i, HasExpansion u v (ratMixed (p.value i)) := by
  induction p with
  | nil => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0⟩
  | step p g ih =>
    obtain ⟨u, v, huv⟩ := ih h
    cases g with
    | constant z =>
      simp only [RationalProgram.productQuotientCount]
      refine ⟨u, v, Fin.cases ?_ huv⟩
      simpa [HasExpansion, RationalProgram.value, RationalProgram.gateValue] using hasExpansion_zero u v
    | input i =>
      simp only [RationalProgram.productQuotientCount]
      refine ⟨u, v, Fin.cases ?_ huv⟩
      simpa [HasExpansion, RationalProgram.value, RationalProgram.gateValue] using hasExpansion_zero u v
    | add i j =>
      simp only [RationalProgram.productQuotientCount]
      refine ⟨u, v, Fin.cases ?_ huv⟩
      simpa [HasExpansion, RationalProgram.value, RationalProgram.gateValue] using hasExpansion_add (huv i) (huv j)
    | sub i j =>
      simp only [RationalProgram.productQuotientCount]
      refine ⟨u, v, Fin.cases ?_ huv⟩
      simpa [HasExpansion, RationalProgram.value, RationalProgram.gateValue] using hasExpansion_sub (huv i) (huv j)
    | mul i j =>
      simp only [RationalProgram.productQuotientCount]
      refine ⟨_, _, Fin.cases (expansion_mul (huv i) (huv j)) (fun k => ?_)⟩
      exact hasExpansion_insert (hasExpansion_insert (huv k) _ _) _ _
  | quot p i j ih =>
    obtain ⟨u, v, huv⟩ := ih h.1
    simp only [RationalProgram.productQuotientCount]
    refine ⟨_, _, Fin.cases (expansion_quot (huv i) (huv j) h.2) (fun k => ?_)⟩
    exact hasExpansion_insert (hasExpansion_insert (huv k) _ _) _ _

/-- The generic-input rank is at most twice the total number of products and
quotients in a correct straight-line algorithm over any ground field. -/
theorem matrixTensor_rank_le_twice_productQuotientCount {a b c : ℕ}
    {P : RationalMatrixAlgorithm F a b c} (h : P.Correct) :
    tensorRank (matrixTensor (FractionRing (MvPolynomial (MatrixInput a b c) F)) b c a) ≤
      2 * P.program.productQuotientCount := by
  classical
  obtain ⟨u, v, huv⟩ := rationalRegisterProducts P.program h.1
  choose w hw using huv
  apply tensorRank_le_of_rankAtMost
  refine ⟨u, v, fun t z => w (P.output z.2 z.1) t, ?_⟩
  funext x y z
  have hout := hw (P.output z.2 z.1) x y
  rw [h.2, map_sum] at hout
  simp only [map_mul, ratMixed_matrixEntry] at hout
  exact hout

/-- A total arithmetic operation bound also controls the generic-input tensor rank. -/
theorem matrixTensor_rank_le_twice_rationalCost {a b c : ℕ} {P : RationalMatrixAlgorithm F a b c}
    (h : P.Correct) :
    tensorRank (matrixTensor (FractionRing (MvPolynomial (MatrixInput a b c) F)) b c a) ≤
      2 * P.cost :=
  (matrixTensor_rank_le_twice_productQuotientCount h).trans
    (Nat.mul_le_mul_left 2 (P.program.productQuotientCount_le_cost))

end

end SpectralBooks
end LinearAlgebra
end OAI
