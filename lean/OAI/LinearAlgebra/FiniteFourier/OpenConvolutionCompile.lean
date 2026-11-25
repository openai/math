import OAI.LinearAlgebra.FiniteFourier.ConvolutionCost
import OAI.LinearAlgebra.FiniteFourier.OpenConvolutionPolynomial
import OAI.LinearAlgebra.FiniteFourier.IntegralLinearCompile

/-! # Filling the child gates of an integral open convolution

The two copies of the input circuit run once. Each child arithmetic program
reads its two preprocessed blocks, and the output circuit collects the child
coefficients. Correctness for integral assignments implies the required formal
polynomial identity over the infinite integral domain of integers.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open MatrixMultiplication
open scoped BigOperators

namespace OpenConvolution

variable {B : Type*} [Fintype B] {n : ℕ} {len : B → ℕ}

/-- Gate budget for compiling a particular list of child multiplication programs. -/
theorem compile_integral (p : OpenConvolution ℤ n B len) (hp : p.RealizesMultiple 1)
    {r : B → ℕ} (P : ∀ b, Arithmetic.Program ℤ (Fin (len b) ⊕ Fin (len b)) (r b))
    (out : ∀ b, Fin (2 * len b - 1) → Fin (r b)) (hP : ∀ b, ComputesConvolution (P b) (out b)) :
    ∃ m, ∃ Q : Arithmetic.Program ℤ (Fin n ⊕ Fin n) m, ∃ result,
      ComputesConvolution Q result ∧
      Q.cost ≤ 3 * p.linearCost + 2 * (∑ b, len b) + (2 * n - 1) + ∑ b, (P b).cost := by
  classical
  let I := Fin n ⊕ Fin n
  let z₀ : Arithmetic.Program ℤ I 0 := .nil
  let input (i : I) (_ : Unit) (x : I → ℤ) := x i
  obtain ⟨r₀, Q₀, hc₀, _, h₀⟩ := intProgram_collect z₀ (fun _ : I => Unit) input (fun _ => 0)
    (fun i _ q _ => by
      obtain ⟨m, z, hc, hk, hv⟩ := intAvailable_input q i
      exact ⟨m, z, by omega, hk, fun _ => hv⟩)
  have hzero : Q₀.cost = 0 := by simpa [z₀, Arithmetic.Program.cost] using hc₀
  let left (x : I → ℤ) (i : Fin n) := x (.inl i)
  let right (x : I → ℤ) (i : Fin n) := x (.inr i)
  obtain ⟨_, L, hcL, hkL, hL⟩ := intCompileLinear Q₀ p.input left (fun i => h₀ (.inl i) ())
  -- Both operand arrays stay available while the child programs run.
  obtain ⟨_, R, hcR, hkR, hR⟩ := intCompileLinear L p.input right (fun i => hkL _ (h₀ (.inr i) ()))
  let childInputs (b : B) (x : I → ℤ) := Sum.elim
    (fun i => p.input.eval (left x) ⟨b, i⟩) (fun i => p.input.eval (right x) ⟨b, i⟩)
  let childrenAt (b : B) (k : Fin (2 * len b - 1)) (x : I → ℤ) :=
    p.children (left x) (right x) ⟨b, k⟩
  have build (b : B) {v : ℕ} (q : Arithmetic.Program ℤ I v)
      (keep : ∀ f, IntAvailable R f → IntAvailable q f) :
      ∃ m, ∃ z : Arithmetic.Program ℤ I m, z.cost ≤ q.cost + (P b).cost ∧
        (∀ f, IntAvailable q f → IntAvailable z f) ∧ ∀ k, IntAvailable z (childrenAt b k) := by
    have hy : ∀ i, IntAvailable q (fun x => childInputs b x i) := by
      rintro (i | i)
      · exact keep _ (hkR _ (hL ⟨b, i⟩))
      · exact keep _ (hR ⟨b, i⟩)
    obtain ⟨m, z, hc, hk, hv⟩ := intSimulateProgram q (P b) (childInputs b) hy
    refine ⟨m, z, hc, hk, fun k => ?_⟩
    have he (x : I → ℤ) : intRegisterValue (P b) (childInputs b x) (out b k) = childrenAt b k x := by
      rw [intRegisterValue, hP b k]
      exact eval_convolutionCoefficient_openConv ℤ _ _ _ k
    simpa only [he] using hv (out b k)
  obtain ⟨_, G, hcG, _, hG⟩ := intProgram_collect R _ childrenAt (fun b => (P b).cost) build
  obtain ⟨m, Q, hcQ, _, hQ⟩ := intCompileLinear G p.output (fun x => p.children (left x) (right x))
    (fun i => hG i.1 i.2)
  choose result hresult using hQ
  refine ⟨m, Q, result, ?_, ?_⟩
  · intro k
    apply MvPolynomial.funext
    intro x
    have hy : Sum.elim (left x) (right x) = x := by
      funext i
      cases i <;> rfl
    exact (hresult k x).trans ((hp (left x) (right x) k).trans <| by
      rw [one_mul, ← eval_convolutionCoefficient_openConv, hy])
  · simp only [Fintype.card_sigma, Fintype.card_fin] at hcL hcR hcQ
    unfold linearCost
    omega

/-- The recursive polynomial multiplication cost after filling the child slots with
minimum-cost integral programs. -/
theorem integralConvolutionCost_le (p : OpenConvolution ℤ n B len) (hp : p.RealizesMultiple 1) :
    integralConvolutionCost n ≤
      3 * p.linearCost + 2 * (∑ b, len b) + (2 * n - 1) + ∑ b, integralConvolutionCost (len b) := by
  choose r P out hP hcost using fun b => integralConvolutionCost_attained (len b)
  obtain ⟨m, Q, result, hQ, hc⟩ := compile_integral p hp P out hP
  exact (FiniteFourier.integralConvolutionCost_le hQ).trans (by simpa only [hcost] using hc)

end OpenConvolution

end FiniteFourier
end LinearAlgebra
end OAI
