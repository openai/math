import OAI.LinearAlgebra.SpectralBooks.Fermion.WickKernel
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Order.Filter.Finite

/-! # Clearing contraction kernels in a Laurent matrix entry

At a fixed degree, a Laurent polynomial residual uses finitely many
coefficients of the propagator. Clearing a pole of order `L` takes `L`
backward differences before this finite convolution.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Fermion
open Filter LaurentPolynomial

/-- The coefficient action of a Laurent polynomial on a two-sided sequence. -/
def laurentAction (P : LaurentPolynomial ℤ) (f : ℤ → ℤ) (s : ℤ) : ℤ :=
  ∑ t ∈ P.coeff.support, f (s-t) * P.coeff t

theorem laurentAction_coeff (P Q : LaurentPolynomial ℤ) (s : ℤ) :
    (Q * P).coeff s = laurentAction P Q.coeff s := by
  simpa only [laurentAction, Finsupp.sum, sub_eq_add_neg] using
    AddMonoidAlgebra.coeff_mul_apply_right Q P s

/-- Coefficientwise stabilization is preserved by a fixed Laurent residual. -/
theorem eventually_coeff_mul_residual (p : ℕ → LaurentPolynomial ℤ) (f : ℤ → ℤ)
    (h : ∀ s, ∀ᶠ N : ℕ in atTop, (p N).coeff s = f s)
    (P : LaurentPolynomial ℤ) (s : ℤ) :
    ∀ᶠ N : ℕ in atTop, (p N * P).coeff s = laurentAction P f s := by
  have hall : ∀ᶠ N : ℕ in atTop, ∀ t ∈ P.coeff.support, (p N).coeff (s-t) = f (s-t) :=
    (eventually_all_finset _).mpr (fun t _ => h (s-t))
  filter_upwards [hall] with N hN
  rw [laurentAction_coeff]
  exact Finset.sum_congr rfl fun t ht => congrArg (· * P.coeff t) (hN t ht)

/-- Multiplying by the clearing polynomial takes iterated backward differences. -/
theorem coeff_clear_pow (Q : LaurentPolynomial ℤ) (L : ℕ) (s : ℤ) :
    ((1 - T 1)^L * Q).coeff s = (kernelDifference^[L] Q.coeff) s := by
  induction L generalizing s with
  | zero => simp
  | succ L ih =>
    rw [pow_succ', mul_assoc, sub_mul, one_mul, Function.iterate_succ_apply']
    rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
    simp only [kernelDifference, T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, ← ih]
    rw [show -(1 : ℤ) + s = s - 1 by omega]

private theorem eventually_kernelDifference_iterate (p : ℕ → ℤ → ℤ) (f : ℤ → ℤ)
    (h : ∀ s, ∀ᶠ N : ℕ in atTop, p N s = f s) (L : ℕ) (s : ℤ) :
    ∀ᶠ N : ℕ in atTop, (kernelDifference^[L] (p N)) s = (kernelDifference^[L] f) s := by
  induction L generalizing s with
  | zero => exact h s
  | succ L ih =>
    filter_upwards [ih s, ih (s-1)] with N h₁ h₂
    simp only [Function.iterate_succ_apply', kernelDifference, h₁, h₂]

/-- Clear the kernel denominator and then convolve with the finite residual. -/
theorem eventually_coeff_clear_residual (p : ℕ → LaurentPolynomial ℤ) (f : ℤ → ℤ)
    (h : ∀ s, ∀ᶠ N : ℕ in atTop, (p N).coeff s = f s)
    (P : LaurentPolynomial ℤ) (L : ℕ) (s : ℤ) :
    ∀ᶠ N : ℕ in atTop, ((1 - T 1)^L * (p N * P)).coeff s =
      laurentAction P (kernelDifference^[L] f) s := by
  simp_rw [← mul_assoc]
  apply eventually_coeff_mul_residual
  intro t
  simp_rw [coeff_clear_pow]
  exact eventually_kernelDifference_iterate (fun N => (p N).coeff) f h L t

/-- The residuals of an incompletely contracted term cancel after all its poles are cleared. -/
theorem laurentAction_kernel_partial_cancellation (P : LaurentPolynomial ℤ) (L k : ℕ)
    (h : k ≤ L) (s : ℤ) :
    laurentAction P (kernelDifference^[L] (forwardKernel k)) s =
      laurentAction P (kernelDifference^[L] (reverseKernel k)) s := by
  rw [kernel_partial_cancellation L k h]

/-- With one remaining simple pole, the residual multiplies the formal delta
by the sum of its coefficients. -/
theorem laurentAction_kernel_full_delta (P : LaurentPolynomial ℤ) (L : ℕ) (s : ℤ) :
    laurentAction P (kernelDifference^[L] (forwardKernel (L+1))) s -
      laurentAction P (kernelDifference^[L] (reverseKernel (L+1))) s =
      ∑ t ∈ P.coeff.support, P.coeff t := by
  unfold laurentAction
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun t _ => by rw [← sub_mul, kernel_full_delta, one_mul]

/-- Differencing leaves a constant integral numerator in front of the kernel. -/
theorem iterate_kernelDifference_const_mul (a : ℤ) (f : ℤ → ℤ) (L : ℕ) :
    kernelDifference^[L] (fun s => a * f s) = fun s => a * (kernelDifference^[L] f) s := by
  induction L with
  | zero => rfl
  | succ L ih =>
    funext s
    simp only [Function.iterate_succ_apply', ih, kernelDifference, mul_sub]

theorem laurentAction_const_mul (P : LaurentPolynomial ℤ) (a : ℤ) (f : ℤ → ℤ) (s : ℤ) :
    laurentAction P (fun t => a * f t) s = a * laurentAction P f s := by
  simp only [laurentAction, Finset.mul_sum, mul_assoc]

/-- A common integral numerator survives the cutoff, clearing and convolution. -/
theorem eventually_coeff_clear_residual_const_mul (p : ℕ → LaurentPolynomial ℤ)
    (a : ℤ) (f : ℤ → ℤ) (h : ∀ s, ∀ᶠ N : ℕ in atTop, (p N).coeff s = a * f s)
    (P : LaurentPolynomial ℤ) (L : ℕ) (s : ℤ) :
    ∀ᶠ N : ℕ in atTop, ((1 - T 1)^L * (p N * P)).coeff s =
      a * laurentAction P (kernelDifference^[L] f) s := by
  simpa only [iterate_kernelDifference_const_mul, laurentAction_const_mul] using
    eventually_coeff_clear_residual p _ h P L s

/-- Forward and reverse cutoff terms cancel for any pole order at most the
clearing order, at every fixed degree and with a common Laurent residual. -/
theorem eventually_coeff_clear_partial (p q : ℕ → LaurentPolynomial ℤ) (a : ℤ)
    (k L : ℕ) (hk : k ≤ L)
    (hp : ∀ s, ∀ᶠ N : ℕ in atTop, (p N).coeff s = a * forwardKernel k s)
    (hq : ∀ s, ∀ᶠ N : ℕ in atTop, (q N).coeff s = a * reverseKernel k s)
    (P : LaurentPolynomial ℤ) (s : ℤ) :
    ∀ᶠ N : ℕ in atTop, ((1 - T 1)^L * (p N * P)).coeff s -
      ((1 - T 1)^L * (q N * P)).coeff s = 0 := by
  filter_upwards [eventually_coeff_clear_residual_const_mul p a _ hp P L s,
    eventually_coeff_clear_residual_const_mul q a _ hq P L s] with N h₁ h₂
  rw [h₁, h₂, laurentAction_kernel_partial_cancellation P L k hk, sub_self]

/-- Forward and reverse cutoff terms with one pole left produce the delta
coefficient times the common numerator and the residual evaluated at one. -/
theorem eventually_coeff_clear_full (p q : ℕ → LaurentPolynomial ℤ) (a : ℤ) (L : ℕ)
    (hp : ∀ s, ∀ᶠ N : ℕ in atTop, (p N).coeff s = a * forwardKernel (L+1) s)
    (hq : ∀ s, ∀ᶠ N : ℕ in atTop, (q N).coeff s = a * reverseKernel (L+1) s)
    (P : LaurentPolynomial ℤ) (s : ℤ) :
    ∀ᶠ N : ℕ in atTop, ((1 - T 1)^L * (p N * P)).coeff s -
      ((1 - T 1)^L * (q N * P)).coeff s = a * ∑ t ∈ P.coeff.support, P.coeff t := by
  filter_upwards [eventually_coeff_clear_residual_const_mul p a _ hp P L s,
    eventually_coeff_clear_residual_const_mul q a _ hq P L s] with N h₁ h₂
  rw [h₁, h₂, ← mul_sub, laurentAction_kernel_full_delta]

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
