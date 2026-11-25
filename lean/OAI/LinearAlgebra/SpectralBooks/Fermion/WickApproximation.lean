import OAI.LinearAlgebra.SpectralBooks.Fermion.WickKernel
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.PowerSeries.Trunc

/-! # Stabilization of products of truncated fermionic kernels

The forward expansion is an ordinary polynomial approximation at zero. The
reverse expansion uses the reciprocal polynomial variable with the sign and
degree shift determined by the pole order. Truncated kernels multiply in
these two presentations, and their coefficients stabilize in each degree.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Fermion
open Filter PowerSeries LaurentPolynomial
open scoped Polynomial PowerSeries BigOperators

private def poleEmbed (rev : Bool) (k : ℕ) (P : Polynomial ℤ) : LaurentPolynomial ℤ :=
  if rev then LaurentPolynomial.C ((-1)^k) * (T (-(k:ℤ)) * invert P.toLaurent)
  else P.toLaurent

private theorem poleEmbed_mul (rev : Bool) (k l : ℕ) (P Q : Polynomial ℤ) :
    poleEmbed rev (k+l) (P*Q) = poleEmbed rev k P * poleEmbed rev l Q := by
  cases rev
  · simp [poleEmbed]
  · simp only [poleEmbed, ite_true, pow_add, map_mul, Nat.cast_add, neg_add, T_add]
    ring

/-- Coefficientwise approximation of the order-`k` pole with numerator `c`.
The polynomial witnesses use the ordinary variable even in the reverse chart. -/
def PoleApprox (rev : Bool) (k : ℕ) (c : ℤ) (p : ℕ → LaurentPolynomial ℤ) : Prop :=
  ∃ P : ℕ → Polynomial ℤ, (∀ N, p N = poleEmbed rev k (P N)) ∧
    ∀ n : ℕ, ∀ᶠ N in atTop, (P N).coeff n = c * forwardKernel k n

namespace PoleApprox

theorem constant (rev : Bool) (c : ℤ) :
    PoleApprox rev 0 c (fun _ ↦ LaurentPolynomial.C c) := by
  refine ⟨fun _ ↦ Polynomial.C c, fun N ↦ ?_, fun n ↦ Eventually.of_forall fun N ↦ ?_⟩
  · cases rev <;> simp [poleEmbed]
  · change (Polynomial.C c).coeff n = c * PowerSeries.coeff n _
    rw [Polynomial.coeff_C, invOneSubPow_zero]
    simp [mul_ite]

theorem mul {rev : Bool} {k l : ℕ} {c d : ℤ} {p q : ℕ → LaurentPolynomial ℤ}
    (hp : PoleApprox rev k c p) (hq : PoleApprox rev l d q) :
    PoleApprox rev (k+l) (c*d) (fun N ↦ p N*q N) := by
  obtain ⟨P,hP,cp⟩ := hp
  obtain ⟨Q,hQ,cq⟩ := hq
  refine ⟨fun N ↦ P N * Q N, fun N ↦ by dsimp only; rw [hP, hQ, poleEmbed_mul], fun n ↦ ?_⟩
  filter_upwards [(eventually_all_finset (Finset.antidiagonal n)).mpr
      (fun (t : ℕ × ℕ) _ ↦ (cp t.1).and (cq t.2))] with N hN
  rw [Polynomial.coeff_mul]
  change _ = (c*d)*coeff n (invOneSubPow ℤ (k+l)).val
  rw [invOneSubPow_add, Units.val_mul, PowerSeries.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [(hN t ht).1, (hN t ht).2]
  unfold forwardKernel
  ring

end PoleApprox

/-- A single kernel retaining precisely the first `n` nonnegative coefficients
in its chosen expansion variable. -/
def trimPole (rev : Bool) (k : ℕ) (c : ℤ) (n : ℕ) : LaurentPolynomial ℤ :=
  if rev then ∑ t ∈ Finset.range n,
    LaurentPolynomial.C ((-1)^k * c * forwardKernel k (t:ℤ)) * T (-(t:ℤ)-k)
  else ∑ t ∈ Finset.range n, LaurentPolynomial.C (c * forwardKernel k (t:ℤ)) * T t

private def approxPoly (k : ℕ) (c : ℤ) (n : ℕ) : Polynomial ℤ :=
  ∑ t ∈ Finset.range n, Polynomial.monomial t (c*forwardKernel k t)

private theorem trimPole_eq_embed (rev : Bool) (k : ℕ) (c : ℤ) (n : ℕ) :
    trimPole rev k c n = poleEmbed rev k (approxPoly k c n) := by
  cases rev
  · simp [trimPole, poleEmbed, approxPoly, map_sum]
  · simp only [trimPole, poleEmbed, ite_true, approxPoly, map_sum, Polynomial.toLaurent_C_mul_T,
      map_mul, invert_C, invert_T, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [sub_eq_add_neg, T_add]
    ring

theorem PoleApprox.trim (rev : Bool) (k : ℕ) (c : ℤ) (d : ℕ) :
    PoleApprox rev k c (fun N ↦ trimPole rev k c (N-d)) := by
  refine ⟨fun N ↦ approxPoly k c (N-d), fun N ↦ trimPole_eq_embed _ _ _ _, fun n ↦ ?_⟩
  filter_upwards [eventually_ge_atTop (n+d+1)] with N hN
  have hn : n < N-d := by omega
  simp [approxPoly, Polynomial.coeff_monomial, hn]

private theorem coeff_toLaurent_nat (P : Polynomial ℤ) (n : ℕ) :
    P.toLaurent.coeff n = P.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ n

private theorem coeff_toLaurent_neg (P : Polynomial ℤ) (n : ℕ) :
    P.toLaurent.coeff (.negSucc n) = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_not_mem_image_support
  rintro ⟨a, _, ha⟩
  change (a:ℤ) = .negSucc n at ha
  omega

theorem PoleApprox.coeff {rev : Bool} {k : ℕ} {c : ℤ} {p : ℕ → LaurentPolynomial ℤ}
    (h : PoleApprox rev k c p) (s : ℤ) :
    ∀ᶠ N in atTop, (p N).coeff s = c * (if rev then reverseKernel else forwardKernel) k s := by
  obtain ⟨P,hP,cp⟩ := h
  have hcoeff (t : ℤ) : ∀ᶠ N in atTop, (P N).toLaurent.coeff t = c * forwardKernel k t := by
    cases t with
    | ofNat n => simpa only [Int.ofNat_eq_natCast, coeff_toLaurent_nat] using cp n
    | negSucc n => exact Eventually.of_forall fun N ↦ by rw [coeff_toLaurent_neg]; simp [forwardKernel]
  cases rev
  · simpa [hP, poleEmbed] using hcoeff s
  · filter_upwards [hcoeff (-s-k)] with N hN
    rw [hP]
    simp only [poleEmbed, ite_true, reverseKernel]
    change (AddMonoidAlgebra.single 0 ((-1:ℤ)^k) *
      (AddMonoidAlgebra.single (-(k:ℤ)) 1 * invert (P N).toLaurent)).coeff s = _
    simp only [AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add, neg_neg,
      one_mul, invert_apply]
    rw [show -((k:ℤ)+s) = -s-k by ring, hN]
    ring

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
