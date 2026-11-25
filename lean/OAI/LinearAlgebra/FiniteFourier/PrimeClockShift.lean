import OAI.LinearAlgebra.FiniteFourier.PrimeClockProduct
import OAI.LinearAlgebra.FiniteFourier.PrimePencil
import Mathlib.Algebra.MvPolynomial.Degrees

/-! # Weighted clock and shift matrices for simultaneous matrix evaluation

The columns are indexed by tuples of cyclic digits. The term for digit `i`
increments that digit, multiplies by the chosen affine form for its old value,
and applies a clock factor on every earlier digit.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix Finset Fin.NatCast

noncomputable section

variable {R : Type*} [CommRing R]

/-- A column-sparse matrix which takes the basis vector at `c` to
`w c` times the basis vector at `f c`. -/
private def weightedMapMatrix {A : Type*} [DecidableEq A] (f : A → A) (w : A → R) : Matrix A A R :=
  fun x c => if x = f c then w c else 0

private theorem weightedMapMatrix_mul {A : Type*} [Fintype A] [DecidableEq A]
    (f g : A → A) (w v : A → R) :
    weightedMapMatrix f w * weightedMapMatrix g v =
    weightedMapMatrix (f ∘ g) (fun c => w (g c) * v c) := by
  ext x c
  simp [weightedMapMatrix, Matrix.mul_apply, mul_ite, ite_mul]

private theorem weightedMapMatrix_pow {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → A) (w : A → R) (n : ℕ) :
    weightedMapMatrix f w ^ n = weightedMapMatrix f^[n] (fun c => ∏ k ∈ range n, w (f^[k] c)) := by
  induction n with
  | zero => ext x c; by_cases hx : x = c <;> simp [weightedMapMatrix, hx]
  | succ n ih =>
    rw [pow_succ', ih, weightedMapMatrix_mul]
    rw [Function.iterate_succ']
    congr 1
    funext c
    rw [prod_range_succ, mul_comm]

private theorem smul_weightedMapMatrix {A : Type*} [DecidableEq A] (f : A → A) (w : A → R) (s : R) :
    s • weightedMapMatrix f w = weightedMapMatrix f (fun c => s * w c) := by
  ext x c
  simp [weightedMapMatrix, mul_ite]

variable {b h : ℕ} [NeZero b]

private def advanceDigit (i : Fin h) (x : Fin h → Fin b) : Fin h → Fin b :=
  Function.update x i (x i + 1)

private theorem advanceDigit_iterate (i : Fin h) (x : Fin h → Fin b) (k : ℕ) (a : Fin h) :
    ((advanceDigit i)^[k] x) a = if a = i then x i + (k : Fin b) else x a := by
  induction k generalizing a with
  | zero => by_cases ha : a = i <;> simp [ha]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases ha : a = i
    · subst a
      simp [advanceDigit, ih, add_assoc]
    · simp [advanceDigit, ih, ha]

private def clockPrefix (ξ : R) (i : Fin h) (x : Fin h → Fin b) : R :=
  ∏ k ∈ Iio i, ξ ^ (x k).val

/-- On the tensor product of `h` factors, apply clocks on the first `i`
digits and a weighted cyclic shift on digit `i`. -/
def qClockTerm (ξ : R) (factors : Fin h → Fin b → R) (i : Fin h) :
    Matrix (Fin h → Fin b) (Fin h → Fin b) R :=
  weightedMapMatrix (advanceDigit i) (fun c => clockPrefix ξ i c * factors i (c i))

private theorem clockPrefix_iterate (ξ : R) (i : Fin h) (x : Fin h → Fin b) (k : ℕ) :
    clockPrefix ξ i ((advanceDigit i)^[k] x) = clockPrefix ξ i x := by
  apply Finset.prod_congr rfl
  intro a ha
  simp [advanceDigit_iterate, (Finset.mem_Iio.mp ha).ne]

omit [NeZero b] in
private theorem clockPrefix_period {ξ : R} (hξ : ξ ^ b = 1) (i : Fin h) (x : Fin h → Fin b) :
    clockPrefix ξ i x ^ b = 1 := by
  rw [clockPrefix, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro a _
  rw [← pow_mul, Nat.mul_comm, pow_mul, hξ, one_pow]

/-- After one full cycle of digit `i`, every row has accumulated the same product. -/
theorem qClockTerm_pow {ξ : R} (hξ : ξ ^ b = 1) (factors : Fin h → Fin b → R) (i : Fin h) :
    qClockTerm ξ factors i ^ b =
      (∏ t, factors i t) • (1 : Matrix (Fin h → Fin b) (Fin h → Fin b) R) := by
  have hstep : (advanceDigit (b := b) i)^[b] = id := by
    funext c a
    by_cases ha : a = i <;> simp [advanceDigit_iterate, ha]
  have hweights (c : Fin h → Fin b) :
      (∏ k ∈ range b, clockPrefix ξ i ((advanceDigit i)^[k] c) *
        factors i (((advanceDigit i)^[k] c) i)) = ∏ t, factors i t := by
    simp only [clockPrefix_iterate, advanceDigit_iterate, ite_true, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_range, clockPrefix_period hξ, one_mul]
    exact prod_clock_shift _ _
  rw [qClockTerm, weightedMapMatrix_pow, hstep]
  ext x c
  by_cases hx : x = c <;> simp [weightedMapMatrix, hx, hweights]

private theorem advanceDigit_comm {i j : Fin h} (hij : i ≠ j) :
    advanceDigit (b := b) j ∘ advanceDigit i = advanceDigit i ∘ advanceDigit j := by
  funext c t
  by_cases hi : t = i <;> by_cases hj : t = j <;>
    simp [advanceDigit, Function.comp_apply, *, Ne.symm hij]

private theorem clockPrefix_before (ξ : R) {i j : Fin h} (hij : i < j) (c : Fin h → Fin b) :
    clockPrefix ξ i (advanceDigit j c) = clockPrefix ξ i c := by
  apply prod_congr rfl
  intro k hk
  have hkj := (lt_trans (mem_Iio.mp hk) hij).ne
  simp [advanceDigit, hkj]

private theorem clockPrefix_after {ξ : R} (hξ : ξ ^ b = 1) {i j : Fin h} (hij : i < j)
    (c : Fin h → Fin b) : clockPrefix ξ j (advanceDigit i c) = ξ * clockPrefix ξ j c := by
  have hw (k : Fin h) : ξ ^ ((advanceDigit i c) k).val =
      (if i = k then ξ else 1) * ξ ^ (c k).val := by
    by_cases hk : k = i
    · subst k
      simpa [advanceDigit] using pow_clock_succ ξ hξ (c i)
    · simp [advanceDigit, hk, Ne.symm hk]
  simp only [clockPrefix, hw, Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq_of_mem _ i (fun _ => ξ) (mem_Iio.mpr hij)]

/-- A later shift commutes past an earlier shift with one factor of `ξ`. -/
theorem qClockTerm_comm {ξ : R} (hξ : ξ ^ b = 1) (factors : Fin h → Fin b → R)
    {i j : Fin h} (hij : i < j) :
    qClockTerm ξ factors j * qClockTerm ξ factors i =
      ξ • (qClockTerm ξ factors i * qClockTerm ξ factors j) := by
  rw [qClockTerm, qClockTerm, weightedMapMatrix_mul, weightedMapMatrix_mul,
    smul_weightedMapMatrix, advanceDigit_comm hij.ne]
  congr 1
  funext c
  rw [clockPrefix_before ξ hij, clockPrefix_after hξ hij]
  simp [advanceDigit, hij.ne, Ne.symm hij.ne]
  ring

/-- With scalar clocks and affine weights, every entry of the term remains affine. -/
theorem qClockTerm_affine {σ : Type*} (ξ : R) (f : Fin h → Fin b → MvPolynomial σ R)
    (hf : ∀ i j, (f i j).totalDegree ≤ 1) (i : Fin h) (x y : Fin h → Fin b) :
    ((qClockTerm (MvPolynomial.C ξ) f i) x y).totalDegree ≤ 1 := by
  classical
  have hc : clockPrefix (MvPolynomial.C ξ : MvPolynomial σ R) i y =
      MvPolynomial.C (clockPrefix ξ i y) := by simp [clockPrefix, map_prod, map_pow]
  by_cases he : x = advanceDigit i y
  · simp only [qClockTerm, weightedMapMatrix, he, hc]
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hf i (y i))
  · simp [qClockTerm, weightedMapMatrix, he]

/-- The sum of the clock-shift matrices evaluates a sum of products on every
independent input, the matrix-power identity used by the repair predictor. -/
theorem qClock_sum_pow [IsDomain R] {ξ : R} (hξ : IsPrimitiveRoot ξ b)
    (factors : Fin h → Fin b → R) :
    (∑ i, qClockTerm ξ factors i) ^ b =
      (∑ i, ∏ t, factors i t) • (1 : Matrix (Fin h → Fin b) (Fin h → Fin b) R) := by
  rw [potter_fin_sum (NeZero.pos b) hξ _ (fun i j hij => qClockTerm_comm hξ.pow_eq_one factors hij)]
  simp only [qClockTerm_pow hξ.pow_eq_one, Finset.sum_smul]

end

end FiniteFourier
end LinearAlgebra
end OAI
