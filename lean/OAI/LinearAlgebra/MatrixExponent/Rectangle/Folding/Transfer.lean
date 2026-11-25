import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.Fintype.BigOperators
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.TreePrice
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup.Dense
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Concentration of additive grades on finite words -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Finset Real

variable {X I : Type} [Fintype X] [Fintype I] [DecidableEq I]

def height (g : X → ℕ) (x : I → X) : ℝ := ∑ i, (g (x i) : ℝ)

/-- The prefactor in the tail bound is fixed before taking word powers. -/
def Focus (g : X → ℕ) (K : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (I : Type) [Fintype I] [DecidableEq I] (t : ℝ), 0 < t →
    ∃ S : Finset (I → X), (S.card : ℝ) ≤ C * Fintype.card (I → X) * exp (-t ^ 2 * Fintype.card I) ∧
      ∀ x ∉ S, ∀ y ∉ S, height g y - height g x ≤ K * t * Fintype.card I

private theorem moment (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1) (hz : ∑ x, f x = 0) (t : ℝ) :
    ∑ x, exp (t * f x) ≤ Fintype.card X * exp (t ^ 2) := by
  have h (x) : exp (t * f x) ≤ cosh t + f x * ((exp t - exp (-t)) / 2) := by
    obtain ⟨hl, hr⟩ := abs_le.mp (hf x)
    have he := convexOn_exp.2 (Set.mem_univ t) (Set.mem_univ (-t))
      (show 0 ≤ (1 + f x) / 2 by linarith) (show 0 ≤ (1 - f x) / 2 by linarith)
      (by ring : (1 + f x) / 2 + (1 - f x) / 2 = 1)
    simp only [smul_eq_mul, show (1 + f x) / 2 * t + (1 - f x) / 2 * (-t) = t * f x by ring] at he
    rw [cosh_eq]
    linarith only [he]
  have he := sum_le_sum (s := univ) fun x _ => h x
  rw [sum_add_distrib, ← sum_mul, hz, zero_mul, add_zero, sum_const, nsmul_eq_mul, card_univ] at he
  exact he.trans (mul_le_mul_of_nonneg_left
    ((cosh_le_exp_half_sq t).trans (exp_le_exp.mpr (by nlinarith [sq_nonneg t]))) (by positivity))

open Classical in
private theorem tail (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1) (hz : ∑ x, f x = 0) {t : ℝ} (ht : 0 < t) :
    (#{x : I → X | 2 * t * Fintype.card I < ∑ i, f (x i)} : ℝ) ≤
      Fintype.card (I → X) * exp (-t ^ 2 * Fintype.card I) := by
  let n := Fintype.card I
  let S : Finset (I → X) := {x | 2 * t * n < ∑ i, f (x i)}
  apply le_of_mul_le_mul_right _ (exp_pos (t * (2 * t * n)))
  calc
    _ = ∑ _ ∈ S, exp (t * (2 * t * n)) := by simp [S, n]
    _ ≤ ∑ x ∈ S, exp (t * ∑ i, f (x i)) := sum_le_sum fun x hx =>
      exp_le_exp.mpr (mul_le_mul_of_nonneg_left (mem_filter.mp hx).2.le ht.le)
    _ ≤ ∑ x : I → X, exp (t * ∑ i, f (x i)) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
    _ = (∑ x, exp (t * f x)) ^ n := by
      simp_rw [mul_sum, exp_sum]
      rw [← Fintype.prod_sum (fun (_ : I) (x : X) => exp (t * f x)), prod_const, card_univ]
    _ ≤ (Fintype.card X * exp (t ^ 2)) ^ n :=
      pow_le_pow_left₀ (by positivity) (moment f hf hz t) _
    _ = _ := by
      rw [Fintype.card_fun, Nat.cast_pow, mul_pow, ← exp_nat_mul, mul_assoc, ← exp_add]
      unfold n
      ring_nf

theorem binary_focus [Nonempty X] (g : X → ℕ) (hg : ∀ x, g x ≤ 1) : Focus g 4 := by
  classical
  let a := (∑ x, (g x : ℝ)) / Fintype.card X
  have hc : 0 < (Fintype.card X : ℝ) := by positivity
  have he : a * Fintype.card X = ∑ x, (g x : ℝ) := div_mul_cancel₀ _ hc.ne'
  have ha : 0 ≤ a := by unfold a; positivity
  have hle (x) : (g x : ℝ) ≤ 1 := by exact_mod_cast hg x
  have ha' : a ≤ 1 := (div_le_one hc).mpr (by simpa using sum_le_sum (s := univ) fun x _ => hle x)
  let f x := (g x : ℝ) - a
  have hz : ∑ x, f x = 0 := by simp [f, sum_sub_distrib, ← he, mul_comm]
  have hf (x) : |f x| ≤ 1 := by unfold f; rw [abs_le]; constructor <;> linarith [hle x]
  refine ⟨2, by norm_num, ?_⟩
  intro I _ _ t ht
  let S (h : X → ℝ) : Finset (I → X) := {x | 2 * t * Fintype.card I < ∑ i, h (x i)}
  have h₁ := tail (I := I) f hf hz ht
  have h₂ := tail (I := I) (-f) (by simpa using hf) (by simp [hz]) ht
  refine ⟨S f ∪ S (-f), ?_, ?_⟩
  · have he : ((S f ∪ S (-f)).card : ℝ) ≤ (S f).card + (S (-f)).card := by
      exact_mod_cast card_union_le (S f) (S (-f))
    unfold S at he ⊢
    linarith only [he, h₁, h₂]
  · intro x hx y hy
    have hx' := (notMem_union.mp hx).2
    have hy' := (notMem_union.mp hy).1
    simp only [S, mem_filter, mem_univ, true_and, not_lt, Pi.neg_apply, sum_neg_distrib,
      f, sum_sub_distrib] at hx' hy'
    unfold height
    linarith only [hx', hy']

abbrev Block (X : Type) := Fin 100 → X

def blockGrade (g : X → ℕ) (x : Block X) := ∑ i, g (x i)

theorem Focus.block {g : X → ℕ} {K : ℝ} (h : Focus g K) : Focus (blockGrade g) (10 * K) := by
  classical
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, ?_⟩
  intro I _ _ t ht
  let e := Equiv.curry I (Fin 100) X
  have hc : (Fintype.card (I × Fin 100) : ℝ) = Fintype.card I * 100 := by simp
  have he (x : I → Block X) : height (blockGrade g) x = height g (e.symm x) := by
    simp only [height, blockGrade, Nat.cast_sum, Fintype.sum_prod_type]
    rfl
  obtain ⟨S, hS, hd⟩ := h (I × Fin 100) (t / 10) (by positivity)
  refine ⟨S.map e.toEmbedding, ?_, ?_⟩
  · rw [card_map]
    rw [Fintype.card_congr e, hc, show -(t / 10) ^ 2 * (Fintype.card I * 100) = -t ^ 2 * Fintype.card I by ring] at hS
    exact hS
  · intro x hx y hy
    rw [he, he]
    rw [mem_map_equiv] at hx hy
    have hh := hd _ hx _ hy
    rw [hc] at hh
    linarith only [hh]

theorem Focus.half [Nonempty X] {g : X → ℕ} {K : ℝ} (h : Focus g K) :
    Focus (fun x => g x / 2) ((K + 4) / 2) := by
  classical
  obtain ⟨C, hC, h⟩ := h
  obtain ⟨D, hD, h'⟩ := binary_focus (fun x => g x % 2) (fun _ => by omega)
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro I _ _ t ht
  obtain ⟨S, hS, hs⟩ := h I t ht
  obtain ⟨T, hT, ht'⟩ := h' I t ht
  refine ⟨S ∪ T, ?_, ?_⟩
  · have hh : ((S ∪ T).card : ℝ) ≤ S.card + T.card := by exact_mod_cast card_union_le S T
    linarith only [hh, hS, hT]
  · intro x hx y hy
    have he (v : I → X) : 2 * height (fun u => g u / 2) v + height (fun u => g u % 2) v = height g v := by
      simp only [height, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      exact_mod_cast (show 2 * (g (v i) / 2) + g (v i) % 2 = g (v i) by omega)
    obtain ⟨hx, hx'⟩ := notMem_union.mp hx
    obtain ⟨hy, hy'⟩ := notMem_union.mp hy
    linarith only [he x, he y, hs x hx y hy, ht' y hy' x hx']

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # A quantitative one-register approximation to a swap -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Prices.Motion
open scoped Classical

def swapMatrix (F W : Type) [Field F] : Matrix (W × W) (W × W) F :=
  fun x y => if x = (y.2, y.1) then 1 else 0

def SwapBound (F W : Type) [Field F] [Fintype W] (dist : W → W → ℝ) (B : ℕ) (C : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∃ N : Matrix (W × W) (W × W) F,
    Low (swapMatrix F W - N) (C * (Fintype.card W : ℝ) ^ 2 * Real.exp (-t ^ 2 * B)) ∧
      ∀ x y, N x y ≠ 0 → dist x.1 y.1 ≤ 48 * t * B

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # Matrix approximation with a bound on displacement -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Finset Prices.Motion
open scoped Classical Kronecker

variable {X Y F : Type} [Field F] {D : X → X → ℝ} {M N : Matrix X X F}
    {a b r s : ℝ}

theorem low_pull (h : Low M r) (f : Y → X) : Low (M.submatrix f f) r := by
  obtain ⟨I, _, hi, P, Q, rfl⟩ := h
  exact ⟨I, inferInstance, hi, P.submatrix f id, Q.submatrix id f, rfl⟩

theorem low_kron {N : Matrix Y Y F} (h : Low M r) (h' : Low N s) : Low (M ⊗ₖ N) (r * s) := by
  obtain ⟨I, _, hi, P, Q, rfl⟩ := h
  obtain ⟨J, _, hj, S, T, rfl⟩ := h'
  refine ⟨I × J, inferInstance, ?_, P ⊗ₖ S, Q ⊗ₖ T, Matrix.mul_kronecker_mul _ _ _ _⟩
  rw [Fintype.card_prod, Nat.cast_mul]
  exact mul_le_mul hi hj (by positivity) ((by positivity : 0 ≤ (Fintype.card I : ℝ)).trans hi)

def Bounded (D : X → X → ℝ) (M : Matrix X X F) (p : ℝ) : Prop :=
  ∀ x y, M x y ≠ 0 → D x y ≤ p

def Within (D : X → X → ℝ) (M : Matrix X X F) (r p : ℝ) : Prop :=
  ∃ N, Low (M - N) r ∧ Bounded D N p

theorem Bounded.mono (h : Bounded D M a) (hab : a ≤ b) : Bounded D M b :=
  fun x y hxy => (h x y hxy).trans hab

theorem Bounded.sub (h : Bounded D M a) (h' : Bounded D N a) : Bounded D (M - N) a := by
  intro x y he
  by_cases hx : M x y = 0
  · exact h' _ _ (by simpa [hx] using he)
  · exact h _ _ hx

theorem Within.exact (h : Bounded D M a) : Within D M 0 a :=
  ⟨M, by rw [sub_self]; exact Low.zero, h⟩

theorem Within.low (h : Low M r) (a : ℝ) : Within D M r a := ⟨0, by simpa, by simp [Bounded]⟩

theorem Within.mono (h : Within D M r a) (hr : r ≤ s) (ha : a ≤ b) : Within D M s b := by
  obtain ⟨P, hp, hp'⟩ := h
  exact ⟨P, hp.mono hr, hp'.mono ha⟩

theorem Within.pull (h : Within D M r a) (f : Y → X) :
    Within (fun x y => D (f x) (f y)) (M.submatrix f f) r a := by
  obtain ⟨P, hp, hp'⟩ := h
  exact ⟨P.submatrix f f, low_pull hp f, fun x y => hp' (f x) (f y)⟩

theorem Within.add (h : Within D M r a) (h' : Within D N s a) : Within D (M + N) (r + s) a := by
  obtain ⟨P, hp, hp'⟩ := h
  obtain ⟨Q, hq, hq'⟩ := h'
  refine ⟨P + Q, by rw [add_sub_add_comm]; exact hp.add hq, fun x y he => ?_⟩
  by_cases hx : P x y = 0
  · exact hq' _ _ (by simpa [hx] using he)
  · exact hp' _ _ hx

theorem Within.mul [Fintype X] (h : Within D M r a) (h' : Within D N s b)
    (ht : ∀ x y z, D x z ≤ D x y + D y z) : Within D (M * N) (r + s) (a + b) := by
  obtain ⟨P, hp, hp'⟩ := h
  obtain ⟨Q, hq, hq'⟩ := h'
  refine ⟨P * Q, ?_, fun x y hxy => ?_⟩
  · exact approx_mul hp hq
  · obtain ⟨z, _, hz⟩ := exists_ne_zero_of_sum_ne_zero (show (∑ z, P x z * Q z y) ≠ 0 from hxy)
    exact (ht _ _ _).trans (add_le_add (hp' _ _ (left_ne_zero_of_mul hz))
      (hq' _ _ (right_ne_zero_of_mul hz)))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # Freeing an active register in a pair of groups -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Finset Prices.Motion
open scoped Classical Kronecker

variable {W T F : Type} [Field F] {d : W → W → ℝ} {D : T → T → ℝ}

abbrev Pair (W T : Type) := (W × T) × (W × T)

def cost (d : W → W → ℝ) (D : T → T → ℝ) (x y : Pair W T) : ℝ :=
  D x.1.2 y.1.2 + d x.2.1 y.2.1 + D x.2.2 y.2.2

private def sw (x : Pair W T) : Pair W T := ((x.2.1, x.1.2), (x.1.1, x.2.2))

@[simp] private theorem sw_sw (x : Pair W T) : sw (sw x) = x := rfl

private def exch (F W T : Type) [Field F] : Matrix (Pair W T) (Pair W T) F :=
  fun x y => if x = sw y then 1 else 0

variable [Fintype W] [Fintype T] {C t : ℝ} {B : ℕ}

private theorem conjugate (M : Matrix (Pair W T) (Pair W T) F) :
    exch F W T * M.submatrix sw sw * exch F W T = M := by
  ext x y
  have h (z) : x = sw z ↔ z = sw x := by constructor <;> rintro rfl <;> simp
  simp [Matrix.mul_apply, exch, h, ite_mul, mul_ite]

private theorem exchange_cost (hD : ∀ x, D x x = 0) (h : SwapBound F W d B C) (ht : 0 < t) :
    Within (cost d D) (exch F W T)
      (C * (Fintype.card (W × T) : ℝ) ^ 2 * Real.exp (-t ^ 2 * B)) (48 * t * B) := by
  obtain ⟨N, hr, hn⟩ := h t ht
  let π (x : Pair W T) := ((x.2.1, x.1.1), (x.1.2, x.2.2))
  let I : Matrix (T × T) (T × T) F := 1
  refine ⟨(N ⊗ₖ I).submatrix π π, ?_, ?_⟩
  · have he : exch F W T - (N ⊗ₖ I).submatrix π π =
        ((swapMatrix F W - N) ⊗ₖ I).submatrix π π := by
      ext x y
      simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, sub_mul]
      congr 1
      simp only [I, π, exch, sw, swapMatrix, Matrix.one_apply, Prod.ext_iff, ite_mul, one_mul, zero_mul,
        ← ite_and]
      congr 1
      exact propext (by tauto)
    rw [he]
    apply (low_pull (low_kron hr (Low.full I)) π).mono
    simp only [Fintype.card_prod, Nat.cast_mul]
    exact le_of_eq (by ring)
  · intro x y hxy
    change N (x.2.1, x.1.1) (y.2.1, y.1.1) * I (x.1.2, x.2.2) (y.1.2, y.2.2) ≠ 0 at hxy
    have he : x.1.2 = y.1.2 ∧ x.2.2 = y.2.2 := by
      simpa [I, Matrix.one_apply] using right_ne_zero_of_mul hxy
    simpa [cost, he.1, he.2, hD] using hn _ _ (left_ne_zero_of_mul hxy)

/-- Apply the second operation with the active registers exchanged. Its
uncontrolled movement then stays on the first register. -/
theorem free_register (hd : ∀ x, d x x = 0) (hd' : ∀ x y z, d x z ≤ d x y + d y z)
    (hD : ∀ x, D x x = 0) (hD' : ∀ x y z, D x z ≤ D x y + D y z)
    (h : SwapBound F W d B C) (ht : 0 < t) {P Q : Matrix (W × T) (W × T) F} {a b : ℝ}
    (hP : Bounded (fun x y => D x.2 y.2) P a) (hQ : Bounded (fun x y => D x.2 y.2) Q b) :
    Within (cost d D) (P ⊗ₖ Q) (2 * C * (Fintype.card (W × T) : ℝ) ^ 2 * Real.exp (-t ^ 2 * B)) (a + b + 96 * t * B) := by
  have tri (x y z : Pair W T) : cost d D x z ≤ cost d D x y + cost d D y z := by
    unfold cost
    linarith only [hD' x.1.2 y.1.2 z.1.2, hd' x.2.1 y.2.1 z.2.1, hD' x.2.2 y.2.2 z.2.2]
  let I : Matrix (W × T) (W × T) F := 1
  have hl : Within (cost d D) (P ⊗ₖ I) 0 a := by
    apply Within.exact
    intro x y hh
    change P x.1 y.1 * I x.2 y.2 ≠ 0 at hh
    have he : x.2 = y.2 := by simpa [I, Matrix.one_apply] using right_ne_zero_of_mul hh
    simpa [cost, he, hD, hd] using hP _ _ (left_ne_zero_of_mul hh)
  have hr : Within (cost d D) ((I ⊗ₖ Q).submatrix sw sw) 0 b := by
    apply Within.exact
    intro x y hh
    change I (x.2.1, x.1.2) (y.2.1, y.1.2) * Q (x.1.1, x.2.2) (y.1.1, y.2.2) ≠ 0 at hh
    have he : x.2.1 = y.2.1 ∧ x.1.2 = y.1.2 := by
      simpa [I, Matrix.one_apply] using left_ne_zero_of_mul hh
    simpa [cost, he.1, he.2, hD, hd] using hQ _ _ (right_ne_zero_of_mul hh)
  have he := exchange_cost hD h ht
  have hh := hl.mul ((he.mul hr tri).mul he tri) tri
  rw [conjugate, ← Matrix.mul_kronecker_mul, show I = 1 from rfl, mul_one, one_mul] at hh
  exact hh.mono (by linarith) (by linarith)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-!
# Interpolating approximations of two groups

The j-th difference on the left is paired with the approximation
at the complementary index on the right. The two rank savings
multiply, so each remainder gets the full target saving.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Prices.Motion
open scoped Classical Kronecker

variable {X F : Type} [Field F] [Fintype X] {D : X → X → ℝ}
  {E : X × X → X × X → ℝ} {M : Matrix X X F} {b : ℕ → ℝ} {q : ℕ} {R H u L : ℝ}

theorem interpolate (hu : 0 ≤ u) (hu' : u ≤ 1) (hR : (Fintype.card X : ℝ) ≤ R) (hb : Monotone b)
    (h : ∀ j : ℕ, 0 < j → Within D M (R * u ^ j) (b j))
    (hh : ∀ j < q, ∀ P Q : Matrix X X F, Bounded D P (b (j + 1)) → Bounded D Q (b (q - j)) →
      Within E (P ⊗ₖ Q) (H * u ^ q) L) :
    Within E (M ⊗ₖ M) (((q : ℝ) * (2 * R ^ 2 + H) + R ^ 2) * u ^ q) L := by
  have hM := (Low.full M).mono hR
  have hR' : 0 ≤ R := (by positivity : 0 ≤ (Fintype.card X : ℝ)).trans hR
  have he (j : ℕ) : ∃ N, (j = 0 → N = 0) ∧ Low (M - N) (R * u ^ j) ∧ Bounded D N (b j) := by
    by_cases hj : j = 0
    · exact ⟨0, fun _ => rfl, by simpa [hj] using hM, by simp [Bounded]⟩
    · obtain ⟨N, hN, hN'⟩ := h j (by omega)
      exact ⟨N, by omega, hN, hN'⟩
  choose A hz hr hp using he
  have step (j : ℕ) (hj : j < q) :
      Within E ((A (j + 1) - A j) ⊗ₖ M) ((2 * R ^ 2 + H) * u ^ q) L := by
    let P := A (j + 1) - A j
    have hs : Low P (2 * R * u ^ j) := by
      rw [show P = (M - A j) - (M - A (j + 1)) by unfold P; abel]
      refine ((hr j).sub (hr (j + 1))).mono ?_
      rw [pow_succ]
      linarith [mul_le_mul_of_nonneg_left hu' (show 0 ≤ R * u ^ j by positivity)]
    have hf := hh j hj P (A (q - j)) ((hp (j + 1)).sub ((hp j).mono (hb (Nat.le_succ _)))) (hp _)
    have hl := low_kron hs (hr (q - j))
    have heq : u ^ j * u ^ (q - j) = u ^ q := by rw [← pow_add, Nat.add_sub_of_le hj.le]
    change Within E (P ⊗ₖ M) _ _
    rw [show P ⊗ₖ M = (P ⊗ₖ (M - A (q - j))) + (P ⊗ₖ A (q - j)) by
      rw [← Matrix.kronecker_add, sub_add_cancel]]
    refine ((Within.low hl L).add hf).mono ?_ le_rfl
    apply le_of_eq
    rw [← heq]
    ring
  have go (i : ℕ) (hi : i ≤ q) : Within E (A i ⊗ₖ M) (i * ((2 * R ^ 2 + H) * u ^ q)) L := by
    induction i with
    | zero =>
      rw [hz _ rfl, Matrix.zero_kronecker, Nat.cast_zero, zero_mul]
      exact Within.low Low.zero L
    | succ i ih =>
      rw [Nat.cast_succ, add_mul, one_mul]
      have hh := (ih (by omega)).add (step i (by omega))
      rwa [← Matrix.add_kronecker, add_sub_cancel] at hh
  have ht := (go q le_rfl).add (Within.low (low_kron (hr q) hM) L)
  rw [← Matrix.add_kronecker, add_sub_cancel] at ht
  exact ht.mono (le_of_eq (by ring)) le_rfl

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # Summing the displacement costs on a dyadic tree -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding

/-- The additive reserve covers the cost of two exchanges and rounding
to a finite interpolation grid. -/
def radius (k : ℕ) := 500 * Real.sqrt ((2 : ℝ) ^ k) - 400

theorem radius_pos (k : ℕ) : 0 < radius k := by
  have hh : (1 : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ k) :=
    Real.one_le_sqrt.mpr (one_le_pow₀ (by norm_num))
  unfold radius
  linarith

private theorem sqrt_tangent {a : ℝ} (ha : 0 ≤ a) :
    Real.sqrt a * Real.sqrt 2 ≤ a + 1 / 2 := by
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    sq_nonneg (Real.sqrt a - Real.sqrt 2 / 2)]

theorem grid_choice (k : ℕ) : ∃ q : ℕ, 0 < q ∧ ∀ j < q,
    radius k * (Real.sqrt (((j : ℝ) + 1) / q) + Real.sqrt (((q : ℝ) - j) / q)) + 96 ≤ radius (k + 1) := by
  obtain ⟨q, hq⟩ := exists_nat_gt (radius k)
  have hq' := (radius_pos k).trans hq
  have hs : (5 / 4 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt] <;> norm_num
  have ht := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨q, Nat.cast_pos.mp hq', fun j hj => ?_⟩
  have hj' : (j : ℝ) ≤ q := Nat.cast_le.mpr hj.le
  let a := ((j : ℝ) + 1) / q
  let b := ((q : ℝ) - j) / q
  have ha : 0 ≤ a := by unfold a; positivity
  have hb : 0 ≤ b := by unfold b; positivity
  have hab : a + b = 1 + 1 / q := by unfold a b; field_simp; ring
  have hm : Real.sqrt a + Real.sqrt b ≤ Real.sqrt 2 + 1 / q := by
    apply le_of_mul_le_mul_right _ (show 0 < Real.sqrt 2 by positivity)
    have h := le_mul_of_one_le_right (show (0 : ℝ) ≤ 1 / q by positivity) (show 1 ≤ Real.sqrt 2 by linarith)
    linarith [sqrt_tangent ha, sqrt_tangent hb]
  calc
    _ ≤ radius k * (Real.sqrt 2 + 1 / q) + 96 := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left hm (radius_pos k).le) _
    _ ≤ radius k * Real.sqrt 2 + 97 := by
      have h := (div_le_one hq').mpr hq.le
      rw [mul_add, mul_one_div]
      linarith
    _ ≤ _ := by
      unfold radius
      rw [pow_succ, Real.sqrt_mul (by positivity)]
      linarith

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # A doubling step with a uniform constant at every target rate -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Prices.Motion
open scoped Classical Kronecker

theorem double (k : ℕ) {C K : ℝ} (hC : 0 ≤ C) (hK : 1 ≤ K) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ (F W T : Type) [Field F] [Fintype W] [Fintype T]
      (d : W → W → ℝ) (D : T → T → ℝ) (B : ℕ),
      (∀ x, d x x = 0) → (∀ x y z, d x z ≤ d x y + d y z) →
      (∀ x, D x x = 0) → (∀ x y z, D x z ≤ D x y + D y z) →
      SwapBound F W d B C → ∀ M : Matrix (W × T) (W × T) F,
      (∀ t : ℝ, 0 < t → Within (fun x y => D x.2 y.2) M
        (K * (Fintype.card (W × T) : ℝ) * Real.exp (-t ^ 2 * B)) (radius k * t * B)) →
      ∀ t : ℝ, 0 < t → Within (cost d D) (M ⊗ₖ M)
        (H * (Fintype.card (W × T) : ℝ) ^ 2 * Real.exp (-t ^ 2 * B)) (radius (k + 1) * t * B) := by
  obtain ⟨q, hq, hr⟩ := grid_choice k
  have hq' : 0 < (q : ℝ) := by positivity
  refine ⟨q * (2 * K ^ 2 + 2 * C) + K ^ 2, ?_, ?_⟩
  · exact (one_le_pow₀ hK).trans (le_add_of_nonneg_left (by positivity))
  intro F W T _ _ _ d D B hd hd' hD hD' hs M hm t ht
  let u := Real.exp (-t ^ 2 * B / q)
  let s (j : ℕ) := t * Real.sqrt ((j : ℝ) / q)
  let b (j : ℕ) := radius k * s j * B
  let N : ℝ := Fintype.card (W × T)
  have hb : Monotone b := by
    intro i j hij
    have hk := radius_pos k
    unfold b s
    gcongr
  have he (j : ℕ) : u ^ j = Real.exp (-(s j) ^ 2 * B) := by
    simp only [u, s, ← Real.exp_nat_mul, mul_pow, Real.sq_sqrt (show 0 ≤ (j : ℝ) / q by positivity)]
    congr 1
    ring
  have heq : u ^ q = Real.exp (-t ^ 2 * B) := by simp [he, s, hq'.ne']
  have hp (j : ℕ) (hj : 0 < j) : Within (fun x y => D x.2 y.2) M (K * N * u ^ j) (b j) := by
    rw [he]
    exact hm (s j) (by unfold s; positivity)
  have hpq (j : ℕ) (hj : j < q) (P Q : Matrix (W × T) (W × T) F)
      (hP : Bounded (fun x y => D x.2 y.2) P (b (j + 1)))
      (hQ : Bounded (fun x y => D x.2 y.2) Q (b (q - j))) :
      Within (cost d D) (P ⊗ₖ Q) (2 * C * N ^ 2 * u ^ q) (radius (k + 1) * t * B) := by
    rw [heq]
    refine (free_register hd hd' hD hD' hs ht hP hQ).mono le_rfl ?_
    simp only [b, s, Nat.cast_add, Nat.cast_one, Nat.cast_sub hj.le]
    linarith only [mul_le_mul_of_nonneg_right (hr j hj) (show 0 ≤ t * B by positivity)]
  have hu : u ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)) hq'.le)
  have hi := interpolate (Real.exp_pos _).le hu
    (le_mul_of_one_le_left (show 0 ≤ N by unfold N; positivity) hK) hb hp hpq
  rw [heq] at hi
  exact hi.mono (le_of_eq (by unfold N; ring)) le_rfl

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # Folding a dyadic power down to one unrestricted register -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Finset Prices.Motion
open scoped Classical Kronecker

variable {W F : Type} [Field F] [Fintype W]

private def inactive (d : W → W → ℝ) {n : ℕ} (x y : Fin n → W) :=
  ∑ i, if i.val = 0 then 0 else d (x i) (y i)

private def Works (k n : ℕ) (K C : ℝ) : Prop :=
  ∀ (F W : Type) [Field F] [Fintype W] (d : W → W → ℝ) (B : ℕ),
    (∀ x, d x x = 0) → (∀ x y z, d x z ≤ d x y + d y z) → SwapBound F W d B C →
    ∀ (M : Matrix W W F) (t : ℝ), 0 < t →
      Within (inactive d) (matPower (fun _ : Fin n => M))
        (K * (Fintype.card W : ℝ) ^ n * Real.exp (-t ^ 2 * B)) (radius k * t * B)

private theorem works_double {k n : ℕ} {K C : ℝ} (hn : 0 < n) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (h : Works k n K C) : ∃ H : ℝ, 1 ≤ H ∧ Works (k + 1) (n + n) H C := by
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨H, hH, hh⟩ := double k hC hK
    refine ⟨H, hH, ?_⟩
    intro F W _ _ d B hd hd' hs M t ht
    let T := Fin n → W
    let D (x y : T) := ∑ i, d (x i) (y i)
    have hD x : D x x = 0 := by simp [D, hd]
    have hD' x y z : D x z ≤ D x y + D y z := by
      unfold D
      rw [← sum_add_distrib]
      exact sum_le_sum (fun i _ => hd' _ _ _)
    let join (x : W × T) : Fin (n + 1) → W := Fin.cons x.1 x.2
    let split (x : Fin (n + 1) → W) : W × T := (x 0, Fin.tail x)
    let A := (matPower (fun _ : Fin (n + 1) => M)).submatrix join join
    have card : (Fintype.card (W × T) : ℝ) = (Fintype.card W : ℝ) ^ (n + 1) := by
      simp [T, pow_succ']
    have hj : (fun x y => inactive d (join x) (join y)) = (fun x y => D x.2 y.2) := by
      funext x y
      simp [inactive, Fin.sum_univ_succ, join, D]
    have hA (u : ℝ) (hu : 0 < u) := (h F W d B hd hd' hs M u hu).pull join
    rw [hj, ← card] at hA
    have he := hh F W T d D B hd hd' hD hD' hs A hA t ht
    let left (x : Fin ((n + 1) + (n + 1)) → W) := x ∘ Fin.castAdd (n + 1)
    let right (x : Fin ((n + 1) + (n + 1)) → W) := x ∘ Fin.natAdd (n + 1)
    let pair x := (split (left x), split (right x))
    have hw := he.pull pair
    have hM : (A ⊗ₖ A).submatrix pair pair = matPower (fun _ : Fin ((n + 1) + (n + 1)) => M) := by
      ext x y
      simp only [A, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, pair, join, split, Fin.cons_self_tail,
        matPower]
      exact (Fin.prod_univ_add (fun i => M (x i) (y i))).symm
    have hdist : (fun x y => cost d D (pair x) (pair y)) = inactive d := by
      funext x y
      unfold inactive
      rw [Fin.sum_univ_add]
      simp [Fin.sum_univ_succ, cost, D, pair, split, left, right, Fin.tail, add_assoc]
    rw [hM, hdist, card, pow_two, ← pow_add] at hw
    exact hw

private theorem works (k : ℕ) {C : ℝ} (hC : 0 ≤ C) : ∃ K : ℝ, 1 ≤ K ∧ Works k (2 ^ k) K C := by
  induction k with
  | zero =>
    refine ⟨1, le_rfl, ?_⟩
    intro F W _ _ d B hd hd' hs M t ht
    have hp : Bounded (inactive d) (matPower (fun _ : Fin 1 => M)) 0 := by simp [Bounded, inactive]
    have hk := radius_pos 0
    exact (Within.exact hp).mono (by positivity) (by positivity)
  | succ k ih =>
    obtain ⟨K, hK, hw⟩ := ih
    rw [pow_succ, mul_two]
    exact works_double (by positivity) hK hC hw

theorem fold (k : ℕ) {C t : ℝ} (hC : 0 ≤ C) (ht : 0 < t) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (F W : Type) [Field F] [Fintype W] (dist : W → W → ℝ) (B : ℕ),
      (∀ x, dist x x = 0) → (∀ x y z, dist x z ≤ dist x y + dist y z) → SwapBound F W dist B C →
      ∀ M : Matrix W W F, ∃ N, Low (matPower (fun _ : Fin (2 ^ k) => M) - N)
        (H * (Fintype.card W : ℝ) ^ (2 ^ k : ℕ) * Real.exp (-t ^ 2 * B)) ∧
      ∀ x y, N x y ≠ 0 → ∑ i ∈ univ.erase 0, dist (x i) (y i) ≤ 500 * t * Real.sqrt ((2 : ℝ) ^ k) * B := by
  obtain ⟨H, hH, h⟩ := works k hC
  refine ⟨H, by linarith, ?_⟩
  intro F W _ _ d B hd hd' hs M
  obtain ⟨N, he, hb⟩ := h F W d B hd hd' hs M t ht
  refine ⟨N, he, fun x y hh => ?_⟩
  have eqn : inactive d x y = ∑ i ∈ univ.erase 0, d (x i) (y i) := by
    unfold inactive
    rw [← sum_erase_add _ _ (mem_univ 0)]
    simp only [Fin.val_zero, ↓reduceIte, add_zero]
    exact sum_congr rfl (fun i hi => ite_eq_right (fun h => (mem_erase.mp hi).1 (Fin.ext h)))
  rw [← eqn]
  refine (hb x y hh).trans ?_
  unfold radius
  linarith only [show 0 ≤ t * B by positivity]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # Dyadic folding and the quadratic tradeoff on a finite grid -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Filter Prices.Motion Interior

/-- Approximation on a fixed number of registers, uniformly for every
sufficiently large alphabet and every decoder. -/
def Folds (K : ℝ) : Prop :=
  ∀ (F : Type) [Field F] (k : ℕ) (η : ℝ), 0 < η → η ^ 2 < (2 : ℝ) ^ k / 2 →
    ∀ᶠ N : ℕ in atTop, ∀ B : Matrix (Fin N) (Fin N) F, ∃ A,
      Low (matPower (fun _ : Fin (2 ^ k) => B) - A) ((N : ℝ) ^ ((2 : ℝ) ^ k - η ^ 2)) ∧
      Rows A ((N : ℝ) ^ (3 + K * η * Real.sqrt ((2 : ℝ) ^ k)))

variable {K : ℝ} {F : Type} [Field F]

/-- With at least the reciprocal of the loss in registers, the constant
cost of the last free register fits in the square-root envelope. -/
theorem Folds.grid (h : Folds K) (hK : 1 ≤ K) (k : ℕ) {r : ℝ}
    (hr : 0 < r) (hr' : r ≤ 1) (hk : 1 ≤ r * (2 : ℝ) ^ k) :
    ∀ᶠ d : ℕ in atTop, ∀ M : Matrix (Fin d) (Fin d) F, ∃ A,
      Low (matPower (fun _ : Fin (2 ^ k) => M) - A) (((d : ℝ) ^ (2 ^ k : ℕ)) ^ (1 - r)) ∧
      Rows A (((d : ℝ) ^ (2 ^ k : ℕ)) ^ ((K + 4) * Real.sqrt r)) := by
  let m := (2 : ℝ) ^ k
  have hm : 0 < m := by unfold m; positivity
  have hs : r ≤ Real.sqrt r := (Real.le_sqrt hr.le hr.le).mpr (by nlinarith)
  by_cases hlarge : 1 / 2 ≤ r
  · filter_upwards [eventually_ge_atTop 1] with d hd M
    have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
    let P := matPower (fun _ : Fin (2 ^ k) => M)
    refine ⟨P, by unfold P; rw [sub_self]; exact Low.zero.mono (by positivity), (Rows.bound P).mono ?_⟩
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    exact Real.self_le_rpow_of_one_le (one_le_pow₀ hd') (by nlinarith)
  let η := Real.sqrt (r * m)
  have ht : η ^ 2 = r * m := Real.sq_sqrt (by positivity)
  have he : η * Real.sqrt m = Real.sqrt r * m := by
    rw [show η = Real.sqrt r * Real.sqrt m from Real.sqrt_mul hr.le _, mul_assoc,
      Real.mul_self_sqrt hm.le]
  have hsmall : η ^ 2 < m / 2 := by rw [ht]; nlinarith
  filter_upwards [eventually_ge_atTop 1, h F k η (by unfold η; positivity) hsmall] with d hd hh M
  have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  obtain ⟨A, hA, hB⟩ := hh M
  have hc (z : ℝ) : ((d : ℝ) ^ (2 ^ k : ℕ)) ^ z = (d : ℝ) ^ (m * z) := by
    rw [← Real.rpow_natCast_mul (by positivity), Nat.cast_pow, Nat.cast_ofNat]
  refine ⟨A, ?_, hB.mono ?_⟩
  · rw [hc, show m * (1 - r) = m - η ^ 2 by rw [ht]; ring]
    exact hA
  · rw [hc]
    apply Real.rpow_le_rpow_of_exponent_le hd'
    change 3 + K * η * Real.sqrt m ≤ m * ((K + 4) * Real.sqrt r)
    rw [mul_assoc, he]
    have hb : 1 ≤ Real.sqrt r * m := hk.trans (mul_le_mul_of_nonneg_right hs hm.le)
    linarith

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # Parity elimination on graded finite partially ordered sets -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Finset Prices.Motion
open scoped Classical

structure Order (X : Type) where
  rel : X → X → Prop
  grade : X → ℕ
  refl : ∀ x, rel x x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z
  inc : ∀ {x y}, rel x y → x ≠ y → grade x < grade y

namespace Order
variable {X F : Type} [Field F] (o : Order X)

def Unitriangular (A : Matrix X X F) : Prop :=
  (∀ x, A x x = 1) ∧ ∀ x y, A x y ≠ 0 → o.rel x y

def block : Order (Block X) where
  rel x y := ∀ i, o.rel (x i) (y i)
  grade := blockGrade o.grade
  refl _ _ := o.refl _
  trans h k i := o.trans (h i) (k i)
  inc {x y} h h' := by
    apply sum_lt_sum
    · intro i _
      by_cases he : x i = y i
      · rw [he]
      · exact (o.inc (h i) he).le
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h'
      exact ⟨i, mem_univ _, o.inc (h i) hi⟩

theorem block_unit {A : Matrix X X F} (h : o.Unitriangular A) :
    o.block.Unitriangular (matPower (fun _ : Fin 100 => A)) := by
  refine ⟨fun x => prod_eq_one (fun _ _ => h.1 _), fun x y hxy i => ?_⟩
  exact h.2 _ _ (prod_ne_zero_iff.mp hxy i (mem_univ _))

def parity (x : X) := o.grade x % 2

def middle : Order X where
  rel x y := o.rel x y ∧ o.parity x = o.parity y
  grade x := o.grade x / 2
  refl x := ⟨o.refl x, rfl⟩
  trans h k := ⟨o.trans h.1 k.1, h.2.trans k.2⟩
  inc h he := by have := o.inc h.1 he; unfold parity at h; omega

def outer (a : ℕ) : Order X where
  rel x y := o.rel x y ∧ (x = y ∨ o.parity x = a ∧ o.parity y ≠ a)
  grade x := if o.parity x = a then 0 else 1
  refl x := ⟨o.refl x, Or.inl rfl⟩
  trans h k := ⟨o.trans h.1 k.1, by grind⟩
  inc h he := by obtain ⟨h₁, h₂⟩ := h.2.resolve_left he; simp [h₁, h₂]

private def Piece (a b : ℕ) (P : Matrix X X F) : Prop :=
  ∀ x y, P x y ≠ 0 → o.rel x y ∧ o.grade x < o.grade y ∧ o.parity x = a ∧ o.parity y = b

variable {o} {a b c e : ℕ} {P Q : Matrix X X F}

private theorem Piece.zero : o.Piece a b (0 : Matrix X X F) := by simp [Piece]

private theorem Piece.sub (h : o.Piece a b P) (k : o.Piece a b Q) : o.Piece a b (P - Q) := by
  intro x y hn
  by_cases he : P x y = 0
  · exact k x y (by simpa [he] using hn)
  · exact h x y he

private theorem Piece.diag (h : o.Piece a b P) (x : X) : P x x = 0 := by
  by_contra he; exact (h x x he).2.1.false

private theorem Piece.out (h : o.Piece a b P) (hab : b ≠ a) :
    (o.outer a).Unitriangular (1 + P) := by
  refine ⟨fun x => by simp [h.diag], ?_⟩
  intro x y hh
  by_cases he : x = y
  · subst y; exact (o.outer a).refl _
  obtain ⟨hr, _, ha, hb⟩ := h x y (by simpa [he] using hh)
  exact ⟨hr, Or.inr ⟨ha, hb.trans_ne hab⟩⟩

variable [Fintype X]

private theorem Piece.mul (h : o.Piece a b P) (k : o.Piece b c Q) : o.Piece a c (P * Q) := by
  intro x y hn
  obtain ⟨z, _, hz⟩ := exists_ne_zero_of_sum_ne_zero hn
  obtain ⟨h₁, h₂, h₃, _⟩ := h x z (left_ne_zero_of_mul hz)
  obtain ⟨k₁, k₂, _, k₃⟩ := k z y (right_ne_zero_of_mul hz)
  exact ⟨o.trans h₁ k₁, h₂.trans k₂, h₃, k₃⟩

private theorem Piece.mul_mismatch (h : o.Piece a b P) (k : o.Piece c e Q) (hne : b ≠ c) :
    P * Q = 0 := by
  ext x y
  by_contra hn
  obtain ⟨z, _, hz⟩ := exists_ne_zero_of_sum_ne_zero hn
  exact hne ((h x z (left_ne_zero_of_mul hz)).2.2.2.symm.trans (k z y (right_ne_zero_of_mul hz)).2.2.1)

private theorem Piece.nil (h : o.Piece a a P) : ∃ n : ℕ, P ^ n = 0 := by
  have hh (n : ℕ) (x y : X) (hn : (P ^ n) x y ≠ 0) : o.grade x + n ≤ o.grade y := by
    induction n generalizing y with
    | zero =>
      have : x = y := by simpa [Matrix.one_apply] using hn
      simp [this]
    | succ n ih =>
      rw [pow_succ, Matrix.mul_apply] at hn
      obtain ⟨z, _, hz⟩ := exists_ne_zero_of_sum_ne_zero hn
      exact Nat.succ_le_of_lt ((ih z (left_ne_zero_of_mul hz)).trans_lt (h z y (right_ne_zero_of_mul hz)).2.1)
  refine ⟨univ.sup o.grade + 1, ?_⟩
  ext x y
  by_contra he
  have := hh _ x y he
  have := Finset.le_sup (f := o.grade) (mem_univ y)
  omega

private theorem Piece.solve_right (h : o.Piece a a P) (k : o.Piece b a Q) :
    ∃ T, o.Piece b a T ∧ T + T * P = Q := by
  obtain ⟨n, hn⟩ := h.nil
  have he : Q * P ^ n = 0 := by rw [hn, mul_zero]
  clear hn
  induction n generalizing Q with
  | zero =>
    rw [pow_zero, mul_one] at he
    exact ⟨0, Piece.zero, by simp [he]⟩
  | succ n ih =>
    rw [pow_succ', ← mul_assoc] at he
    obtain ⟨T, hT, ht⟩ := ih (k.mul h) he
    exact ⟨Q - T, k.sub hT, by rw [sub_mul, ← ht]; abel⟩

private theorem Piece.solve_left (h : o.Piece a a P) (k : o.Piece a b Q) :
    ∃ T, o.Piece a b T ∧ T + P * T = Q := by
  obtain ⟨n, hn⟩ := h.nil
  have he : P ^ n * Q = 0 := by rw [hn, zero_mul]
  clear hn
  induction n generalizing Q with
  | zero =>
    rw [pow_zero, one_mul] at he
    exact ⟨0, Piece.zero, by simp [he]⟩
  | succ n ih =>
    rw [pow_succ, mul_assoc] at he
    obtain ⟨T, hT, ht⟩ := ih (h.mul k) he
    exact ⟨Q - T, k.sub hT, by rw [mul_sub, ← ht]; abel⟩

/-- Even–odd elimination. The off-diagonal factors have binary
grades and the remaining factor halves the original grade. -/
theorem factor {A : Matrix X X F} (h : o.Unitriangular A) :
    ∃ L M R : Matrix X X F, (o.outer 1).Unitriangular L ∧ o.middle.Unitriangular M ∧
      (o.outer 0).Unitriangular R ∧ A = L * M * R := by
  let B (a b : ℕ) : Matrix X X F := fun x y =>
    if x ≠ y ∧ o.parity x = a ∧ o.parity y = b then A x y else 0
  have hp a b : o.Piece a b (B a b) := by
    intro x y hn
    unfold B at hn
    split at hn
    · rename_i he
      have hr := h.2 x y hn
      exact ⟨hr, o.inc hr he.1, he.2⟩
    · contradiction
  have he : A = 1 + B 0 0 + B 1 1 + B 1 0 + B 0 1 := by
    have par (x : X) : o.parity x = 0 ∨ o.parity x = 1 := by unfold parity; omega
    ext x y
    simp only [Matrix.add_apply, Matrix.one_apply]
    by_cases hh : x = y
    · subst y; simp [B, h.1]
    rcases par x with hx|hx <;> rcases par y with hy|hy <;> simp [B, hx, hy, hh]
  obtain ⟨L, hL, hL'⟩ := (hp 0 0).solve_right (hp 1 0)
  obtain ⟨R, hR, hR'⟩ := (hp 0 0).solve_left (hp 0 1)
  let Z := B 1 1 - L * B 0 1
  have hZ : o.Piece 1 1 Z := (hp 1 1).sub (hL.mul (hp 0 1))
  refine ⟨1 + L, 1 + B 0 0 + Z, 1 + R, hL.out (by decide), ?_, hR.out (by decide), ?_⟩
  · refine ⟨fun x => by simp [(hp 0 0).diag, hZ.diag], ?_⟩
    intro x y hn
    by_cases hh : x = y
    · subst y; exact o.middle.refl _
    by_cases hz : Z x y = 0
    · obtain ⟨hr, _, ha, hb⟩ := hp 0 0 x y (by simpa [hh, hz] using hn)
      exact ⟨hr, ha.trans hb.symm⟩
    · obtain ⟨hr, _, ha, hb⟩ := hZ x y hz
      exact ⟨hr, ha.trans hb.symm⟩
  · have h₁ := hL.mul_mismatch hZ (by decide)
    have h₂ := hZ.mul_mismatch hR (by decide)
    calc
      A = 1 + B 0 0 + Z + (L + L * B 0 0) + (R + B 0 0 * R) + L * (R + B 0 0 * R) := by
        rw [hL', hR', he]; unfold Z; abel
      _ = (1 + L) * (1 + B 0 0 + Z) * (1 + R) := by
        simp only [add_mul, mul_add, mul_one, one_mul, h₁, h₂, add_zero, mul_assoc]
        abel

end Order
end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end
