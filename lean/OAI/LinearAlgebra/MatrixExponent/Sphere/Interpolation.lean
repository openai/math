import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas

section
/-!
# Translation of a contraction at a nilpotent parameter

The negative binomial expansion truncates because the parameter is nilpotent.
All coefficients are integral and the proof uses no division.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

open Finset

variable {R : Type*} [CommRing R]

private theorem negative_binomial (x : R) (N : ℕ) (hx : x ^ N = 0) (q : ℕ) :
    (∑ j ∈ range N, x ^ j * (j + q).choose q) * (1 - x) ^ (q + 1) = 1 := by
  induction q with
  | zero => simpa [hx] using geom_sum_mul_neg x N
  | succ q ih =>
    let h (j : ℕ) := x ^ j * (j + q).choose (q + 1)
    have recu : (∑ j ∈ range N, x ^ j * (j + (q + 1)).choose (q + 1)) * (1 - x) =
        ∑ j ∈ range N, x ^ j * (j + q).choose q := by
      apply sub_eq_zero.mp
      rw [sum_mul, ← sum_sub_distrib]
      calc
        _ = ∑ j ∈ range N, (h j - h (j + 1)) := by
          apply sum_congr rfl
          intro j _
          unfold h
          rw [show j + 1 + q = j + (q + 1) by omega, ← Nat.add_assoc,
            Nat.choose_succ_succ, Nat.cast_add, pow_succ]
          ring
        _ = h 0 - h N := sum_range_sub' _ _
        _ = 0 := by simp [h, hx]
    rw [pow_succ', ← mul_assoc, recu, ih]

/-- Translation of the mode at the moving point against one fixed spectator. -/
theorem kernel_translate (u z a : R) (N m n : ℕ) (hu : u ^ N = 0) :
    (∑ f ∈ range N, u ^ (2 * f + 1) * (f.choose m : R) * ((f + n).choose n : R) * z ^ (f + n + 1) * a ^ (f - m)) *
        (1 - a * u ^ 2 * z) ^ (m + n + 1) = u ^ (2 * m + 1) * ((m + n).choose n : R) * z ^ (m + n + 1) := by
  let g (f : ℕ) := u ^ (2 * f + 1) * (f.choose m : R) * ((f + n).choose n : R) * z ^ (f + n + 1) * a ^ (f - m)
  have head : ∑ f ∈ range m, g f = 0 := by
    apply sum_eq_zero
    intro f hf
    simp [g, Nat.choose_eq_zero_of_lt (mem_range.mp hf)]
  have tail : ∑ j ∈ range m, g (N + j) = 0 := by
    apply sum_eq_zero
    intro j _
    unfold g
    rw [pow_eq_zero_of_le (by omega : N ≤ 2 * (N + j) + 1) hu]
    simp
  have shift : ∑ f ∈ range N, g f = ∑ j ∈ range N, g (m + j) := by
    rw [← add_zero (∑ f ∈ range N, g f), ← tail, ← sum_range_add, Nat.add_comm N m,
      sum_range_add, head, zero_add]
  let c := u ^ (2 * m + 1) * ((m + n).choose n : R) * z ^ (m + n + 1)
  have term (j : ℕ) : g (m + j) = c * ((a * u ^ 2 * z) ^ j * (j + (m + n)).choose (m + n)) := by
    have hc : (m + j).choose m * (m + j + n).choose n =
        (m + n).choose n * (j + (m + n)).choose (m + n) := by
      rw [show j + (m + n) = m + j + n by omega, Nat.mul_comm ((m + n).choose n),
        Nat.choose_mul (Nat.le_add_left n m)]
      simp [Nat.mul_comm]
    unfold g c
    rw [mul_assoc (u ^ _), ← Nat.cast_mul, hc, Nat.cast_mul,
      show 2 * (m + j) + 1 = 2 * m + 1 + 2 * j by omega, show m + j + n + 1 = m + n + 1 + j by omega,
      pow_add u (2 * m + 1), pow_add z (m + n + 1), mul_pow, mul_pow, pow_mul, Nat.add_sub_cancel_left]
    ring
  have hx : (a * u ^ 2 * z) ^ N = 0 := by
    rw [mul_pow, mul_pow, ← pow_mul, pow_eq_zero_of_le (by omega : N ≤ 2 * N) hu, mul_zero, zero_mul]
  change (∑ f ∈ range N, g f) * _ = c
  rw [shift]
  simp_rw [term]
  rw [← mul_sum, mul_assoc, negative_binomial _ _ hx, mul_one]

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# The two binomial transforms at the middle site

Vandermonde's identity and a finite difference of a row of Pascal's
triangle give integral identities, valid also after reduction modulo two.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

open Finset

theorem binom_forward (K : Type*) [CommRing K] (m b : ℕ) :
    (∑ f ∈ range (m + 1), (m.choose f : K) * b.choose f) = (b + m).choose m := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.cast_sum]
  apply sum_congr rfl
  intro f hf
  rw [Nat.choose_symm (mem_range_succ_iff.mp hf), Nat.cast_mul, mul_comm]

/-- A signed difference raises the offset of the lower binomial index by one. -/
theorem binom_difference (K : Type*) [CommRing K] (m b d : ℕ) :
    (∑ f ∈ range (m + 1), (m.choose f : K) * ((-1) ^ f * (b + f).choose (f + d))) =
      (-1 : K) ^ m * b.choose (m + d) := by
  induction m generalizing d with
  | zero => simp
  | succ m ih =>
    rw [sum_choose_succ_mul (fun f _ => (-1 : K) ^ f * (b + f).choose (f + d)) m,
      ← sum_add_distrib]
    calc
      _ = -(∑ f ∈ range (m + 1), (m.choose f : K) * ((-1) ^ f * (b + f).choose (f + (d + 1)))) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro f _
        rw [show f + 1 + d = (f + d) + 1 by omega, ← Nat.add_assoc b f 1, Nat.choose_succ_succ,
          Nat.cast_add, pow_succ, ← Nat.add_assoc f d 1]
        ring
      _ = _ := by rw [ih, pow_succ, show m + 1 + d = m + (d + 1) by omega]; ring

theorem binom_backward (K : Type*) [CommRing K] (m b : ℕ) :
    (∑ f ∈ range (m + 1), (-1 : K) ^ f * m.choose f * (b + f).choose f) =
      (-1 : K) ^ m * b.choose m := by
  simpa only [Nat.add_zero, mul_left_comm, mul_assoc] using binom_difference K m b 0

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# The three-point fermion kernel

The points are zero, one and infinity. The infinity pairing uses the
ordinary dual basis, with no factor of a square root of minus one.
`dual` denotes a triangular change of modes at the middle point.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

abbrev Mode (r : ℕ) := Fin r × ℕ

/-- Twice the energy of a word of generators. -/
def energy {r : ℕ} (x : List (Mode r)) : ℕ :=
  (x.map fun i => 2 * i.2 + 1).sum

inductive Chart
  | origin | middle | dual | infinity
  deriving DecidableEq

def Chart.reflect : Chart → Chart
  | .origin => .infinity
  | .middle => .dual
  | .dual => .middle
  | .infinity => .origin

abbrev Mark (r : ℕ) := Chart × Mode r

variable (R : Type*) [CommRing R] {r : ℕ}

private def near (l m : ℕ) : R := (-1) ^ m * (l + m).choose m

private def kernel (s t : Chart) (l m : ℕ) : R :=
  match s, t with
  | .origin, .middle => near R l m
  | .middle, .origin => -near R m l
  | .origin, .infinity => if l = m then 1 else 0
  | .infinity, .origin => -(if l = m then 1 else 0)
  | .middle, .infinity => m.choose l
  | .infinity, .middle => -(l.choose m : R)
  | .origin, .dual => l.choose m
  | .dual, .origin => -(m.choose l : R)
  | .dual, .infinity => near R m l
  | .infinity, .dual => -near R l m
  | _, _ => 0

def pairing (x y : Mark r) : R :=
  if x.2.1 = y.2.1 then kernel R x.1 y.1 x.2.2 y.2.2 else 0

theorem pairing_self (x : Mark r) : pairing R x x = 0 := by
  obtain ⟨s, x⟩ := x
  cases s <;> simp [pairing, kernel]

theorem pairing_skew (x y : Mark r) : pairing R y x = -pairing R x y := by
  obtain ⟨s, i, l⟩ := x
  obtain ⟨t, j, m⟩ := y
  by_cases h : i = j
  · subst j
    cases s <;> cases t <;> simp [pairing, kernel, eq_comm]
  · simp [pairing, h, Ne.symm h]

def reflect (x : Mark r) : Mark r := (x.1.reflect, x.2)

theorem pairing_reflect (x y : Mark r) :
    pairing R (reflect x) (reflect y) = -pairing R x y := by
  obtain ⟨s, i, l⟩ := x
  obtain ⟨t, j, m⟩ := y
  by_cases h : i = j
  · subst j
    cases s <;> cases t <;> simp [pairing, kernel, reflect, Chart.reflect] <;> rfl
  · simp [pairing, reflect, h]

def lower (m f : ℕ) : R := (-1) ^ m * m.choose f

/-- The reflected modes are integral combinations of modes of no greater
energy. Both binomial identities hold after reduction in any characteristic. -/
theorem pairing_lower (x : Mode r) (y : Mark r) :
    pairing R (.dual, x) y = ∑ f ∈ Finset.range (x.2 + 1),
      lower R x.2 f * pairing R (.middle, x.1, f) y := by
  obtain ⟨i, m⟩ := x
  obtain ⟨t, j, b⟩ := y
  by_cases h : i = j
  · subst j
    cases t <;> simp only [pairing, kernel, ↓reduceIte, mul_zero, Finset.sum_const_zero]
    · simp only [near, lower]
      have he (f : ℕ) :
          (-1 : R) ^ m * m.choose f * -((-1) ^ f * (b + f).choose f) =
            -((-1) ^ m) * ((-1) ^ f * m.choose f * (b + f).choose f) := by ring
      simp_rw [he]
      rw [← Finset.mul_sum, binom_backward, neg_mul, ← mul_assoc, ← mul_pow]
      simp
    · simp only [near, lower, mul_assoc, ← Finset.mul_sum, binom_forward]
  · simp [pairing, h]

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# The sphere kernel and motion of one site

A mode contraction is polynomial in the reciprocal separation. For a
nilpotent displacement `u²`, the translated separation can be inverted
exactly by a finite geometric sum.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

open Finset

variable {R : Type*} [CommRing R] {F : Type*} [Field F] {r : ℕ}

def coeff (x y : Mode r) (z : R) : R :=
  if x.1 = y.1 then (-1) ^ y.2 * (x.2 + y.2).choose y.2 * z ^ (x.2 + y.2 + 1) else 0

def shift (u z : R) (N : ℕ) := z * ∑ i ∈ range N, (u ^ 2 * z) ^ i

def shifted (u z a : R) (N : ℕ) := z * ∑ i ∈ range N, (a * u ^ 2 * z) ^ i

abbrev Site (F : Type*) (r : ℕ) := F × Mode r

def fieldKernel (x y : Site F r) : F := coeff x.2 y.2 (y.1 - x.1)⁻¹

theorem coeff_skew (x y : Mode r) (z : R) : coeff y x (-z) = -coeff x y z := by
  unfold coeff
  by_cases h : x.1 = y.1
  · rw [ite_eq_left h.symm, ite_eq_left h, Nat.add_comm y.2 x.2, Nat.choose_symm_add, neg_pow z]
    have hs : (-1 : R) ^ x.2 * (-1) ^ (x.2 + y.2 + 1) = -(-1) ^ y.2 := by
      rw [pow_succ, pow_add, ← mul_assoc, ← mul_assoc, ← mul_pow]
      simp
    rw [mul_mul_mul_comm, hs, neg_mul, mul_assoc]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, neg_zero]

theorem fieldKernel_skew (x y : Site F r) : fieldKernel y x = -fieldKernel x y := by
  unfold fieldKernel
  rw [← neg_sub y.1 x.1, inv_neg, coeff_skew]

theorem fieldKernel_self (x : Site F r) : fieldKernel x x = 0 := by
  simp [fieldKernel, coeff, pow_succ]

private theorem geom_inv (u z a : R) (N : ℕ) (hu : u ^ N = 0) :
    (∑ i ∈ range N, (a * u ^ 2 * z) ^ i) * (1 - a * u ^ 2 * z) = 1 := by
  rw [geom_sum_mul_neg, mul_pow, mul_pow, ← pow_mul, pow_eq_zero_of_le (by omega : N ≤ 2 * N) hu,
    mul_zero, zero_mul, sub_zero]

theorem shifted_mul (u z a : R) (N : ℕ) (hu : u ^ N = 0) : shifted u z a N * (1 - a * u ^ 2 * z) = z := by
  rw [shifted, mul_assoc, geom_inv u z a N hu, mul_one]

/-- Expand the moving mode at the center, with its doubled-energy weight. -/
theorem coeff_shifted (u z a : R) (N : ℕ) (hu : u ^ N = 0) (x y : Mode r) :
    u ^ (2 * x.2 + 1) * coeff x y (shifted u z a N) =
      ∑ f ∈ range N, u ^ (2 * f + 1) * (f.choose x.2 : R) * a ^ (f - x.2) * coeff (x.1, f) y z := by
  by_cases h : x.1 = y.1
  · let G := ∑ i ∈ range N, (a * u ^ 2 * z) ^ i
    let d := x.2 + y.2 + 1
    have hi : (1 - a * u ^ 2 * z) ^ d * G ^ d = 1 := by
      rw [← mul_pow, mul_comm, geom_inv u z a N hu, one_pow]
    let T := ∑ f ∈ range N, u ^ (2 * f + 1) * (f.choose x.2 : R) * (f + y.2).choose y.2 * z ^ (f + y.2 + 1) * a ^ (f - x.2)
    have ht : T * (1 - a * u ^ 2 * z) ^ d = u ^ (2 * x.2 + 1) * ((x.2 + y.2).choose y.2 : R) * z ^ d :=
      kernel_translate u z a N x.2 y.2 hu
    simp only [coeff, ite_eq_left h]
    calc
      _ = (-1) ^ y.2 * ((u ^ (2 * x.2 + 1) * ((x.2 + y.2).choose y.2 : R) * z ^ d) * G ^ d) := by
        unfold shifted G d
        rw [mul_pow]
        ring
      _ = (-1) ^ y.2 * T := by rw [← ht, mul_assoc T, hi, mul_one]
      _ = _ := by
        unfold T
        rw [mul_sum]
        apply sum_congr rfl
        intro f _
        ring
  · simp [coeff, h]

theorem coeff_shift (u z : R) (N : ℕ) (hu : u ^ N = 0) (x y : Mode r) :
    u ^ (2 * x.2 + 1) * coeff x y (shift u z N) =
      ∑ f ∈ range N, (u ^ (2 * f + 1) * (f.choose x.2 : R)) * coeff (x.1, f) y z := by
  simpa only [shift, shifted, one_mul, one_pow, mul_one] using coeff_shifted u z 1 N hu x y

theorem shift_mul (u z : R) (N : ℕ) (hu : u ^ N = 0) : shift u z N * (1 - u ^ 2 * z) = z := by
  simpa only [shift, shifted, one_mul] using shifted_mul u z 1 N hu

/-- Composing displacements of the reciprocal separation adds their offsets. -/
theorem shifted_add (u z a b : R) (N : ℕ) (hu : u ^ N = 0) :
    shifted u (shifted u z a N) b N = shifted u z (a + b) N := by
  let z' := shifted u z a N
  have ha : z' * (1 - a * u ^ 2 * z) = z := shifted_mul _ _ _ _ hu
  have hprod : (1 - b * u ^ 2 * z') * (1 - a * u ^ 2 * z) = 1 - (a + b) * u ^ 2 * z := by
    rw [sub_mul, one_mul, mul_assoc (b * u ^ 2), ha]
    ring
  have hab : shifted u z' b N * (1 - (a + b) * u ^ 2 * z) = z := by
    rw [← hprod, ← mul_assoc, shifted_mul _ _ _ _ hu, ha]
  let G := ∑ i ∈ range N, ((a + b) * u ^ 2 * z) ^ i
  change shifted u z' b N = z * G
  rw [← hab, mul_assoc, mul_comm (1 - _) G, geom_inv u z (a + b) N hu, mul_one]

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# Interpolation at auxiliary marks

Clearing common denominators converts vanishing at the auxiliary marks to
a polynomial identity. Evaluating it at a pole of maximal order isolates
one coefficient. This argument works in every characteristic.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

open Finset Polynomial

variable {F A B : Type*} [Field F] [Fintype A]

theorem span_of_separates (v : B → A → F)
    (h : ∀ c : A → F, (∀ b, ∑ i, c i * v b i = 0) → c = 0) :
    Submodule.span F (Set.range v) = ⊤ := by
  classical
  by_contra hn
  obtain ⟨φ, hφ, hz⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hn)
    inferInstance
  let c i := φ (Pi.basisFun F A i)
  have he (x : A → F) : ∑ i, c i * x i = φ x := by
    conv_rhs => rw [← (Pi.basisFun F A).sum_repr x, map_sum]
    simp only [map_smul, Pi.basisFun_repr, smul_eq_mul, mul_comm, c]
  have hc : c = 0 := h c fun b => by
    rw [he, ← Submodule.mem_bot F, ← hz]
    exact ⟨v b, Submodule.subset_span ⟨b, rfl⟩, rfl⟩
  apply hφ
  apply LinearMap.ext
  intro x
  simp [← he, hc]

/-- The total pole order suffices, even if the bound varies by site. -/
theorem cauchy_span_degrees [Fintype B] (a : A ↪ F × ℕ) (z : B ↪ F)
    (V : Finset F) (q : F → ℕ) (hV : ∀ i, (a i).1 ∈ V) (ha : ∀ i, (a i).2 < q (a i).1)
    (hz : ∀ j i, z j ≠ (a i).1) (hcard : (∑ x ∈ V, q x) ≤ Fintype.card B) :
    Submodule.span F (Set.range (fun j i => (z j - (a i).1)⁻¹ ^ ((a i).2 + 1))) = ⊤ := by
  classical
  apply span_of_separates
  intro c hc
  by_contra hne
  let s := univ.filter fun i => c i ≠ 0
  have hs : s.Nonempty := by
    contrapose! hne
    funext i
    have : i ∉ s := by rw [hne]; simp
    simpa [s] using this
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun t => (a t).2) hs
  let d := Function.update q (a i).1 ((a i).2 + 1)
  have hdi : d (a i).1 = (a i).2 + 1 := Function.update_self _ _ _
  have hdq (x : F) : d x ≤ q x := by
    by_cases h : x = (a i).1
    · subst x; rw [hdi]; exact ha i
    · simp [d, h]
  let m j := d (a j).1 - ((a j).2 + 1)
  have hm (j : A) (hj : j ∈ s) : (a j).2 + 1 + m j = d (a j).1 := by
    apply Nat.add_sub_of_le
    by_cases h : (a j).1 = (a i).1
    · rw [h, hdi]; exact Nat.succ_le_succ (hmax j hj)
    · rw [show d (a j).1 = q (a j).1 from Function.update_of_ne h _ _]; exact ha j
  let p (j : A) := C (c j) * (X - C (a j).1) ^ (m j) *
    ∏ x ∈ V.erase (a j).1, (X - C x) ^ d x
  let P := ∑ j ∈ s, p j
  have hdeg (x : F) (k : ℕ) : ((X - C x) ^ k).natDegree = k := by
    rw [Polynomial.natDegree_pow, natDegree_X_sub_C, mul_one]
  have hpdeg (j : A) (hj : j ∈ s) : (p j).natDegree < ∑ x ∈ V, q x := calc
    _ ≤ m j + ∑ x ∈ V.erase (a j).1, d x := by
      apply natDegree_mul_le.trans
      apply Nat.add_le_add
      · exact (natDegree_C_mul_le _ _).trans_eq (hdeg _ _)
      · refine (natDegree_prod_le _ _).trans_eq ?_
        simp only [hdeg]
    _ < ∑ x ∈ V, d x := by
      rw [← add_sum_erase V d (hV j)]
      have := hm j hj
      omega
    _ ≤ _ := sum_le_sum fun x _ => hdq x
  have hd : P.natDegree < ∑ x ∈ V, q x := by
    have hb : P.natDegree ≤ (∑ x ∈ V, q x) - 1 :=
      natDegree_sum_le_of_forall_le _ _ (fun j hj => Nat.le_sub_one_of_lt (hpdeg j hj))
    have := hpdeg i hi
    omega
  have ev (x : F) (j : A) :
      (p j).eval x = c j * (x - (a j).1) ^ (m j) *
        ∏ y ∈ V.erase (a j).1, (x - y) ^ d y := by
    simp [p, eval_prod]
  have he (b : B) : P.eval (z b) = 0 := by
    have hc' : ∑ j ∈ s, c j * (z b - (a j).1)⁻¹ ^ ((a j).2 + 1) = 0 := by
      rw [← hc b]
      apply sum_subset (subset_univ _)
      intro j _ hj
      have : c j = 0 := by simpa [s] using hj
      simp [this]
    rw [show P = ∑ j ∈ s, p j from rfl, eval_finsetSum]
    calc
      _ = (∑ j ∈ s, c j * (z b - (a j).1)⁻¹ ^ ((a j).2 + 1)) *
          ∏ x ∈ V, (z b - x) ^ d x := by
        rw [sum_mul]
        apply sum_congr rfl
        intro j hj
        have hp : (z b - (a j).1) ^ d (a j).1 =
            (z b - (a j).1) ^ ((a j).2 + 1) * (z b - (a j).1) ^ (m j) := by
          rw [← pow_add, hm j hj]
        rw [ev, ← mul_prod_erase V (fun x => (z b - x) ^ d x) (hV j), hp, inv_pow]
        simp only [mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ (sub_ne_zero.mpr (hz b j)))]
      _ = 0 := by rw [hc', zero_mul]
  have hp := eq_zero_of_natDegree_lt_card_of_eval_eq_zero P z.injective he (hd.trans_le hcard)
  have hv : P.eval (a i).1 = (p i).eval (a i).1 := by
    rw [show P = ∑ j ∈ s, p j from rfl, eval_finsetSum]
    apply sum_eq_single_of_mem i hi
    intro j hj hji
    rw [ev]
    by_cases h : (a j).1 = (a i).1
    · have hn : (a j).2 ≠ (a i).2 := fun he => hji (a.injective (Prod.ext h he))
      have hmj : m j ≠ 0 := by have := hm j hj; rw [h, hdi] at this; omega
      simp [h, hmj]
    · rw [prod_eq_zero (mem_erase.mpr ⟨Ne.symm h, hV i⟩) (by simp [hdi]), mul_zero]
  have hn : (p i).eval (a i).1 ≠ 0 := by
    rw [ev, show m i = 0 by simp [m, hdi], pow_zero, mul_one]
    refine mul_ne_zero (mem_filter.mp hi).2 (prod_ne_zero_iff.mpr ?_)
    intro x hx
    exact pow_ne_zero _ (sub_ne_zero.mpr (mem_erase.mp hx).1.symm)
  exact hn (by rw [← hv, hp, eval_zero])

/-- Sufficiently many pole-free evaluations span all covectors on distinct
pairs of a pole and a mode. The bound on the number of points is polynomial. -/
theorem cauchy_span [Fintype B] (a : A ↪ F × ℕ) (z : B ↪ F) (q : ℕ)
    (ha : ∀ i, (a i).2 < q) (hz : ∀ j i, z j ≠ (a i).1)
    (hcard : (1 + Fintype.card A) * q < Fintype.card B) :
    Submodule.span F (Set.range (fun j i => (z j - (a i).1)⁻¹ ^ ((a i).2 + 1))) = ⊤ := by
  classical
  let V := univ.image (fun i => (a i).1)
  apply cauchy_span_degrees a z V (fun _ => q) (fun j => mem_image_of_mem _ (mem_univ j)) ha hz
  simp only [sum_const, Nat.nsmul_eq_mul]
  exact (Nat.mul_le_mul_right q (card_image_le.trans (Nat.le_add_left _ _))).trans hcard.le

end OAI.LinearAlgebra.MatrixExponent.Sphere
end
