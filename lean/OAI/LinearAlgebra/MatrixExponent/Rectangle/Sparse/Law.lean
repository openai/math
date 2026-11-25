import OAI.LinearAlgebra.MatrixExponent.Rectangle.Weights
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import OAI.LinearAlgebra.MatrixExponent.Rectangle.FiniteModel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Model
import OAI.LinearAlgebra.TensorSpectrum.TagWords
import Mathlib.Algebra.BigOperators.Field
import OAI.LinearAlgebra.TensorSpectrum.TagEntropy
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Mask

section
/-! # Decompositions of weighted rectangular products -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k i' j' k' I J K r s : ℕ}

/-- One term for every row, column and inner index. -/
theorem weighted_volume (w : Fin i → Fin j → Fin k → F) : WeightedRankLE w (i * j * k) := by
  rw [mul_right_comm i j k]
  let e : Fin (i * k * j) ≃ Pos i k × Fin j :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _))
  refine ⟨fun l x => if (e l).1 = x then 1 else 0,
    fun l y => if (e l).1.2 = y.1 ∧ (e l).2 = y.2 then 1 else 0,
    fun l z => if (e l).1.1 = z.1 ∧ (e l).2 = z.2 then w (e l).1.1 (e l).2 (e l).1.2 else 0, ?_⟩
  intro x y z
  rw [Fintype.sum_eq_single (e.symm (x, y.2))]
  · by_cases h : x.2 = y.1 <;> simp [h]
  · intro l hl
    by_cases h : (e l).1 = x
    · have h' : (e l).2 ≠ y.2 := fun h' => hl (e.eq_symm_apply.mpr (Prod.ext h h'))
      simp [h']
    · simp [h]

/-- Tensor two decompositions, allowing an arbitrary enumeration of paired
side indices. Summing over the paired terms factors the coefficient identity. -/
theorem WeightedRankLE.tensor {w : Fin i → Fin j → Fin k → F} {v : Fin i' → Fin j' → Fin k' → F}
    (h : WeightedRankLE w r) (h' : WeightedRankLE v s)
    (u : Fin I ≃ Pos i i') (q : Fin J ≃ Pos j j') (p : Fin K ≃ Pos k k') :
    WeightedRankLE (fun x y z => w (u x).1 (q y).1 (p z).1 * v (u x).2 (q y).2 (p z).2) (r * s) := by
  obtain ⟨a, b, c, h⟩ := h
  obtain ⟨a', b', c', h'⟩ := h'
  let coeff {n m g l N M : ℕ} (e : Fin N ≃ Pos n m) (f : Fin M ≃ Pos g l)
      (α : Fin r → Pos n g → F) (β : Fin s → Pos m l → F) (t : Fin (r * s)) (x : Pos N M) :=
    α (finProdFinEquiv.symm t).1 ((e x.1).1, (f x.2).1) *
      β (finProdFinEquiv.symm t).2 ((e x.1).2, (f x.2).2)
  refine ⟨coeff u p a a', coeff p q b b', coeff u q c c', ?_⟩
  intro x y z
  calc
    _ = (∑ l, a l ((u x.1).1, (p x.2).1) * b l ((p y.1).1, (q y.2).1) *
          c l ((u z.1).1, (q z.2).1)) *
        (∑ l, a' l ((u x.1).2, (p x.2).2) * b' l ((p y.1).2, (q y.2).2) *
          c' l ((u z.1).2, (q z.2).2)) := by
      rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l' _
      simp only [coeff, Equiv.symm_apply_apply]
      rw [mul_mul_mul_comm (a _ _), mul_mul_mul_comm]
    _ = _ := by
      rw [h, h', ite_mul, zero_mul, mul_ite, mul_zero, ← ite_and]
      have he {n m N : ℕ} (e : Fin N ≃ Pos n m) (u v : Fin N) :
          u = v ↔ (e u).1 = (e v).1 ∧ (e u).2 = (e v).2 :=
        e.injective.eq_iff.symm.trans Prod.ext_iff
      simp only [he u x.1 z.1, he p x.2 y.1, he q y.2 z.2, and_assoc, and_left_comm, and_comm]

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-! Permutation symmetry and the elementary area and volume bounds. -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k r : ℕ}

theorem RankLE.cycle (h : RankLE F i j k r) : RankLE F j k i r := by
  obtain ⟨a, b, c, h⟩ := h
  refine ⟨fun l x => c l x.swap, a, fun l z => b l z.swap, ?_⟩
  intro x y z
  simpa only [Prod.fst_swap, Prod.snd_swap, mul_assoc, mul_comm, mul_left_comm,
    and_assoc, and_comm, and_left_comm, eq_comm] using h y z.swap x.swap

theorem RankLE.transpose (h : RankLE F i j k r) : RankLE F j i k r := by
  obtain ⟨a, b, c, h⟩ := h
  refine ⟨fun l x => b l x.swap, fun l y => a l y.swap, fun l z => c l z.swap, ?_⟩
  intro x y z
  simpa only [Prod.fst_swap, Prod.snd_swap, mul_comm, and_assoc, and_comm, and_left_comm,
    eq_comm] using h y.swap x.swap z.swap

/-- Fixing the inner index gives an identity submatrix of the output flattening. -/
theorem RankLE.area (h : RankLE F i j k r) (hk : 0 < k) : i * j ≤ r := by
  obtain ⟨a, b, c, h⟩ := h
  let v : Fin k := ⟨0, hk⟩
  let A : Matrix (Pos i j) (Fin r) F := fun x l => a l (x.1, v) * b l (v, x.2)
  let B : Matrix (Fin r) (Pos i j) F := c
  have hAB : A * B = 1 := by
    ext x z
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa only [A, B, Prod.ext_iff, true_and] using h (x.1, v) (v, x.2) z
  have := (Matrix.rank_mul_le_left A B).trans A.rank_le_card_width
  simpa only [hAB, Matrix.rank_one, Pos, Fintype.card_prod, Fintype.card_fin] using this

/-- One product per row, column and inner index. -/
theorem rank_volume (F : Type*) [Field F] (i j k : ℕ) : RankLE F i j k (i * j * k) :=
  weighted_volume (fun (_ : Fin i) (_ : Fin j) (_ : Fin k) => (1 : F))

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-! Tensor products, powers and cyclic symmetrization of rectangular decompositions. -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F K : Type*} [Field F] [Field K] {i j k i' j' k' r s : ℕ}

theorem RankLE.map (h : RankLE F i j k r) (f : F →+* K) : RankLE K i j k r := by
  obtain ⟨a, b, c, h⟩ := h
  refine ⟨fun l x => f (a l x), fun l y => f (b l y), fun l z => f (c l z), ?_⟩
  intro x y z
  simpa only [map_sum, map_mul, apply_ite f, map_one, map_zero] using congrArg f (h x y z)

/-- Split each matrix index into two digits and multiply the corresponding
coefficients. Summing over pairs of terms factors the coefficient identity. -/
theorem RankLE.tensor (h : RankLE F i j k r) (h' : RankLE F i' j' k' s) :
    RankLE F (i * i') (j * j') (k * k') (r * s) := by
  have hw : WeightedRankLE (fun (_ : Fin i) (_ : Fin j) (_ : Fin k) => (1 : F)) r := h
  have hv : WeightedRankLE (fun (_ : Fin i') (_ : Fin j') (_ : Fin k') => (1 : F)) s := h'
  have ht := hw.tensor hv finProdFinEquiv.symm finProdFinEquiv.symm finProdFinEquiv.symm
  simp only [one_mul] at ht
  exact ht

theorem RankLE.pow (h : RankLE F i j k r) (p : ℕ) :
    RankLE F (i ^ p) (j ^ p) (k ^ p) (r ^ p) := by
  induction p with
  | zero => simpa using rank_volume F 1 1 1
  | succ p ih => simpa only [pow_succ] using ih.tensor h

/-- Tensoring the three cyclic arrangements makes all sides equal to the volume. -/
theorem RankLE.symmetrize (h : RankLE F i j k r) : MatrixExponent.RankLE F (i * j * k) (r ^ 3) := by
  change RankLE F (i * j * k) (i * j * k) (i * j * k) (r ^ 3)
  simpa only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm] using
    (h.tensor h.cycle).tensor h.cycle.cycle

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-!
# Powers of weighted products

Side indices of a power are digit strings. Coefficients multiply over
digits, so support sizes multiply and rank bounds are submultiplicative.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k r : ℕ}

theorem rankW_spec (w : Fin i → Fin j → Fin k → F) : WeightedRankLE w (rankW w) :=
  Nat.sInf_mem (show {r : ℕ | WeightedRankLE w r}.Nonempty from ⟨_, weighted_volume w⟩)

theorem rankW_le {w : Fin i → Fin j → Fin k → F} (h : WeightedRankLE w r) : rankW w ≤ r :=
  Nat.sInf_le h

@[simp] theorem WPower_one (n : ℕ) :
    WPower (fun (_ : Fin i) (_ : Fin j) (_ : Fin k) => (1 : F)) n = fun _ _ _ => 1 := by
  funext a b c
  simp [WPower]

private def split (d n m : ℕ) : Fin (d ^ (n + m)) ≃ Fin (d ^ n) × Fin (d ^ m) :=
  finFunctionFinEquiv.symm.trans ((Fin.appendEquiv n m).symm.trans
    (Equiv.prodCongr finFunctionFinEquiv finFunctionFinEquiv))

theorem rankW_add (w : Fin i → Fin j → Fin k → F) (n m : ℕ) :
    rankW (WPower w (n + m)) ≤ rankW (WPower w n) * rankW (WPower w m) := by
  apply rankW_le
  have h := (rankW_spec (WPower w n)).tensor (rankW_spec (WPower w m))
    (split i n m) (split j n m) (split k n m)
  convert h using 1
  funext a b c
  unfold WPower
  rw [Fin.prod_univ_add]
  simp [split, Fin.appendEquiv]

private theorem sum_words {n d : ℕ} (f : Fin n → Fin d → ℕ) :
    (∑ a : Fin (d ^ n), ∏ l, f l (finFunctionFinEquiv.symm a l)) = ∏ l, ∑ a, f l a := by
  rw [← finFunctionFinEquiv.sum_comp, Fintype.prod_sum]
  simp only [Equiv.symm_apply_apply]

open Classical in
private theorem indicator_prod {n : ℕ} (f : Fin n → F) :
    (if ∏ l, f l = 0 then 0 else 1) = ∏ l, if f l = 0 then (0 : ℕ) else 1 := by
  by_cases h : ∃ l, f l = 0
  · obtain ⟨l, hl⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ l) hl, ite_eq_left rfl]
    exact (Finset.prod_eq_zero (Finset.mem_univ l) (by simp [hl])).symm
  · push Not at h
    simp [h, Finset.prod_ne_zero_iff]

theorem supportSize_power (w : Fin i → Fin j → Fin k → F) (n : ℕ) :
    supportSize (WPower w n) = (supportSize w) ^ n := by
  classical
  unfold supportSize WPower
  simp_rw [indicator_prod]
  let f a b c := if w a b c = 0 then (0 : ℕ) else 1
  have h₁ (a : Fin (i ^ n)) (b : Fin (j ^ n)) :=
    sum_words (fun l c => f (finFunctionFinEquiv.symm a l) (finFunctionFinEquiv.symm b l) c)
  have h₂ (b : Fin (j ^ n)) :=
    sum_words (fun l a => ∑ c, f a (finFunctionFinEquiv.symm b l) c)
  have h₃ := sum_words (fun (_ : Fin n) b => ∑ a, ∑ c, f a b c)
  unfold f at h₁ h₂ h₃
  simp_rw [h₁, h₂, h₃]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem rankW_mul (w : Fin i → Fin j → Fin k → F) (n m : ℕ) (hm : 1 ≤ m) :
    rankW (WPower w (n * m)) ≤ (rankW (WPower w n)) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => rw [mul_one, pow_one]
  | succ m _ ih =>
    rw [Nat.mul_succ, pow_succ]
    exact (rankW_add w _ _).trans (Nat.mul_le_mul_right _ ih)

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
# Isolating triples by coloring the three alphabets

For two different labels only a fraction `1/m` of the `m`-colorings
identify them. The union bound and averaging retain at least five
sixths of the candidate triples at each of the three steps. Completion
lists always refer to the original support.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open Finset

variable {α : Type*} {i m d : ℕ}

private def collisions (m : ℕ) (x y : Fin i) :=
  univ.filter fun c : Fin i → Fin m => c x = c y

private theorem collision_bound {x y : Fin i} (h : x ≠ y) :
    (collisions m x y).card * m ≤ Fintype.card (Fin i → Fin m) := by
  let f (p : (collisions m x y) × Fin m) := Function.update p.1.val x p.2
  have hi : Function.Injective f := by
    rintro ⟨c, a⟩ ⟨c', a'⟩ he
    have ha : a = a' := by simpa [f] using congrFun he x
    have hc (z) (hz : z ≠ x) : c.val z = c'.val z := by simpa [f, hz] using congrFun he z
    have hh : c = c' := by
      apply Subtype.ext
      funext z
      by_cases hz : z = x
      · subst z
        exact (mem_filter.mp c.property).2.trans ((hc y h.symm).trans (mem_filter.mp c'.property).2.symm)
      · exact hc z hz
    exact Prod.ext hh ha
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hi

private theorem one_label (U : Finset α) (label : α → Fin i) (N : α → Finset (Fin i))
    (hd : 0 < d) (hN : ∀ t ∈ U, (N t).card ≤ d) :
    ∃ (c : Fin i → Fin (6 * d)) (V : Finset α),
      V ⊆ U ∧ 5 * U.card ≤ 6 * V.card ∧ ∀ t ∈ V, ∀ x ∈ N t, c x = c (label t) → x = label t := by
  classical
  let C := Fin i → Fin (6 * d)
  let bad (t : α) : Finset C := ((N t).erase (label t)).biUnion fun x => collisions (6 * d) x (label t)
  have hb (t) (ht : t ∈ U) : 6 * (bad t).card ≤ Fintype.card C := by
    let A := (N t).erase (label t)
    have hA : A.card ≤ d := card_erase_le.trans (hN t ht)
    apply Nat.le_of_mul_le_mul_right _ hd
    calc
      6 * (bad t).card * d = (bad t).card * (6 * d) := by ring
      _ ≤ (∑ x ∈ A, (collisions (6 * d) x (label t)).card) * (6 * d) :=
        Nat.mul_le_mul_right _ card_biUnion_le
      _ ≤ ∑ _ ∈ A, Fintype.card C := by
        rw [sum_mul]
        exact sum_le_sum (fun x hx => collision_bound (mem_erase.mp hx).1)
      _ ≤ Fintype.card C * d := by
        simp only [sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm A.card]
        exact Nat.mul_le_mul_left _ hA
  have havg : (∑ c : C, 6 * (U.filter fun t => c ∈ bad t).card) ≤ ∑ _ : C, U.card := by
    calc
      _ = ∑ t ∈ U, 6 * (bad t).card := by
        simp_rw [card_filter, mul_sum]
        rw [sum_comm]
        simp [← mul_sum, mul_comm]
      _ ≤ ∑ _ ∈ U, Fintype.card C := sum_le_sum hb
      _ = _ := by simp [mul_comm]
  have : Nonempty C := ⟨fun _ => ⟨0, by omega⟩⟩
  obtain ⟨c, _, hc⟩ := exists_le_of_sum_le univ_nonempty havg
  refine ⟨c, U.filter (fun t => c ∉ bad t), filter_subset _ _, ?_, ?_⟩
  · have he := card_filter_add_card_filter_not (s := U) (fun t => c ∈ bad t)
    omega
  · intro t ht x hx he
    by_contra hne
    exact (mem_filter.mp ht).2 (mem_biUnion.mpr
      ⟨x, mem_erase.mpr ⟨hne, hx⟩, mem_filter.mpr ⟨mem_univ _, he⟩⟩)

theorem color {i j k d e f : ℕ} (S U : Finset (Cell i j k))
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hr : ∀ t ∈ U, (rows S t).card ≤ d) (hc : ∀ t ∈ U, (cols S t).card ≤ e)
    (hi : ∀ t ∈ U, (inner S t).card ≤ f) :
    ∃ (a : Fin i → Fin (6 * d)) (b : Fin j → Fin (6 * e)) (c : Fin k → Fin (6 * f))
      (V : Finset (Cell i j k)), V ⊆ U ∧ U.card ≤ 2 * V.card ∧
      (∀ t ∈ V, ∀ x ∈ rows S t, a x = a t.1 → x = t.1) ∧
      (∀ t ∈ V, ∀ y ∈ cols S t, b y = b t.2.1 → y = t.2.1) ∧
      (∀ t ∈ V, ∀ z ∈ inner S t, c z = c t.2.2 → z = t.2.2) := by
  obtain ⟨a, X, hX, hx, ha⟩ := one_label U (·.1) (rows S) hd hr
  obtain ⟨b, Y, hY, hy, hb⟩ := one_label X (·.2.1) (cols S) he fun t ht => hc t (hX ht)
  obtain ⟨c, V, hV, hv, hc⟩ := one_label Y (·.2.2) (inner S) hf fun t ht => hi t (hX (hY ht))
  exact ⟨a, b, c, V, hV.trans (hY.trans hX), by omega,
    fun t ht => ha t (hY (hV ht)), fun t ht => hb t (hV ht), hc⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

section
/-! # A finite rank comparison for bounded completion sets -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse

/-- The constant pays for three independent colorings and the
loss of at most half of the selected triples. Tensor powers remove it. -/
def DegreeBound (F : Type*) [Field F] : Prop :=
  ∀ i j k I J K r : ℕ, 0 < I → 0 < J → 0 < K →
    ∀ (w : Fin i → Fin j → Fin k → F) (U : Finset (Cell i j k)), U ⊆ support w →
      (∀ t ∈ U, (rows (support w) t).card ≤ I) →
      (∀ t ∈ U, (cols (support w) t).card ≤ J) →
      (∀ t ∈ U, (inner (support w) t).card ≤ K) →
      WeightedRankLE w r →
        U.card * Real.exp (exponent F (Real.log I) (Real.log J) (Real.log K)) ≤
          432 * (I : ℝ) * J * K * r

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

section
/-! # Completion counts for powers of a partial product -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open Finset

variable {F : Type*} [Field F] {i j k n : ℕ}

def pack (p : Fin n → Cell i j k) : Cell (i ^ n) (j ^ n) (k ^ n) :=
  (finFunctionFinEquiv (fun l => (p l).1), finFunctionFinEquiv (fun l => (p l).2.1),
    finFunctionFinEquiv (fun l => (p l).2.2))

theorem pack_injective : Function.Injective (@pack i j k n) := by
  let unpack (t : Cell (i ^ n) (j ^ n) (k ^ n)) (l : Fin n) :=
    (finFunctionFinEquiv.symm t.1 l, finFunctionFinEquiv.symm t.2.1 l,
      finFunctionFinEquiv.symm t.2.2 l)
  apply Function.LeftInverse.injective (g := unpack)
  intro p
  funext l
  simp [unpack, pack]

variable (w : Fin i → Fin j → Fin k → F) (p : Fin n → Cell i j k)

theorem card_support : (support w).card = supportSize w := by
  classical
  rw [support, card_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, ite_not]
  rw [sum_comm]
  rfl

theorem mem_pack : pack p ∈ support (WPower w n) ↔ ∀ l, p l ∈ support w := by
  simp only [support, mem_filter, mem_univ, true_and]
  simp [WPower, pack, prod_ne_zero_iff]

/-- Completed labels are independent digit strings. -/
private theorem count_digits {d : ℕ} (A : Finset (Fin (d ^ n))) (B : Fin n → Finset (Fin d))
    (h : ∀ x, x ∈ A ↔ ∀ l, finFunctionFinEquiv.symm x l ∈ B l) :
    A.card = ∏ l, (B l).card := by
  have he : A = (Fintype.piFinset B).map finFunctionFinEquiv.toEmbedding := by
    ext x
    rw [h, mem_map_equiv, Fintype.mem_piFinset]
  rw [he, card_map, Fintype.card_piFinset]

theorem rows_power :
    (rows (support (WPower w n)) (pack p)).card = ∏ l, (rows (support w) (p l)).card := by
  apply count_digits
  intro x
  simp only [rows, mem_filter, mem_univ, true_and]
  simp only [support, mem_filter, mem_univ, true_and]
  simp [WPower, pack, prod_ne_zero_iff]

theorem cols_power :
    (cols (support (WPower w n)) (pack p)).card = ∏ l, (cols (support w) (p l)).card := by
  apply count_digits
  intro x
  simp only [cols, mem_filter, mem_univ, true_and]
  simp only [support, mem_filter, mem_univ, true_and]
  simp [WPower, pack, prod_ne_zero_iff]

theorem inner_power :
    (inner (support (WPower w n)) (pack p)).card = ∏ l, (inner (support w) (p l)).card := by
  apply count_digits
  intro x
  simp only [inner, mem_filter, mem_univ, true_and]
  simp only [support, mem_filter, mem_univ, true_and]
  simp [WPower, pack, prod_ne_zero_iff]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

section
/-! # Completion counts on a fixed type of support words -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open OAI.LinearAlgebra.TensorSpectrum

/-- A type of independent supported triples gives as many distinct
triples in the power, all with the same three completion counts. -/
theorem fiber {F : Type*} [Field F] {i j k m : ℕ}
    (w : Fin i → Fin j → Fin k → F) (e : Fin m ≃ support w) (n : ℕ) (t : TagWords.CountVector m n) :
    ∃ U : Finset (Cell (i ^ n) (j ^ n) (k ^ n)), U ⊆ support (WPower w n) ∧
      U.card = (TagWords.fiber t).card ∧ ∀ p ∈ U,
        (rows (support (WPower w n)) p).card = TagWords.countWeight (fun a => (rows (support w) (e a).val).card) t ∧
        (cols (support (WPower w n)) p).card = TagWords.countWeight (fun a => (cols (support w) (e a).val).card) t ∧
        (inner (support (WPower w n)) p).card = TagWords.countWeight (fun a => (inner (support w) (e a).val).card) t := by
  let f : TagWords.Word m n ↪ Cell (i ^ n) (j ^ n) (k ^ n) :=
    ⟨fun x => pack fun l => (e (x l)).val, fun _ _ he =>
      funext fun l => e.injective (Subtype.ext (congrFun (pack_injective he) l))⟩
  refine ⟨(TagWords.fiber t).map f, ?_, Finset.card_map _, ?_⟩
  · intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hp
    exact (mem_pack w _).2 fun l => (e (x l)).property
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hp
    rw [show f x = pack (fun l => (e (x l)).val) from rfl, rows_power, cols_power, inner_power]
    have he (a : Fin m → ℕ) : ∏ l, a (x l) = TagWords.countWeight a t :=
      TagWords.wordWeight_eq_of_mem_fiber a hx
    exact ⟨he (fun a => (rows (support w) (e a).val).card),
      he (fun a => (cols (support w) (e a).val).card),
      he (fun a => (inner (support w) (e a).val).card)⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

section
/-!
# Nonnegative dual total correlation

Apply entropy subadditivity to the first index and the pair of
remaining indices, then to the two remaining indices within
each fixed first-index slice.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open Finset

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

private def left (S : Finset (X × Y)) (y : Y) := univ.filter fun x => (x, y) ∈ S

private def right (S : Finset (X × Y)) (x : X) := univ.filter fun y => (x, y) ∈ S

private theorem sum_right (S : Finset (X × Y)) (f : X × Y → ℝ) :
    ∑ x, ∑ y ∈ right S x, f (x, y) = ∑ p ∈ S, f p := by
  simp only [right, sum_filter]
  rw [← Fintype.sum_prod_type (fun p => if p ∈ S then f p else 0)]
  simp

private theorem count_right (S : Finset (X × Y)) : ∑ x, ((right S x).card : ℝ) = S.card := by
  simpa using sum_right S (fun _ => 1)

private theorem count_left (S : Finset (X × Y)) : ∑ y, ((left S y).card : ℝ) = S.card := by
  rw [← count_right S]
  simp only [left, right, card_filter, Nat.cast_sum]
  rw [sum_comm]

/-- For the uniform distribution on a relation, the sum of the
two conditional entropies is bounded by the joint entropy. -/
private theorem pair_bound (S : Finset (X × Y)) :
    ∑ p ∈ S, (Real.log (right S p.1).card + Real.log (left S p.2).card) ≤
      S.card * Real.log S.card := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  let a x := ((right S x).card : ℝ)
  let b y := ((left S y).card : ℝ)
  let m : ℝ := S.card
  have hm : 0 < m := Nat.cast_pos.mpr hS.card_pos
  have hsum : ∑ p ∈ S, a p.1 * b p.2 ≤ m * m := by
    calc
      _ ≤ ∑ p : X × Y, a p.1 * b p.2 := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by
        intro p _ _
        unfold a b
        positivity)
      _ = m * m := by
        rw [Fintype.sum_prod_type]
        simp only [← mul_sum, ← sum_mul, a, b, count_left, count_right, m]
  calc
    _ ≤ ∑ p ∈ S, (a p.1 * b p.2 / m - 1 + Real.log m) := by
      apply sum_le_sum
      rintro ⟨x, y⟩ hxy
      have ha : 0 < a x := Nat.cast_pos.mpr (card_pos.mpr ⟨y, mem_filter.mpr ⟨mem_univ _, hxy⟩⟩)
      have hb : 0 < b y := Nat.cast_pos.mpr (card_pos.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, hxy⟩⟩)
      have hh := Real.log_le_sub_one_of_pos (div_pos (mul_pos ha hb) hm)
      rw [Real.log_div (mul_pos ha hb).ne' hm.ne', Real.log_mul ha.ne' hb.ne'] at hh
      exact sub_le_iff_le_add.mp hh
    _ ≤ _ := by
      simp only [sum_add_distrib, sum_sub_distrib, ← sum_div, sum_const, nsmul_eq_mul, mul_one]
      change _ / m - m + m * Real.log m ≤ m * Real.log m
      linarith only [(div_le_iff₀ hm).mpr hsum]

theorem premium_nonneg {i j k : ℕ} (S : Finset (Cell i j k)) (hS : S.Nonempty) :
    0 ≤ premium S := by
  have hm : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS.card_pos
  have h₁ := pair_bound S
  have h₂ : ∑ p ∈ S, (Real.log (cols S p).card + Real.log (inner S p).card) ≤
      ∑ p ∈ S, Real.log (right S p.1).card := by
    rw [← sum_right S, ← sum_right S]
    apply sum_le_sum
    intro x _
    have he (t : Fin j × Fin k) : cols S (x, t) = left (right S x) t.2 := by
      ext y; simp [cols, left, right]
    have hf (t : Fin j × Fin k) : inner S (x, t) = right (right S x) t.1 := by
      ext z; simp [inner, right]
    simp only [he, hf, sum_const, nsmul_eq_mul]
    simpa only [add_comm] using pair_bound (right S x)
  unfold premium
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  apply sub_nonneg.mpr
  unfold conditional
  rw [div_le_iff₀ hm, mul_comm]
  have he (t : Cell i j k) : rows S t = left S t.2 := rfl
  simp only [he, sum_add_distrib] at *
  linarith only [h₁, h₂]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

/-! # Multiplicative weights from completion counts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
open OAI.LinearAlgebra.TensorSpectrum.TagWords

def unitWeight (s : ℝ) (x y z : ℕ) := Real.exp (s * (Real.log x + Real.log y + Real.log z))

variable {m n : ℕ}

private theorem log_count (a : Fin m → ℕ) (ha : ∀ i, 0 < a i) (t : CountVector m n) :
    Real.log (countWeight a t : ℕ) = ∑ i, (t i).val * Real.log (a i) := by
  simp only [countWeight, Nat.cast_prod, Nat.cast_pow]
  rw [Real.log_prod (fun i _ => pow_ne_zero _ (by exact_mod_cast (ha i).ne'))]
  simp only [Real.log_pow]

theorem unit_count (s : ℝ) (a b c : Fin m → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i) (t : CountVector m n) :
    countWeight (fun i => unitWeight s (a i) (b i) (c i)) t =
      unitWeight s (countWeight a t) (countWeight b t) (countWeight c t) := by
  unfold unitWeight
  rw [log_count a ha t, log_count b hb t, log_count c hc t,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem sum_exp_lower (hm : 0 < m) (a : Fin m → ℝ) :
    m * Real.exp ((∑ i, a i) / m) ≤ ∑ i, Real.exp (a i) := by
  have hm' : 0 < (m : ℝ) := by positivity
  have hp : 0 < ∑ i, Real.exp (a i) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  let b := (m : ℝ)⁻¹ * ∑ i, Real.exp (a i)
  have he := TensorSpectrum.weighted_log_le_log_of_sum_le (fun _ => (m : ℝ)⁻¹)
    (fun i => Real.exp (a i)) b (fun _ => by positivity) (by simp [hm.ne'])
    (fun _ => Real.exp_pos _) (by unfold b; positivity) (by unfold b; rw [Finset.mul_sum])
  simp only [Real.log_exp, b, inv_mul_eq_div, ← Finset.sum_div] at he
  rw [mul_comm, ← le_div_iff₀ hm']
  exact (Real.le_log_iff_exp_le (by positivity)).mp he

variable {i j k : ℕ} (S : Finset (Cell i j k)) (e : Fin S.card ≃ S)

def rCount (a : Fin S.card) := (rows S (e a).val).card
def cCount (a : Fin S.card) := (cols S (e a).val).card
def kCount (a : Fin S.card) := (inner S (e a).val).card

theorem rCount_pos (a) : 0 < rCount S e a := Finset.card_pos.mpr
  ⟨(e a).val.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e a).property⟩⟩

theorem cCount_pos (a) : 0 < cCount S e a := Finset.card_pos.mpr
  ⟨(e a).val.2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e a).property⟩⟩

theorem kCount_pos (a) : 0 < kCount S e a := Finset.card_pos.mpr
  ⟨(e a).val.2.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e a).property⟩⟩

def weight (s : ℝ) (a : Fin S.card) := unitWeight s (rCount S e a) (cCount S e a) (kCount S e a)

theorem exp_conditional (h : S.Nonempty) (s : ℝ) :
    S.card * Real.exp (s * conditional S) ≤ ∑ a, weight S e s a := by
  let f (t : Cell i j k) := Real.log (rows S t).card + Real.log (cols S t).card +
    Real.log (inner S t).card
  have he : ∑ a, s * f (e a).val = s * ∑ t ∈ S, f t := by
    rw [← Finset.mul_sum, e.sum_comp (fun t => f t.val), Finset.sum_coe_sort]
  have hp := sum_exp_lower h.card_pos (fun a => s * f (e a).val)
  rw [he, mul_div_assoc] at hp
  exact hp

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse
end

/-! # Powers of a weighting supported on a set of output cells -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k : ℕ}
  {w : Fin i → Fin j → Fin k → F} {u : Finset (Pos i j)}

private theorem size_cells (hw : ∀ x y z, w x y z ≠ 0 ↔ (x, y) ∈ u) :
    supportSize w = u.card * k := by
  classical
  have he x y z : (if w x y z = 0 then 0 else 1) = (if (x, y) ∈ u then 1 else 0 : ℕ) := by
    by_cases h : (x, y) ∈ u
    · simp [h, (hw x y z).mpr h]
    · simp [h, not_ne_iff.mp (mt (hw x y z).mp h)]
  unfold supportSize
  simp_rw [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type (fun p : Pos i j => k * if p ∈ u then 1 else 0)]
  simp [mul_ite]

theorem power_cells (hw : ∀ x y z, w x y z ≠ 0 ↔ (x, y) ∈ u) (hk : 0 < k) (n : ℕ) :
    ∃ v : Finset (Pos (i ^ n) (j ^ n)), v.card = u.card ^ n ∧
      ∀ x y z, WPower w n x y z ≠ 0 ↔ (x, y) ∈ v := by
  classical
  let v : Finset (Pos (i ^ n) (j ^ n)) := Finset.univ.filter fun p =>
    ∀ l : Fin n, (finFunctionFinEquiv.symm p.1 l, finFunctionFinEquiv.symm p.2 l) ∈ u
  have hv x y z : WPower w n x y z ≠ 0 ↔ (x, y) ∈ v := by
    simp [WPower, v, Finset.prod_ne_zero_iff, hw]
  refine ⟨v, ?_, hv⟩
  have he := supportSize_power w n
  rw [size_cells hv, size_cells hw, mul_pow] at he
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hk n) he

theorem short_pow (i j q n : ℕ) : short (i ^ n) (j ^ n) (q ^ n) = n * short i j q := by
  unfold short
  simp only [Nat.cast_pow, Real.log_pow, mul_div_assoc, mul_min_of_nonneg _ _ (Nat.cast_nonneg n)]

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end
