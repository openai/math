import OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior.Model
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup.Dense

/-! # Private formulas and shared measurements -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior

variable {F : Type*} [Field F] {X Y Z E : Type} [Fintype E]

theorem private_of_span (M : Z → X → Y → F) (a : Z → Product F X Y) (b : E → Product F X Y)
    (h : ∀ z, M z - (a z).apply ∈ Submodule.span F (Set.range (fun l => (b l).apply))) :
    Private M (Fintype.card E) := by
  have hi (z) := (Submodule.mem_span_range_iff_exists_fun _).mp (h z)
  choose c hc using hi
  let e := (Fintype.equivFin E).symm
  refine ⟨a, b ∘ e, fun z l => c z (e l), fun z x y => ?_⟩
  have he := congrFun (congrFun (hc z) x) y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at he
  simp only [Function.comp_apply, e.sum_comp (fun t => c z t * (b t).apply x y)]
  rw [he, add_sub_cancel]

/-- A batch of independent products, indexed by the group and two
outer indices. The right input has column before inner index. -/
abbrev Port (G A H : Type) := G × A × H
abbrev Out (G A : Type) := G × A × A

open Classical in
def batch (F : Type*) [Field F] (G A H : Type) (z : Out G A) (x y : Port G A H) : F :=
  if x.1 = z.1 ∧ y.1 = z.1 ∧ x.2.1 = z.2.1 ∧ y.2.1 = z.2.2 ∧ x.2.2 = y.2.2 then 1 else 0

/-- Common measurements in this seed vanish whenever the two inputs
belong to the same group and the same summation index. -/
structure Seed (F : Type*) [Field F] (G A H E C : Type) [Fintype C] where
  main : Out G A → Product F (Port G A H) (Port G A H)
  extra : E → Product F (Port G A H) (Port G A H)
  code : Out G A → C → E
  eqn : ∀ z x y, batch F G A H z x y =
    (main z).apply x y - ∑ t, (extra (code z t)).apply x y
  aligned : ∀ t x y, x.1 = y.1 → x.2.2 = y.2.2 → (extra t).apply x y = 0

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

/-!
# A joint outer-product and dot-product identity

Use two affine lines of each nonzero slope in a finite auxiliary field.
Each pair of a left and a right line intersects exactly once, except
parallel lines of the same slope. Subtracting the product at every grid
point from the unrestricted product leaves the dot product of equal
slopes. All encoder entries are zero or one over the target field.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
open scoped Classical

abbrev Letter (K : Type) [Field K] := K ⊕ Kˣ

variable {K : Type} [Field K]

private def left : Letter K → K × K → Prop
  | .inl i, p => p.1 = i
  | .inr h, p => p.1 = h * p.2

private def right : Letter K → K × K → Prop
  | .inl j, p => p.2 = j
  | .inr h, p => p.1 = h * p.2 + 1

private theorem parallel (a : Kˣ) (p : K × K) : ¬ (left (.inr a) p ∧ right (.inr a) p) := by
  simp [left, right]
  grind

private theorem meet (x y : Letter K) (h : ¬ ∃ a, x = .inr a ∧ y = .inr a) :
    ∃! p, left x p ∧ right y p := by
  rcases x with i | a <;> rcases y with j | b
  · exact ⟨(i, j), ⟨rfl, rfl⟩, fun p hp => Prod.ext hp.1 hp.2⟩
  · refine ⟨(i, (i - 1) / b), ⟨rfl, ?_⟩, ?_⟩
    · change i = (b : K) * ((i - 1) / b) + 1
      rw [mul_div_cancel₀ _ b.ne_zero, sub_add_cancel]
    · rintro ⟨u, v⟩ ⟨hu, hv⟩
      change u = i at hu
      change u = (b : K) * v + 1 at hv
      subst u
      refine Prod.ext rfl ((eq_div_iff b.ne_zero).mpr ?_)
      rw [hv]
      ring
  · refine ⟨(a * j, j), ⟨rfl, rfl⟩, ?_⟩
    intro p hp
    exact Prod.ext (hp.1.trans (congrArg ((a : K) * ·) hp.2)) hp.2
  · have hab : (a : K) ≠ b := by
      intro he
      exact h ⟨a, rfl, by rw [Units.ext he]⟩
    let z := ((a : K) - b)⁻¹
    have he : ((a : K) - b) * z = 1 := mul_inv_cancel₀ (sub_ne_zero.mpr hab)
    refine ⟨(a * z, z), ⟨rfl, ?_⟩, ?_⟩
    · change (a : K) * z = b * z + 1
      rw [← he]; ring
    · rintro ⟨u, v⟩ ⟨hu, hv⟩
      change u = (a : K) * v at hu
      change u = (b : K) * v + 1 at hv
      have hh : ((a : K) - b) * v = 1 := by rw [sub_mul, ← hu, hv]; ring
      have hz : v = z := mul_left_cancel₀ (sub_ne_zero.mpr hab) (hh.trans he.symm)
      exact Prod.ext (hu.trans (congrArg ((a : K) * ·) hz)) hz

variable (F : Type*) [Field F]

def encoderL (p : K × K) (x : Letter K) : F := if left x p then 1 else 0
def encoderR (p : K × K) (x : Letter K) : F := if right x p then 1 else 0

theorem ordinary_entry (p : K × K) (i j : K) :
    encoderL F p (.inl i) * encoderR F p (.inl j) = if p = (i, j) then 1 else 0 := by
  by_cases h : p.1 = i <;> by_cases h' : p.2 = j <;>
    simp [encoderL, encoderR, left, right, Prod.ext_iff, h, h']

theorem equal_entry (p : K × K) (a : Kˣ) :
    encoderL F p (.inr a) * encoderR F p (.inr a) = 0 := by
  have h := parallel a p
  grind [encoderL, encoderR]

theorem dot_entry [Fintype K] (x y : Letter K) :
    1 - ∑ p, encoderL F p x * encoderR F p y =
      if ∃ a, x = .inr a ∧ y = .inr a then 1 else 0 := by
  split_ifs with h
  · obtain ⟨a, rfl, rfl⟩ := h
    simp [equal_entry]
  obtain ⟨p, hp, hu⟩ := meet x y h
  rw [Fintype.sum_eq_single p]
  · simp [encoderL, encoderR, hp.1, hp.2]
  · intro t ht
    have he : ¬ (left x t ∧ right y t) := fun he => ht (hu t he)
    grind [encoderL, encoderR]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

/-!
# One distinguished position per block

Use a line slope in one position, and ordinary indices in the
others. Reading the dot-product identity at the distinguished
position gives independent products, all with the same correction
dictionary indexed by words of ordinary grid points.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
open scoped Classical

variable (F : Type*) [Field F] {K : Type} [Field K] {n : ℕ}

private abbrev InFromBlock (K : Type) [Field K] (n : ℕ) := Port (Fin (n + 1)) (Fin n → K) Kˣ
private abbrev OutputFromBlock (K : Type) (n : ℕ) := Out (Fin (n + 1)) (Fin n → K)

private def encode (x : InFromBlock K n) : Fin (n + 1) → Letter K :=
  x.1.insertNth (.inr x.2.2) (fun l => .inl (x.2.1 l))

private theorem encode_slope (x : InFromBlock K n) (i : Fin (n + 1)) (a : Kˣ) :
    encode x i = .inr a ↔ x.1 = i ∧ x.2.2 = a := by
  by_cases h : x.1 = i
  · subst i; simp [encode]
  obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm h)
  simp [encode, h]

private def point (z : OutputFromBlock K n) (l : Fin n) : K × K := (z.2.1 l, z.2.2 l)

private def primary (z : OutputFromBlock K n) : Product F (InFromBlock K n) (InFromBlock K n) :=
  ⟨fun x => ∏ l, encoderL F (point z l) (encode x (z.1.succAbove l)),
   fun y => ∏ l, encoderR F (point z l) (encode y (z.1.succAbove l))⟩

private def ordinaryBlock (q : Fin (n + 1) → K × K) : Product F (InFromBlock K n) (InFromBlock K n) :=
  ⟨fun x => ∏ l, encoderL F (q l) (encode x l), fun y => ∏ l, encoderR F (q l) (encode y l)⟩

private theorem expand (z : OutputFromBlock K n) (x y : InFromBlock K n) (a : K × K) :
    (ordinaryBlock F (z.1.insertNth a (point z))).apply x y =
      encoderL F a (encode x z.1) * encoderR F a (encode y z.1) * (primary F z).apply x y := by
  unfold Product.apply ordinaryBlock primary
  simp only [← Finset.prod_mul_distrib]
  rw [Fin.prod_univ_succAbove _ z.1]
  simp

private theorem primary_eq (g : Fin (n + 1)) (x y u v : Fin n → K) (a : Kˣ) :
    (primary F (g, u, v)).apply (g, x, a) (g, y, a) = if x = u ∧ y = v then 1 else 0 := by
  simp only [Product.apply, primary, point, encode, Fin.insertNth_apply_succAbove, ← Finset.prod_mul_distrib,
    ordinary_entry, Fintype.prod_ite_zero, Finset.prod_const_one, Prod.mk.injEq, forall_and, ← funext_iff]
  congr 1
  exact propext (and_congr eq_comm eq_comm)

/-- The auxiliary field indexes zero-one coefficients over `F`. -/
def blockSeed (K : Type) [Field K] [Fintype K] (n : ℕ) :
    Seed F (Fin (n + 1)) (Fin n → K) Kˣ (Fin (n + 1) → K × K) (K × K) where
  main := primary F
  extra := ordinaryBlock F
  code z a := z.1.insertNth a (point z)
  eqn z x y := by
    simp only [expand, ← Finset.sum_mul, ← one_sub_mul, dot_entry]
    simp_rw [encode_slope]
    by_cases he : x.1 = z.1 ∧ y.1 = z.1 ∧ x.2.2 = y.2.2
    · rcases z with ⟨g, u, v⟩
      rcases x with ⟨g', x, a⟩
      rcases y with ⟨g'', y, b⟩
      change g' = g ∧ g'' = g ∧ a = b at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      simp [batch, primary_eq]
    · unfold batch
      grind
  aligned q x y hg ha := by
    simp only [ordinaryBlock, Product.apply, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_zero (Finset.mem_univ x.1)
    rw [(encode_slope x _ _).2 ⟨rfl, rfl⟩, (encode_slope y _ _).2 ⟨hg.symm, ha.symm⟩]
    exact equal_entry F _ _

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

section
/-! # Choosing the grid to retain a quadratic saving -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior

/-- The width overhead grows linearly in the mesh parameter while
the block length grows quadratically. A mesh parameter proportional
to the inverse gap leaves room on both output sides. -/
theorem parameters {x y z a : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1)
    (hz : 0 ≤ z) (hz' : z < x * y) (ha : 1 ≤ a) :
    ∃ (q : ℕ) (l θ φ : ℝ), 1 ≤ l ∧ (q : ℝ) = l * l ∧ 0 < θ ∧ θ < φ ∧
      φ * (x * q + a * l) ≤ x ∧ φ * (y * q + a * l) ≤ y ∧ z ≤ θ * (x * y * q) ∧
      (1 / (16 * (4 * a + 1) ^ 2)) * (x * y - z) ^ 2 ≤ θ / 4 := by
  let g := x * y - z
  have hg : 0 < g := sub_pos.mpr hz'
  have hg' : g ≤ 1 := by unfold g; nlinarith
  let t := g / (x * y)
  have ht : 0 < t := by unfold t; positivity
  have ht' : t ≤ 1 := (div_le_one (by positivity)).mpr (sub_le_self _ hz)
  have ht₀ : t * (x * y) = g := div_mul_cancel₀ _ (by positivity)
  let m := ⌈4 * a / g⌉₊
  let l : ℝ := m
  have hl : 1 ≤ l := Nat.one_le_cast.mpr (Nat.ceil_pos.mpr (by positivity))
  have hlo : 4 * a ≤ l * g := (div_le_iff₀ hg).mp (Nat.le_ceil _)
  have hhi : l * g ≤ 4 * a + 1 := by
    calc
      _ ≤ (4 * a / g + 1) * g := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (by positivity)).le hg.le
      _ = 4 * a + g := by rw [add_mul, div_mul_cancel₀ _ hg.ne', one_mul]
      _ ≤ _ := by linarith
  let q := m * m
  have hq : (q : ℝ) = l * l := Nat.cast_mul _ _
  have hq' : 0 < (q : ℝ) := by rw [hq]; positivity
  let θ := (1 - 3 * t / 4) / q
  let φ := (1 - t / 2) / q
  have he : θ * q = 1 - 3 * t / 4 := div_mul_cancel₀ _ hq'.ne'
  have hf : φ * q = 1 - t / 2 := div_mul_cancel₀ _ hq'.ne'
  have hθ : 0 < θ := div_pos (by linarith) hq'
  have hφ : θ < φ := div_lt_div_of_pos_right (by linarith) hq'
  have hcost : a * l ≤ q * g / 4 := by
    rw [hq]
    linarith [mul_le_mul_of_nonneg_right hlo (by linarith : 0 ≤ l)]
  have outer (b : ℝ) (hb : x * y ≤ b) : φ * (b * q + a * l) ≤ b := by
    calc
      _ ≤ φ * (b * q + q * g / 4) := by gcongr; linarith
      _ = (φ * q) * (b + g / 4) := by ring
      _ ≤ b := by
        rw [hf]
        linarith [mul_le_mul_of_nonneg_left hb ht.le, mul_nonneg ht.le hg.le]
  refine ⟨q, l, θ, φ, hl, hq, hθ, hφ, outer x (by nlinarith), outer y (by nlinarith), ?_, ?_⟩
  · rw [show θ * (x * y * q) = (θ * q) * (x * y) by ring, he]
    change t * (x * y) = x * y - z at ht₀
    linarith
  · have hsq : (q : ℝ) * g ^ 2 ≤ (4 * a + 1) ^ 2 := by
      rw [hq, show l * l * g ^ 2 = (l * g) ^ 2 by ring]
      gcongr
    change (1 / (16 * (4 * a + 1) ^ 2)) * g ^ 2 ≤ θ / 4
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    calc
      _ ≤ (4 * θ * q) * g ^ 2 := le_mul_of_one_le_left (by positivity) (by linarith)
      _ = (4 * θ) * (q * g ^ 2) := by ring
      _ ≤ (4 * θ) * (4 * a + 1) ^ 2 := by gcongr
      _ = _ := by ring

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

/-! # Tiling output rectangles while retaining private products -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
open Finset

variable {F : Type*} [Field F] {X Y Z X' Y' Z' U V : Type} {M : Z → X → Y → F} {r : ℕ}

theorem Private.pull (h : Private M r) (a : X' → X) (b : Y' → Y) (c : Z' → Z) :
    Private (fun z x y => M (c z) (a x) (b y)) r := by
  obtain ⟨p, q, d, he⟩ := h
  let map (t : Product F X Y) : Product F X' Y' := ⟨t.left ∘ a, t.right ∘ b⟩
  exact ⟨fun z => map (p (c z)), fun l => map (q l), d ∘ c, fun z x y => he _ _ _⟩

theorem Private.collect [Fintype U] [Fintype V] (h : Private M r)
    (a : X' → U → X) (b : Y' → V → Y) (c : Z' → Z) :
    Private (fun z x y => ∑ i, ∑ j, M (c z) (a x i) (b y j)) r := by
  obtain ⟨p, q, d, he⟩ := h
  let map (t : Product F X Y) : Product F X' Y' :=
    ⟨fun x => ∑ i, t.left (a x i), fun y => ∑ j, t.right (b y j)⟩
  have hv (t : Product F X Y) (x y) :
      (map t).apply x y = ∑ i, ∑ j, t.apply (a x i) (b y j) := by
    simp only [map, Product.apply, sum_mul, mul_sum]
    rw [sum_comm]
  refine ⟨fun z => map (p (c z)), fun l => map (q l), d ∘ c, ?_⟩
  intro z x y
  simp only [he, hv, Function.comp_apply, sum_add_distrib, mul_sum]
  congr 1
  simp_rw [sum_comm (s := (univ : Finset V)) (t := (univ : Finset (Fin r)))]
  rw [sum_comm]

variable {i j k i' j' k' : ℕ}

theorem PrivateProducts.cut (h : PrivateProducts F i j k r) (hi : i' ≤ i) (hj : j' ≤ j)
    (hk : k' ≤ k) : PrivateProducts F i' j' k' r := by
  let lift {a b a' b'} (ha : a' ≤ a) (hb : b' ≤ b) (x : Pos a' b') : Pos a b :=
    (Fin.castLE ha x.1, Fin.castLE hb x.2)
  have he := Private.pull h (lift hi hk) (lift hk hj) (lift hi hj)
  simpa only [PrivateProducts, lift, Fin.castLE_inj] using he

theorem PrivateProducts.rank (h : PrivateProducts F i j k r) : RankLE F i j k (i * j + r) := by
  obtain ⟨p, q, d, he⟩ := h
  let e : (Pos i j ⊕ Fin r) ≃ Fin (i * j + r) :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv
  let s l := (e.symm l).elim p q
  refine ⟨fun l => (s l).left, fun l => (s l).right,
    fun l z => (e.symm l).elim (fun t => if t = z then 1 else 0) (d z), ?_⟩
  intro x y z
  rw [← e.sum_comp, Fintype.sum_sum_type]
  simp only [s, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, mul_ite, mul_one, mul_zero,
    Fintype.sum_ite_eq']
  simpa only [Product.apply, mul_comm] using (he z x y).symm

/-- Glue independent square tiles by identifying the inputs they share. -/
theorem tile {G A H : Type} {s a k : ℕ} (g : Pos s s ≃ G) (u : Fin a ≃ A) (v : Fin k ≃ H)
    (h : Private (batch F G A H) r) : PrivateProducts F (s * a) (s * a) k r := by
  classical
  let e : Fin (s * a) ≃ Pos s a := finProdFinEquiv.symm
  let X (x : Pos (s * a) k) (j : Fin s) : Port G A H := (g ((e x.1).1, j), u (e x.1).2, v x.2)
  let Y (y : Pos k (s * a)) (i : Fin s) : Port G A H := (g (i, (e y.2).1), u (e y.2).2, v y.1)
  let Z (z : Pos (s * a) (s * a)) : Out G A :=
    (g ((e z.1).1, (e z.2).1), u (e z.1).2, u (e z.2).2)
  have hh := h.collect X Y Z
  unfold PrivateProducts
  convert hh using 1
  funext z x y
  have hx (j i) : batch F G A H (Z z) (X x j) (Y y i) =
      if j = (e z.2).1 ∧ i = (e z.1).1 then
        if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0 else 0 := by
    have he (x y : Fin (s * a)) : x = y ↔ (e x).1 = (e y).1 ∧ (e x).2 = (e y).2 :=
      e.injective.eq_iff.symm.trans Prod.ext_iff
    simp only [batch, X, Y, Z, Equiv.apply_eq_iff_eq, Prod.mk.injEq, he x.1 z.1, he y.2 z.2,
      ← ite_and]
    congr 1
    exact propext (by tauto)
  simp [hx, ite_and]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

/-!
# Converting short sums to private products

Across a square array of groups, a short sum of separable forms is
itself a thin matrix product. Only the private terms of distinguished
sums remain private. All products for other sums are shared.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
open Finset

variable {F : Type*} [Field F] {X Y Z O : Type} {m n r : ℕ}

def Slots (M : Z → X → Y → F) (r m : ℕ) : Prop :=
  ∃ (a : Z ⊕ Fin r → Fin m → Product F X Y) (c : Z → Fin r → F), ∀ z x y,
    M z x y = (∑ j, (a (.inl z) j).apply x y) + ∑ l, c z l * ∑ j, (a (.inr l) j).apply x y

def matrix (F : Type*) [Field F] (i j k : ℕ) (z : Pos i j) (x : Pos i k) (y : Pos k j) :=
  if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then (1 : F) else 0

def signal (a : Fin m → Product F X Y) (z : Pos n n) (x : Fin n × X) (y : Fin n × Y) : F :=
  if x.1 = z.1 ∧ y.1 = z.2 then ∑ j, (a j).apply x.2 y.2 else 0

private theorem signal_private (a : Fin m → Product F X Y) (h : PrivateProducts F n n m r) :
    Private (signal (n := n) a) r := by
  obtain ⟨p, q, c, he⟩ := h
  let lift (b : Product F (Pos n m) (Pos m n)) : Product F (Fin n × X) (Fin n × Y) :=
    ⟨fun x => ∑ i, (a i).left x.2 * b.left (x.1, i),
     fun y => ∑ j, (a j).right y.2 * b.right (j, y.1)⟩
  have eqn (b) (x y) : (lift b).apply x y =
      ∑ i, ∑ j, (a i).left x.2 * (a j).right y.2 * b.apply (x.1, i) (j, y.1) := by
    simp only [Product.apply, lift, sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  refine ⟨lift ∘ p, lift ∘ q, c, fun z x y => ?_⟩
  have target : signal a z x y = ∑ i, ∑ j, (a i).left x.2 * (a j).right y.2 *
      matrix F n n m z (x.1, i) (j, y.1) := by
    by_cases h₁ : x.1 = z.1 <;> by_cases h₂ : y.1 = z.2 <;>
      simp [signal, matrix, h₁, h₂, mul_ite, Product.apply]
  change ∀ z x y, matrix F n n m z x y = _ at he
  rw [target]
  simp only [Function.comp_apply, eqn, he, mul_add, sum_add_distrib, mul_sum]
  congr 1
  rw [sum_comm (s := (univ : Finset (Fin r)))]
  apply sum_congr rfl
  intro i _
  rw [sum_comm (s := (univ : Finset (Fin r)))]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- Charge all corrections at each slot and all private products of
the common slots. -/
private theorem shared [Fintype Z] [Fintype O]
    (T : Z ⊕ Fin r → O → X → Y → F) (c : Z → Fin r → F) (h : ∀ i, Private (T i) m) :
    Private (fun (p : Z × O) x y => T (.inl p.1) p.2 x y + ∑ j, c p.1 j * T (.inr j) p.2 x y)
      ((Fintype.card Z + r) * m + r * Fintype.card O) := by
  choose a b d he using h
  let E := ((Z ⊕ Fin r) × Fin m) ⊕ (Fin r × O)
  let B : E → Product F X Y := Sum.elim (fun p => b p.1 p.2) (fun p => a (.inr p.1) p.2)
  let W := Submodule.span F (Set.range fun l => (B l).apply)
  have hb i z : T i z - (a i z).apply ∈ W := by
    have h' : T i z - (a i z).apply = ∑ l, d i z l • (b i l).apply := by
      funext x y
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, he, add_sub_cancel_left]
    rw [h']
    exact W.sum_mem fun l _ => W.smul_mem _ (Submodule.subset_span ⟨.inl (i, l), rfl⟩)
  have ha i z : T (.inr i) z ∈ W := by
    have hh : (a (.inr i) z).apply ∈ W := Submodule.subset_span ⟨.inr (i, z), rfl⟩
    simpa using W.add_mem (hb (.inr i) z) hh
  rw [show (Fintype.card Z + r) * m + r * Fintype.card O = Fintype.card E by simp [E]]
  refine private_of_span _ (fun z => a (.inl z.1) z.2) B ?_
  intro z
  have hs : (∑ j, c z.1 j • T (.inr j) z.2) ∈ W := W.sum_mem fun j _ => W.smul_mem _ (ha j z.2)
  convert W.add_mem (hb (.inl z.1) z.2) hs using 1
  funext x y
  simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem Slots.enlarge {i j k p b e : ℕ} (h : Slots (matrix F i j k) e p)
    (hb : PrivateProducts F b b p r) :
    PrivateProducts F (i * b) (j * b) k ((i * j + e) * r + e * (b * b)) := by
  obtain ⟨a, c, he⟩ := h
  have hs := shared (fun t => signal (n := b) (a t)) c (fun t => signal_private (a t) hb)
  let I : Fin (i * b) ≃ Pos i b := finProdFinEquiv.symm
  let J : Fin (j * b) ≃ Pos j b := finProdFinEquiv.symm
  let x (p : Pos (i * b) k) := ((I p.1).2, (I p.1).1, p.2)
  let y (p : Pos k (j * b)) := ((J p.2).2, p.1, (J p.2).1)
  let z (p : Pos (i * b) (j * b)) := (((I p.1).1, (J p.2).1), ((I p.1).2, (J p.2).2))
  have hh := hs.pull x y z
  simp only [Pos, Fintype.card_prod, Fintype.card_fin] at hh
  unfold PrivateProducts
  convert hh using 1
  funext w u v
  have hi (p q : Fin (i * b)) := (I.injective.eq_iff (a := p) (b := q)).symm.trans Prod.ext_iff
  have hj (p q : Fin (j * b)) := (J.injective.eq_iff (a := p) (b := q)).symm.trans Prod.ext_iff
  simp only [signal, x, y, z, hi u.1 w.1, hj v.2 w.2]
  by_cases ht : (I u.1).2 = (I w.1).2 ∧ (J v.2).2 = (J w.2).2
  · simp only [ht.1, ht.2, and_true, ↓reduceIte]
    exact he ((I w.1).1, (J w.2).1) ((I u.1).1, u.2) (v.1, (J v.2).1)
  · simp only [ite_eq_right ht, mul_zero, sum_const_zero, add_zero]
    apply ite_eq_right
    tauto

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

section
/-! # Replicating private rectangles and cutting off the boundary -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
open scoped Classical

variable {F : Type*} [Field F] {i j k r : ℕ}

theorem PrivateProducts.repeat (h : PrivateProducts F i j k r) (a b : ℕ) :
    PrivateProducts F (a * i) (b * j) k (a * b * r) := by
  obtain ⟨p, q, c, he⟩ := h
  let I : Fin (a * i) ≃ Pos a i := finProdFinEquiv.symm
  let J : Fin (b * j) ≃ Pos b j := finProdFinEquiv.symm
  let z (p : Pos (a * i) (b * j)) := ((I p.1).2, (J p.2).2)
  let g (p : Pos (a * i) (b * j)) := ((I p.1).1, (J p.2).1)
  let x (p : Pos (a * i) k) := ((I p.1).2, p.2)
  let y (p : Pos k (b * j)) := (p.1, (J p.2).2)
  let lift (s : Pos a b) (t : Product F (Pos i k) (Pos k j)) : Product F (Pos (a * i) k) (Pos k (b * j)) :=
    ⟨fun u => if (I u.1).1 = s.1 then t.left (x u) else 0,
     fun v => if (J v.2).1 = s.2 then t.right (y v) else 0⟩
  let E := Pos a b × Fin r
  let e := (Equiv.prodCongr (finProdFinEquiv (m := a) (n := b)) (Equiv.refl (Fin r))).trans
    finProdFinEquiv
  refine ⟨fun w => lift (g w) (p (z w)), fun l => lift (e.symm l).1 (q (e.symm l).2),
    fun w l => if (e.symm l).1 = g w then c (z w) (e.symm l).2 else 0, ?_⟩
  intro w u v
  rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Equiv.symm_apply_apply, ite_mul, zero_mul, Fintype.sum_ite_eq']
  have hi (p q : Fin (a * i)) := (I.injective.eq_iff (a := p) (b := q)).symm.trans Prod.ext_iff
  have hj (p q : Fin (b * j)) := (J.injective.eq_iff (a := p) (b := q)).symm.trans Prod.ext_iff
  simp only [hi u.1 w.1, hj v.2 w.2]
  by_cases hu : (I u.1).1 = (I w.1).1
  · by_cases hv : (J v.2).1 = (J w.2).1
    · simpa only [lift, g, x, y, z, Product.apply, hu, hv, true_and, ↓reduceIte] using he (z w) (x u) (y v)
    · simp [lift, g, Product.apply, hv]
  · simp [lift, g, Product.apply, hu]

theorem PrivateProducts.cover (h : PrivateProducts F i j k r) {I J K : ℕ}
    (hi : 0 < i) (hi' : i ≤ I) (hj : 0 < j) (hj' : j ≤ J) (hk : K ≤ k) :
    ∃ R, PrivateProducts F I J K R ∧ R * (i * j) ≤ 4 * (I * J) * r := by
  have round (i I : ℕ) (hi : 0 < i) (hi' : i ≤ I) :
      ∃ m, I ≤ m * i ∧ m * i ≤ 2 * I := by
    refine ⟨I / i + 1, ?_, ?_⟩
    · rw [Nat.add_mul, Nat.one_mul]
      have := Nat.mod_lt I hi
      have := Nat.mod_add_div' I i
      omega
    · rw [Nat.add_mul, Nat.one_mul]
      have := Nat.div_mul_le_self I i
      omega
  obtain ⟨a, ha, ha'⟩ := round i I hi hi'
  obtain ⟨b, hb, hb'⟩ := round j J hj hj'
  refine ⟨a * b * r, (h.repeat a b).cut ha hb hk, ?_⟩
  calc
    _ = (a * i) * (b * j) * r := by ring
    _ ≤ (2 * I) * (2 * J) * r := by gcongr
    _ = _ := by ring

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

/-! # Filling arbitrary output rectangles from a geometric sequence -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
open Filter

variable {F : Type*} [Field F] {x y z b : ℝ}

theorem PrivateProducts.map {K : Type*} [Field K] (f : K →+* F) {i j k r : ℕ}
    (h : PrivateProducts K i j k r) : PrivateProducts F i j k r := by
  obtain ⟨p, q, c, he⟩ := h
  let lift (a : Product K (Pos i k) (Pos k j)) : Product F _ _ := ⟨f ∘ a.left, f ∘ a.right⟩
  refine ⟨lift ∘ p, lift ∘ q, fun t u => f (c t u), fun t u v => ?_⟩
  simpa only [Function.comp_apply, lift, Product.apply, apply_ite f, map_zero, map_one,
    map_add, map_mul, map_sum] using congrArg f (he t u v)

private theorem between {θ φ : ℝ} (hb : 1 < b) (hθ : 0 < θ) (hφ : θ < φ) (n₀ : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∃ n ≥ n₀, (m : ℝ) ^ θ ≤ b ^ n ∧ b ^ n ≤ (m : ℝ) ^ φ := by
  have h₁ := (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
  have h₂ := (tendsto_rpow_atTop (sub_pos.mpr hφ)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, h₁.eventually_ge_atTop (b ^ n₀),
    h₂.eventually_ge_atTop b] with m hm hmn hmg
  have hm' : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near (Real.one_le_rpow hm' hθ.le) hb
  refine ⟨n + 1, ?_, hn'.le, ?_⟩
  · by_contra! hlt
    exact hn'.not_ge ((pow_le_pow_right₀ hb.le hlt.le).trans hmn)
  · rw [pow_succ, show φ = θ + (φ - θ) by ring, Real.rpow_add (by positivity)]
    exact mul_le_mul hn hmg (by positivity) (by positivity)

theorem fill {X Y Z θ φ δ : ℝ} (hb : 1 < b) (hθ : 0 < θ) (hφ : θ < φ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hx : φ * X ≤ x) (hy : φ * Y ≤ y) (hz : z ≤ θ * Z) (hδ : δ ≤ θ / 4)
    (h : ∀ᶠ n : ℕ in atTop, ∃ i j k r : ℕ, 0 < i ∧ 0 < j ∧ (i : ℝ) ≤ (b ^ n) ^ X ∧
      (j : ℝ) ≤ (b ^ n) ^ Y ∧ (b ^ n) ^ Z ≤ k ∧ (r : ℝ) * (b ^ n) ^ (1 / 4 : ℝ) ≤ 3 * i * j ∧ PrivateProducts F i j k r) :
    ∀ᶠ m : ℕ in atTop, ∃ r : ℕ, PrivateProducts F (side m x) (side m y) (side m z) r ∧
      (r : ℝ) ≤ 12 * side m x * side m y * (m : ℝ) ^ (-δ) := by
  obtain ⟨n₀, hn⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop 1, between hb hθ hφ n₀] with m hm hseq
  have hm' : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  obtain ⟨n, h₀, hlo, hhi⟩ := hseq
  obtain ⟨i, j, k, r, hi, hj, hI, hJ, hK, hr, hp⟩ := hn n h₀
  have outer {i : ℕ} {a A : ℝ} (ha : 0 ≤ A) (ha' : φ * A ≤ a) (hs : (i : ℝ) ≤ (b ^ n) ^ A) :
      i ≤ side m a := by
    apply (Nat.cast_le (α := ℝ)).mp
    calc
      (i : ℝ) ≤ ((m : ℝ) ^ φ) ^ A := hs.trans (Real.rpow_le_rpow (by positivity) hhi ha)
      _ ≤ (m : ℝ) ^ a := by rw [← Real.rpow_mul (by positivity)]; gcongr
      _ ≤ _ := Nat.le_ceil _
  have inner {a A : ℝ} (ha : 0 ≤ A) (ha' : a ≤ θ * A) : (m : ℝ) ^ a ≤ (b ^ n) ^ A := by
    apply le_trans (Real.rpow_le_rpow_of_exponent_le hm' ha')
    rw [Real.rpow_mul (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hlo ha
  have hk : side m z ≤ k := Nat.ceil_le.mpr ((inner hZ hz).trans hK)
  obtain ⟨R, hR, he⟩ := hp.cover hi (outer hX hx hI) hj (outer hY hy hJ) hk
  refine ⟨R, hR, ?_⟩
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  apply le_of_mul_le_mul_right _ (show 0 < (i : ℝ) * j by positivity)
  have he' : (R : ℝ) * ((i : ℝ) * j) ≤ 4 * ((side m x : ℝ) * side m y) * r := by exact_mod_cast he
  have ht : (m : ℝ) ^ δ ≤ (b ^ n) ^ (1 / 4 : ℝ) := inner (by norm_num) (by linarith)
  calc
    _ = (R : ℝ) * ((i : ℝ) * j) * (m : ℝ) ^ δ := by ring
    _ ≤ (4 * ((side m x : ℝ) * side m y) * r) * (b ^ n) ^ (1 / 4 : ℝ) := by gcongr
    _ ≤ 4 * ((side m x : ℝ) * side m y) * (3 * i * j) := by rw [mul_assoc]; gcongr
    _ = _ := by ring

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

/-!
# Cost of words with many corrections

Give each correction letter weight `2^(b+1)`. If even the weighted
correction alphabet is no larger than the output alphabet, the
high-correction words are at most a fraction `2⁻ⁿ` of the output
words after `b n` positions.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
open Finset
open scoped Classical

variable {O E : Type} {m n : ℕ}

def changes (p : Fin m → O ⊕ E) : ℕ := #{i | (p i).isRight}

abbrev Errors (O E : Type) (m n : ℕ) := {p : Fin m → O ⊕ E // n ≤ changes p}

variable [Fintype O] [Fintype E]

theorem error_count (b n : ℕ) (h : 2 ^ (b + 1) * Fintype.card E ≤ Fintype.card O) :
    2 ^ n * Fintype.card (Errors O E (b * n) n) ≤ Fintype.card O ^ (b * n) := by
  let q := 2 ^ (b + 1)
  let w (p : O ⊕ E) := if p.isRight then q else 1
  have hw (p : Fin (b * n) → O ⊕ E) : q ^ changes p = ∏ i, w (p i) := by
    simp [w, changes, prod_ite]
  have hs : ∑ p, w p ≤ 2 * Fintype.card O := by
    rw [Fintype.sum_sum_type]
    simp [w]
    change q * Fintype.card E ≤ Fintype.card O at h
    linarith
  have he : Fintype.card (Errors O E (b * n) n) * q ^ n ≤ (2 * Fintype.card O) ^ (b * n) := by
    rw [Fintype.card_subtype]
    calc
      _ = ∑ _ ∈ (univ : Finset (Fin (b * n) → O ⊕ E)).filter (fun p => n ≤ changes p), q ^ n := by simp
      _ ≤ ∑ p ∈ univ.filter (fun p : Fin (b * n) → O ⊕ E => n ≤ changes p), ∏ i, w (p i) := by
        apply sum_le_sum
        intro p hp
        rw [← hw]
        exact pow_le_pow_right₀ (one_le_pow₀ (by decide)) (mem_filter.mp hp).2
      _ ≤ ∑ p : Fin (b * n) → O ⊕ E, ∏ i, w (p i) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = (∑ p, w p) ^ (b * n) := (Fintype.sum_pow _ _).symm
      _ ≤ _ := Nat.pow_le_pow_left hs _
  apply Nat.le_of_mul_le_mul_left (c := 2 ^ (b * n)) _ (by positivity)
  simp only [q, pow_succ, mul_pow, ← pow_mul] at he
  simpa only [mul_comm, mul_left_comm, mul_assoc] using he

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

/-!
# Removing the middle layers of a product expansion

If the corrected coordinates vanish at intermediate error counts,
the discrepancy of the private product lies in the span of the raw
words with many errors. This uses distributivity over the ground field.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
open Finset
open scoped Classical

variable (F : Type*) [Field F] {V : Type*} [CommRing V] [Algebra F V]
    {O E C : Type} [Fintype C] {m n : ℕ}
    (f : Fin m → O ⊕ E → V) (o : Fin m → O) (e : Fin m → C → E)

def raw (p : Fin m → O ⊕ E) := ∏ i, f i (p i)

def errors (i : Fin m) := ∑ j, f i (.inr (e i j))

def layer (s : Finset (Fin m)) :=
  ∏ i, if i ∈ s then errors f e i else f i (.inl (o i)) - errors f e i

private theorem layer_high (s : Finset (Fin m)) (hs : n ≤ s.card) :
    layer f o e s ∈ Submodule.span F (Set.range fun p : Errors O E m n => raw f p.val) := by
  let W := Submodule.span F (Set.range fun p : Errors O E m n => raw f p.val)
  let t (i : Fin m) (c : Option C) : O ⊕ E := c.elim (.inl (o i)) (fun j => .inr (e i j))
  let a (i : Fin m) (c : Option C) : F :=
    if i ∈ s then if c.isSome then 1 else 0 else if c.isSome then -1 else 1
  have he (i) : (if i ∈ s then errors f e i else f i (.inl (o i)) - errors f e i) =
      ∑ c, a i c • f i (t i c) := by
    by_cases h : i ∈ s <;> simp [a, t, h, Fintype.sum_option, errors, sub_eq_add_neg]
  unfold layer
  simp_rw [he]
  rw [Fintype.prod_sum]
  apply Submodule.sum_mem
  intro p _
  have he : (∏ i, a i (p i) • f i (t i (p i))) =
      (∏ i, a i (p i)) • raw f (fun i => t i (p i)) := by
    simp only [Algebra.smul_def, prod_mul_distrib, map_prod, raw]
  rw [he]
  by_cases h : ∏ i, a i (p i) = 0
  · simp [h]
  have hp : n ≤ changes (fun i => t i (p i)) := by
    refine hs.trans (card_le_card ?_)
    intro i hi
    have hv := prod_ne_zero_iff.mp h i (mem_univ _)
    cases hh : p i
    · simp [a, hi, hh] at hv
    · simp [t, hh]
  exact W.smul_mem _ (Submodule.subset_span ⟨⟨_, hp⟩, rfl⟩)

theorem middle_layers (hz : ∀ s : Finset (Fin m), s.Nonempty → s.card < n → layer f o e s = 0) :
    layer f o e ∅ - raw f (fun i => .inl (o i)) ∈
      Submodule.span F (Set.range fun p : Errors O E m n => raw f p.val) := by
  let W := Submodule.span F (Set.range fun p : Errors O E m n => raw f p.val)
  have he : raw f (fun i => .inl (o i)) = ∑ s, layer f o e s := by
    rw [show raw f (fun i => .inl (o i)) =
        ∏ i, (errors f e i + (f i (.inl (o i)) - errors f e i)) by simp [raw]]
    rw [Fintype.prod_add]
    apply sum_congr rfl
    intro s _
    simp [layer, prod_ite, compl_eq_univ_sdiff, sdiff_eq_filter]
  rw [he, ← add_sum_erase _ _ (mem_univ ∅), sub_add_cancel_left]
  apply W.neg_mem
  apply W.sum_mem
  intro s hs
  rcases lt_or_ge s.card n with h | h
  · rw [hz s (nonempty_iff_ne_empty.mpr (mem_erase.mp hs).1) h]
    exact W.zero_mem
  · exact layer_high F f o e s h

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

/-!
# Amplifying a private seed with an agreement code

The code forces either exact agreement at all slots, annihilating
each common term, or disagreement at many slots, annihilating
all intermediate layers of the corrected expansion.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
open Finset
open scoped Classical

variable {G A H E C : Type} {F : Type*} [Field F] [Fintype C] {m n k : ℕ}

private abbrev InFromShell (G A : Type) (m k : ℕ) := Port (Fin m → G) (Fin m → A) (Fin k)
private abbrev OutputFromShell (G A : Type) (m : ℕ) := Out (Fin m → G) (Fin m → A)

private def out (z : OutputFromShell G A m) (i : Fin m) : Out G A := (z.1 i, z.2.1 i, z.2.2 i)

variable (c : (Fin m → G) → Fin k → Fin m → H)

private def read (x : InFromShell G A m k) (i : Fin m) : Port G A H :=
  (x.1 i, x.2.1 i, c x.1 x.2.2 i)


private def Separates := ∀ x a y d, (x, a) ≠ (y, d) →
  n ≤ hammingDist (fun i => (x i, c x a i)) (fun i => (y i, c y d i))

private theorem agreement (h : Separates (n := n) c) {x y : InFromShell G A m k} {s : Finset (Fin m)}
    (hs : s.card < n) (he : ∀ i ∉ s, (read c x i).1 = (read c y i).1 ∧
      (read c x i).2.2 = (read c y i).2.2) : x.1 = y.1 ∧ x.2.2 = y.2.2 := by
  apply Prod.mk.inj
  by_contra hne
  apply hs.not_ge
  refine (h _ _ _ _ hne).trans (card_le_card ?_)
  intro i hi
  by_contra hn
  exact (mem_filter.mp hi).2 (Prod.ext (he i hn).1 (he i hn).2)

variable (S : Seed F G A H E C)

private def one (t : Out G A ⊕ E) := t.elim S.main S.extra

private def signalFromShell (i : Fin m) (t : Out G A ⊕ E) (x y : InFromShell G A m k) :=
  (one S t).apply (read c x i) (read c y i)

private def wordProduct (t : Fin m → Out G A ⊕ E) : Product F (InFromShell G A m k) (InFromShell G A m k) :=
  ⟨fun x => ∏ i, (one S (t i)).left (read c x i), fun y => ∏ i, (one S (t i)).right (read c y i)⟩

private theorem word_apply (t) : (wordProduct c S t).apply = raw (signalFromShell c S) t := by
  funext x y
  simp only [Product.apply, wordProduct, raw, Finset.prod_apply, signalFromShell, prod_mul_distrib]

private def fixups (z : OutputFromShell G A m) := fun i => S.code (out z i)

private theorem layer_eq (s : Finset (Fin m)) (z : OutputFromShell G A m) (x y : InFromShell G A m k) :
    layer (signalFromShell c S) (out z) (fixups S z) s x y =
    ∏ i, if i ∈ s then ∑ t, (S.extra (fixups S z i t)).apply (read c x i) (read c y i)
      else batch F G A H (out z i) (read c x i) (read c y i) := by
  simp only [layer, Finset.prod_apply]
  apply prod_congr rfl
  intro i _
  by_cases he : i ∈ s <;> simp [he, errors, Finset.sum_apply, signalFromShell, one, fixups, S.eqn]

private theorem middle_zero (h : Separates (n := n) c) (z : OutputFromShell G A m) (s : Finset (Fin m))
    (hs : s.Nonempty) (hs' : s.card < n) : layer (signalFromShell c S) (out z) (fixups S z) s = 0 := by
  funext x y
  simp only [Pi.zero_apply, layer_eq]
  by_contra hn
  have hv i := prod_ne_zero_iff.mp hn i (mem_univ _)
  obtain ⟨hg, hk⟩ := agreement c h (x := x) (y := y) hs' (by
    intro i hi
    have ht := hv i
    simp only [ite_eq_right hi, batch, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at ht
    exact ⟨ht.1.trans ht.2.1.symm, ht.2.2.2.2⟩)
  obtain ⟨i, hi⟩ := hs
  have he := hv i
  rw [ite_eq_left hi] at he
  apply he
  apply sum_eq_zero
  intro t _
  apply S.aligned
  · simp [read, hg]
  · simp [read, hg, hk]

private theorem empty_layer (hn : 0 < n) (h : Separates (n := n) c) (z : OutputFromShell G A m) :
    layer (signalFromShell c S) (out z) (fixups S z) ∅ = batch F (Fin m → G) (Fin m → A) (Fin k) z := by
  funext x y
  simp only [layer_eq, notMem_empty, ↓reduceIte, batch, Fintype.prod_ite_zero, prod_const_one]
  congr 1
  apply propext
  constructor
  · intro he
    have hg := agreement c h (x := x) (y := y) (s := ∅) hn (fun i _ =>
      ⟨(he i).1.trans (he i).2.1.symm, (he i).2.2.2.2⟩)
    exact ⟨funext fun i => (he i).1, funext fun i => (he i).2.1, funext fun i => (he i).2.2.1,
      funext fun i => (he i).2.2.2.1, hg.2⟩
  · rintro ⟨hg, hg', ha, ha', hk⟩ i
    simp [read, out, hg, hg', ha, ha', hk]

theorem Seed.amplify [Fintype G] [Fintype A] [Fintype E] [Fintype H] {b k n : ℕ}
    (S : Seed F G A H E C) (hb : 0 < b)
    (hgap : 2 ^ b * Fintype.card G * Fintype.card H * k < Fintype.card H ^ b)
    (herr : 2 ^ (b + 1) * Fintype.card E ≤ Fintype.card (Out G A)) (hn : 0 < n) :
    ∃ r, 2 ^ n * r ≤ Fintype.card (Out G A) ^ (b * n) ∧
      Private (batch F (Fin (b * n) → G) (Fin (b * n) → A) (Fin (k ^ n))) r := by
  obtain ⟨c, hc⟩ := Interior.code hb hgap hn
  refine ⟨_, error_count _ _ herr, ?_⟩
  refine private_of_span _ (fun z => wordProduct c S (fun i => .inl (out z i)))
    (fun t : Errors (Out G A) E (b * n) n => wordProduct c S t.val) ?_
  intro z
  simp_rw [word_apply, ← empty_layer c S hn hc z]
  exact middle_layers F _ _ _ (middle_zero c S hc z)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end
