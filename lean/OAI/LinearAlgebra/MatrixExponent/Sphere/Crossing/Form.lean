import OAI.LinearAlgebra.MatrixExponent.Sphere.Private.Preparation
import Mathlib.Algebra.BigOperators.Intervals
import OAI.LinearAlgebra.MatrixExponent.Sphere.Interpolation
import OAI.LinearAlgebra.MatrixExponent.Sphere.Seam
import OAI.LinearAlgebra.MatrixExponent.Sphere.Block
import OAI.LinearAlgebra.MatrixExponent.Sphere.Width
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.LinearAlgebra.MatrixExponent.Sphere.Coupled
import Mathlib.RingTheory.AdjoinRoot

section
/-! # Splitting a binary form between its two affine charts -/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

open Polynomial Finset

variable {R α : Type*} [CommRing R]

namespace BinaryForm

theorem x (R : Type*) [CommRing R] : BinaryForm 1 (X : R[X]) 1 := by
  refine ⟨natDegree_X_le, ?_⟩
  simp

theorem y (R : Type*) [CommRing R] : BinaryForm 1 (1 : R[X]) X := by
  simp [BinaryForm, reflect_one]

theorem sub {d : ℕ} {p q a b : R[X]} (h : BinaryForm d p q) (g : BinaryForm d a b) :
    BinaryForm d (p - a) (q - b) :=
  ⟨(natDegree_sub_le _ _).trans (max_le h.1 g.1), by rw [reflect_sub, h.2, g.2]⟩

theorem neg {d : ℕ} {p q : R[X]} (h : BinaryForm d p q) : BinaryForm d (-p) (-q) := by
  simpa using (BinaryForm.zero d).sub h

theorem nat (R : Type*) [CommRing R] (m : ℕ) : BinaryForm 0 (m : R[X]) (m : R[X]) := by
  simpa using BinaryForm.const (m : R)

theorem sign (R : Type*) [CommRing R] (m : ℕ) : BinaryForm 0 ((-1 : R[X]) ^ m) ((-1 : R[X]) ^ m) := by
  simpa using BinaryForm.const ((-1 : R) ^ m)

/-- Evaluate at the common diagonal by taking complementary initial jets. -/
theorem split {d : ℕ} {p q : R[X]} (h : BinaryForm d p q) (m : ℕ) :
    p.eval 1 = (∑ i ∈ range m, p.coeff i) + ∑ i ∈ range (d + 1 - m), q.coeff i := by
  have hd := h.1
  rw [eval_eq_sum_range' (by omega : p.natDegree < m + (d + 1 - m))]
  simp only [one_pow, mul_one, sum_range_add]
  congr 1
  rw [← sum_range_reflect q.coeff]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [← h.2, coeff_reflect, revAt_le (by omega)]
  congr 1
  omega

end BinaryForm

theorem wick_form_standard (w : α → ℕ) (k l : α → α → R[X])
    (h : ∀ x y, BinaryForm (w x + w y) (k x y) (l x y)) (xs : List α) :
    BinaryForm (xs.map w).sum (wick k xs) (wick l xs) := by
  have aux (x : α) (ys : List α) (d : ℕ) (P Q : List α → R[X])
      (hp : ∀ zs : List α, zs.length + 1 = ys.length → BinaryForm (d + (zs.map w).sum) (P zs) (Q zs)) :
      BinaryForm (d + w x + (ys.map w).sum) (contract (k x) P ys) (contract (l x) Q ys) := by
    induction ys generalizing d P Q with
    | nil => exact BinaryForm.zero _
    | cons y ys ih =>
      rw [contract_cons, contract_cons, List.map_cons, List.sum_cons]
      apply BinaryForm.sub
      · rw [show d + w x + (w y + (ys.map w).sum) = w x + w y + (d + (ys.map w).sum) by omega]
        exact (h x y).mul (hp ys rfl)
      · rw [show d + w x + (w y + (ys.map w).sum) = d + w y + w x + (ys.map w).sum by omega]
        refine ih _ _ _ fun zs hz => ?_
        simpa only [List.map_cons, List.sum_cons, add_assoc] using hp (y :: zs) (by simp [hz])
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => simpa using BinaryForm.const (1 : R)
    | cons x xs =>
      rw [wick_cons, wick_cons, List.map_cons, List.sum_cons, ← zero_add (w x)]
      refine aux x xs 0 _ _ fun ys hy => ?_
      rw [zero_add]
      exact ih ys.length (by simp only [List.length_cons] at hn; omega) ys rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# A polynomial four-site sphere

Place the four marks at zero, X², Y² and infinity. Remove the poles
at zero by scaling every incident generator by its doubled energy.
At X² = Y² share the pole between the two middle marks asymmetrically,
charging mode m by m+1 on one side and by m on the other. On blocks
of equal length these two corrections to total degree cancel.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Crossing

inductive Corner where
  | a | b | c | d
  deriving DecidableEq

abbrev Label := Corner × Mode 1

def tag (t : Corner) (xs : List (Mode 1)) : List Label := xs.map (t, ·)

def labels (a b c d : List (Mode 1)) : List Label :=
  tag .a a ++ tag .b b ++ tag .c c ++ tag .d d.reverse

variable {R : Type*} [CommRing R]

def wt (x : Mode 1) := 2 * x.2 + 1

def exponent (flip : Bool) (x : Mode 1) := if flip then x.2 else x.2 + 1

def gap (flip : Bool) (X Y : R) := if flip then X ^ 2 - Y ^ 2 else Y ^ 2 - X ^ 2

def near (R : Type*) [CommRing R] (x y : Mode 1) : R := (-1) ^ y.2 * (x.2 + y.2).choose y.2

def upper (flip : Bool) (X Y : R) : Label → Label → R
  | (.a, x), (.b, y) => Y ^ wt x * gap flip X Y ^ exponent flip y * near R x y
  | (.a, x), (.c, y) => X ^ wt x * gap flip X Y ^ exponent (!flip) y * near R x y
  | (.a, x), (.d, y) => if x = y then (X * Y) ^ wt x else 0
  | (.b, x), (.c, y) => X ^ wt x * Y ^ wt y * (if flip then -near R y x else near R x y)
  | (.b, x), (.d, y) => X ^ wt y * gap flip X Y ^ exponent flip x * y.2.choose x.2
  | (.c, x), (.d, y) => Y ^ wt y * gap flip X Y ^ exponent (!flip) x * y.2.choose x.2
  | _, _ => 0

def kernel (flip : Bool) (X Y : R) (x y : Label) := upper flip X Y x y - upper flip X Y y x

def form (flip : Bool) (X Y : R) (a b c d : List (Mode 1)) :=
  wick (kernel flip X Y) (labels a b c d)

theorem skew (flip : Bool) (X Y : R) (x y : Label) : kernel flip X Y y x = -kernel flip X Y x y :=
  (neg_sub _ _).symm

private def swap : Label → Label
  | (.b, x) => (.c, x)
  | (.c, x) => (.b, x)
  | x => x

private theorem swap_pair (X Y : R) (x y : Label) :
    kernel true Y X (swap x) (swap y) = kernel false X Y x y := by
  obtain ⟨s, x⟩ := x
  obtain ⟨t, y⟩ := y
  cases s <;> cases t <;> simp [kernel, upper, swap, gap, mul_comm]

theorem swap_form (X Y : R) (a b c d : List (Mode 1)) :
    form false X Y a b c d = (-1 : R) ^ (b.length * c.length) * form true Y X a c b d := by
  have he : (labels a b c d).map swap = tag .a a ++ tag .c b ++ tag .b c ++ tag .d d.reverse := by
    simp [labels, tag, swap, Function.comp_def]
  have e := wick_swap_blocks (skew true Y X) (tag .a a) (tag .c b) (tag .b c) (tag .d d.reverse)
  rw [← he, wick_map] at e
  simpa only [swap_pair, form, labels, tag, List.length_map] using e

variable {S : Type*} [CommRing S] (f : R →+* S)

private theorem map_upper (flip : Bool) (X Y : R) (x y : Label) :
    f (upper flip X Y x y) = upper flip (f X) (f Y) x y := by
  obtain ⟨s, x⟩ := x
  obtain ⟨t, y⟩ := y
  cases s <;> cases t <;> simp [upper, near, gap, apply_ite f]

theorem map_form (flip : Bool) (X Y : R) (a b c d : List (Mode 1)) :
    f (form flip X Y a b c d) = form flip (f X) (f Y) a b c d := by
  unfold form
  rw [wick_hom]
  simp only [kernel, map_sub, map_upper]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Crossing
end

section
/-! # Degree of the four-site crossing form -/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Crossing

open Polynomial

variable (R : Type*) [CommRing R]

private def degree : Label → ℕ
  | (.b, x) => 2 * (x.2 + 1)
  | (.c, x) => 2 * x.2
  | (_, x) => wt x

private theorem upper_form (u v : Label) :
    BinaryForm (degree u + degree v) (upper false (X : R[X]) 1 u v) (upper false 1 X u v) := by
  obtain ⟨s, x⟩ := u
  obtain ⟨t, y⟩ := v
  have hx := BinaryForm.x R
  have hy := BinaryForm.y R
  have hg := (hy.pow 2).sub (hx.pow 2)
  have hnear : BinaryForm 0 (near R[X] x y) (near R[X] x y) :=
    (BinaryForm.sign R y.2).mul (BinaryForm.nat R _)
  cases s <;> cases t
  case a.b =>
    simpa [degree, upper, gap, exponent] using ((hy.pow (wt x)).mul (hg.pow (y.2 + 1))).mul hnear
  case a.c =>
    simpa [degree, upper, gap, exponent] using ((hx.pow (wt x)).mul (hg.pow y.2)).mul hnear
  case a.d =>
    by_cases h : x = y
    · simpa [degree, upper, h, two_mul] using (hx.mul hy).pow (wt x)
    · simp only [upper, ite_eq_right h]
      exact BinaryForm.zero _
  case b.c =>
    have h : degree (.b, x) + degree (.c, y) = wt x + wt y := by simp [degree, wt]; omega
    rw [h]
    simpa [upper] using ((hx.pow (wt x)).mul (hy.pow (wt y))).mul hnear
  case b.d =>
    simpa [degree, upper, gap, exponent, add_comm] using
      ((hx.pow (wt y)).mul (hg.pow (x.2 + 1))).mul (BinaryForm.nat R (y.2.choose x.2))
  case c.d =>
    simpa [degree, upper, gap, exponent, add_comm] using
      ((hy.pow (wt y)).mul (hg.pow x.2)).mul (BinaryForm.nat R (y.2.choose x.2))
  all_goals exact BinaryForm.zero _

private theorem tag_degree (s : Corner) (xs : List (Mode 1)) :
    ((tag s xs).map degree).sum + (if s = .c then xs.length else 0) =
      energy xs + (if s = .b then xs.length else 0) := by
  induction xs with
  | nil => simp [tag, energy]
  | cons x xs ih =>
    cases s <;> simp [tag, energy, degree, wt, Function.comp_def] at ih ⊢ <;> omega

theorem form_degree (a b c d : List (Mode 1)) (he : b.length = c.length) :
    BinaryForm (energy a + energy b + energy c + energy d)
      (form false (X : R[X]) 1 a b c d) (form false 1 X a b c d) := by
  have h : ((labels a b c d).map degree).sum = energy a + energy b + energy c + energy d := by
    have ha := tag_degree .a a
    have hb := tag_degree .b b
    have hc := tag_degree .c c
    have hd := tag_degree .d d.reverse
    simp only [labels, List.map_append, List.sum_append]
    have : energy d.reverse = energy d := by simp [energy]
    simp [this] at ha hb hc hd
    omega
  rw [← h]
  apply wick_form_standard
  intro x y
  exact (upper_form R x y).sub (add_comm (degree y) (degree x) ▸ upper_form R y x)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Crossing
end

section
/-!
# The diagonal specialization

At the collision the second corner can pair only with the third. Equal
lengths force those two corners to pair fully with each other, leaving
the ordinary Kronecker pairing of the two remaining wedges.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable {R α β : Type*} [CommRing R]

private theorem isolate (k : α → α → R) (f : β → α) (h : ∀ i j, k (f i) (f j) = 0)
    (xs : List β) (ys zs : List α) (hl : xs.length = ys.length)
    (hz : ∀ i z, z ∈ zs → k (f i) z = 0) :
    wick k (xs.map f ++ ys ++ zs) = wick k (xs.map f ++ ys) * wick k zs := by
  have front (x : β) (u : List β) (v : List α) :
      wick k ((x :: u).map f ++ v) =
        (-1 : R) ^ u.length * contract (k (f x)) (fun l => wick k (u.map f ++ l)) v := by
    rw [List.map_cons, List.cons_append, wick_cons]
    exact contract_skip _ _ _ _ _ (fun _ _ _ _ => by rw [h, zero_mul])
  induction xs generalizing ys with
  | nil =>
    have : ys = [] := List.length_eq_zero_iff.mp hl.symm
    simp [this]
  | cons x xs ih =>
    rw [List.append_assoc, front, front, contract_append _ _ _ _ (hz x)]
    have eq : contract (k (f x)) (fun l => wick k (xs.map f ++ (l ++ zs))) ys =
        contract (k (f x)) (fun l => wick k zs * wick k (xs.map f ++ l)) ys := by
      apply contract_congr
      intro l he
      rw [← List.append_assoc, ih l (by simp only [List.length_cons] at hl; omega), mul_comm]
    rw [eq, contract_scale]
    ring

namespace Crossing

variable (R)

private def chart : Label → Mark 1
  | (.b, x) => (.origin, x)
  | (_, x) => (.middle, x)

private theorem middle (b c : List (Mode 1)) :
    wick (kernel false (1 : R) 1) (tag .b b ++ tag .c c) = fusion R b c [] := by
  have h : marks .origin b ++ marks .middle c = (tag .b b ++ tag .c c).map chart := by
    simp [marks, tag, chart, Function.comp_def]
  simp only [fusion, List.reverse_nil, show marks .infinity ([] : List (Mode 1)) = [] from rfl,
    List.append_nil, h, wick_map]
  apply wick_eq_on
  simp only [tag, List.forall_mem_append, List.forall_mem_map]
  constructor <;> intro x _ <;> constructor <;> intro y _
  all_goals simp [kernel, upper, chart, pairing, Subsingleton.elim x.1 y.1]
  all_goals rfl

private theorem outside (a d : Wedge 1) :
    wick (kernel false (1 : R) 1) (tag .a a.val ++ tag .d d.val.reverse) =
      if a.val = d.val then 1 else 0 := by
  apply wick_dual (skew false 1 1) <;> intros <;> simp [kernel, upper]

theorem diagonal (a b c d : Wedge 1) (he : b.val.length = c.val.length) :
    form false (1 : R) 1 a.val b.val c.val d.val =
      (if a.val = d.val then 1 else 0) * fusion R b.val c.val [] := by
  let A := tag .a a.val
  let B := tag .b b.val
  let C := tag .c c.val
  let D := tag .d d.val.reverse
  let k := kernel false (1 : R) 1
  have heven : Even (A.length * (B ++ C).length) := by
    simp only [B, C, List.length_append, tag, List.length_map, he]
    exact ⟨A.length * c.val.length, mul_add _ _ _⟩
  have swap := wick_swap_blocks (skew false (1 : R) 1) [] A (B ++ C) D
  have hi : wick k (B ++ C ++ (A ++ D)) = wick k (B ++ C) * wick k (A ++ D) := by
    apply isolate k (fun i => (.b, i)) (by simp [k, kernel, upper]) b.val C (A ++ D)
    · simpa [C, tag] using he
    · intro i
      simp only [A, D, tag, List.forall_mem_append, List.forall_mem_map]
      simp [k, kernel, upper, gap, exponent, pow_succ]
  calc
    _ = wick k (B ++ C ++ (A ++ D)) := by
      change wick k (A ++ B ++ C ++ D) = _
      simpa only [List.nil_append, heven.neg_one_pow, one_mul, List.append_assoc] using swap
    _ = _ := by rw [hi, middle, outside, mul_comm]

end Crossing
end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

/-- A four-site pairing split at fixed levels. The middle two ordered
wedges have the same length. -/
def CrossingSlice (K : Type*) [Field K] : Prop :=
  ∀ a b c l M N : ℕ, 2 * a + b + c < M + N →
    ∃ (P Q : Wedge 1 → Wedge 1 → LevelLE 1 M → K)
      (S T : Wedge 1 → Wedge 1 → LevelLE 1 N → K),
      ∀ x y z w : Wedge 1, energy x.val = a → energy y.val = b → energy z.val = c →
        energy w.val = a → y.val.length = l → z.val.length = l →
        (if x.val = w.val then 1 else 0) * fusion K y.val z.val [] =
          (∑ i, P x y i * Q w z i) + (∑ i, S x z i * T w y i)

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

/-- Finite-energy bounds on the two alternative factorizations. -/
def FiniteCrossing (K : Type*) [Field K] : Prop :=
  ∀ a b H M N : ℕ, width b 0 ≤ H → 2 * a + b + H < M + N →
    Crossing K (Fintype.card (Level 1 a)) (Fintype.card (Level 1 b))
      ((H + 1) ^ 2 * Fintype.card (LevelLE 1 M)) ((H + 1) ^ 2 * Fintype.card (LevelLE 1 N))

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

/-!
# Crossing independent wires

At the second corner use the fusion preimage of each matrix unit with
vacuum output. Record the energy and length of the preimage on each cut.
The length filter makes unequal-length input pairs vanish.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere
open Finset Classical

variable {K : Type*} [Field K]

private theorem crossing_of_fintype {X Y U V : Type} [Fintype X] [Fintype Y] [Fintype U] [Fintype V]
    (A B : X → Y → U → K) (C D : X → Y → V → K)
    (h : ∀ i i' j j', (if i = i' ∧ j = j' then 1 else 0) =
      (∑ z, A i j z * B i' j' z) + (∑ z, C i j' z * D i' j z)) :
    Crossing K (Fintype.card X) (Fintype.card Y) (Fintype.card U) (Fintype.card V) := by
  let x := (Fintype.equivFin X).symm
  let y := (Fintype.equivFin Y).symm
  let u := (Fintype.equivFin U).symm
  let v := (Fintype.equivFin V).symm
  refine ⟨fun i j k => A (x i) (y j) (u k), fun i j k => B (x i) (y j) (u k),
    fun i j k => C (x i) (y j) (v k), fun i j k => D (x i) (y j) (v k), ?_⟩
  intro i i' j j'
  have e := h (x i) (x i') (y j) (y j')
  rw [← u.sum_comp, ← v.sum_comp] at e
  simpa only [x.injective.eq_iff, y.injective.eq_iff] using e

private abbrev Tag (H : ℕ) := Fin (H + 1) × Fin (H + 1)
private abbrev Cut (H M : ℕ) := Tag H × LevelLE 1 M

private def key (H : ℕ) (t : Wedge 1) : Tag H :=
  (⟨min (energy t.val) H, by omega⟩, ⟨min t.val.length H, by omega⟩)

private theorem key_ok {H : ℕ} (t : Wedge 1) (ht : energy t.val ≤ H) :
    (key H t).1.val = energy t.val ∧ (key H t).2.val = t.val.length := by
  have hn := t.length_sq_le
  have hl : t.val.length ≤ H := by nlinarith
  simp [key, ht, hl]

private abbrev Slice (K : Type*) (H M : ℕ) := Tag H → Wedge 1 → Wedge 1 → LevelLE 1 M → K

private def weighted {H M : ℕ} (P : Slice K H M) (x : Wedge 1)
    (v : Wedge 1 →₀ K) (s : Cut H M) : K :=
  ∑ t ∈ v.support, if key H t = s.1 then v t * P s.1 x t s.2 else 0

private def plain {H M : ℕ} (Q : Slice K H M) (w z : Wedge 1) (s : Cut H M) : K :=
  if z.val.length = s.1.2.val then Q s.1 w z s.2 else 0

private theorem collect {H M : ℕ} (P Q : Slice K H M) (x w z : Wedge 1)
    (v : Wedge 1 →₀ K) :
    ∑ s, weighted P x v s * plain Q w z s =
      ∑ t ∈ v.support, if z.val.length = (key H t).2.val then
        v t * ∑ j, P (key H t) x t j * Q (key H t) w z j else 0 := by
  unfold weighted
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  rw [Fintype.sum_prod_type, sum_comm]
  simp only [ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true, plain]
  split_ifs <;> simp [mul_sum, mul_assoc]

theorem finite_of_slice (K : Type*) [Field K] (h : CrossingSlice K) : FiniteCrossing K := by
  intro a b H M N hH hMN
  let vac : Wedge 1 := ⟨[], by simp⟩
  choose v hv he using fun y : Level 1 b => fusion_width_length K y.val vac
  have bound (y : Level 1 b) (t : Wedge 1) (ht : t ∈ (v y).support) :
      energy t.val ≤ H ∧ t.val.length = y.val.val.length := by
    obtain ⟨hl, hl'⟩ := hv y t ht
    rw [y.property, show energy vac.val = 0 from rfl] at hl
    exact ⟨Nat.cast_le.mp (hl.trans hH), hl'⟩
  choose P Q S T hp using fun i : Tag H =>
    h a i.1.val b i.2.val M N (by have := i.1.isLt; omega)
  have size (L : ℕ) : Fintype.card (Cut H L) = (H + 1) ^ 2 * Fintype.card (LevelLE 1 L) := by
    simp [Cut, Tag, pow_two]
  rw [← size M, ← size N]
  apply crossing_of_fintype
    (fun x y => weighted P x.val (v y)) (fun w z => plain Q w.val z.val)
    (fun x z => plain S x.val z.val) (fun w y => weighted T w.val (v y))
  intro x w y z
  have eqy : y.val = z.val ↔ y = z := Subtype.ext_iff.symm
  have eqx : x.val.val = w.val.val ↔ x = w := Subtype.ext_iff.symm.trans Subtype.ext_iff.symm
  have ey : (∑ t ∈ (v y).support, v y t * fusion K t.val z.val.val []) =
      if y = z then 1 else 0 := by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, eqy] using
      he y z.val vac (z.property.trans y.property.symm) rfl
  simp_rw [mul_comm (plain S _ _ _)]
  rw [collect, collect, ← sum_add_distrib]
  by_cases hl : y.val.val.length = z.val.val.length
  · calc
      _ = (if x = w then 1 else 0) *
          (∑ t ∈ (v y).support, v y t * fusion K t.val z.val.val []) := by
        simp only [ey, ite_and, ite_mul, one_mul, zero_mul]
        split_ifs <;> rfl
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro t ht
        obtain ⟨hb, hy⟩ := bound y t ht
        obtain ⟨h₁, h₂⟩ := key_ok t hb
        have hz := (h₂.trans (hy.trans hl)).symm
        have hi := hp (key H t) x.val t z.val w.val x.property h₁.symm z.property w.property h₂.symm hz
        simp only [eqx] at hi
        rw [ite_eq_left hz, ite_eq_left hz, mul_left_comm, hi, mul_add]
        simp only [mul_comm]
  · have hyz : y ≠ z := by rintro rfl; exact hl rfl
    rw [ite_eq_right (fun h => hyz h.2)]
    symm
    apply sum_eq_zero
    intro t ht
    obtain ⟨hb, hy⟩ := bound y t ht
    have hz : z.val.val.length ≠ (key H t).2.val := by
      rw [(key_ok t hb).2, hy]
      exact Ne.symm hl
    rw [ite_eq_right hz, ite_eq_right hz, zero_add]

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# Shifted crossings from finite energies

Take the input levels just under two quadratic energy budgets. Shrinking
the output budgets slightly leaves room for the polynomial factors in the
finite crossing and for the loss in level selection.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere
open Real Filter

private theorem level_exists {v c : ℝ} (hv : 0 < v) (hc : 0 < c) (hc' : c < entropy) :
    ∀ᶠ x : ℝ in atTop, ∃ e : ℕ, (e : ℝ) ≤ (v * x) ^ 2 ∧ exp (v * (c * x)) ≤ Fintype.card (Level 1 e) := by
  have h := (tendsto_id.const_mul_atTop hv).eventually (entropy_attained (sub_pos.mpr hc'))
  filter_upwards [h, eventually_gt_atTop 0] with x hx hpos
  obtain ⟨e, he, hb⟩ := hx
  rw [sub_sub_cancel, id_eq, mul_left_comm] at hb
  have hcard : 0 < (Fintype.card (Level 1 e) : ℝ) := by
    have hlog := (show 0 < v * (c * x) by positivity).trans_le hb
    by_contra! h
    have : (Fintype.card (Level 1 e) : ℝ) = 0 := le_antisymm h (by positivity)
    simp [this] at hlog
  exact ⟨e, he, (le_log_iff_exp_le hcard).mp hb⟩

private theorem cut_cost {u v A : ℝ} (hu : 0 < u) (hv : 0 < v) (hA : entropy * v < A) :
    ∀ᶠ x : ℝ in atTop, ∀ H M : ℕ, (H : ℝ) ≤ (u * x) ^ 2 + u * x + 1 → (M : ℝ) ≤ (v * x) ^ 2 →
      (((H + 1) ^ 2 * Fintype.card (LevelLE 1 M) : ℕ) : ℝ) ≤ exp (A * x) := by
  let C := (u ^ 2 + u + 2) ^ 2 * (v ^ 2 + 1)
  have hC : 0 ≤ C := by unfold C; positivity
  have h := (isLittleO_pow_exp_pos_mul_atTop 6 (sub_pos.mpr hA)).const_mul_left C
  filter_upwards [eventually_ge_atTop 1, h.bound zero_lt_one] with x hx hl
  intro H M hH hM
  have hxx : x ≤ x ^ 2 := by nlinarith
  have h₁ : (H : ℝ) + 1 ≤ (u ^ 2 + u + 2) * x ^ 2 := by
    nlinarith only [hH, mul_le_mul_of_nonneg_left hxx hu.le, hxx, hx]
  have h₂ : (M : ℝ) + 1 ≤ (v ^ 2 + 1) * x ^ 2 := by nlinarith only [hM, hx, hxx]
  have h₃ : sqrt (M : ℝ) ≤ v * x := sqrt_le_iff.mpr ⟨by positivity, hM⟩
  have h₄ : C * x ^ 6 ≤ exp ((A - entropy * v) * x) := by
    simpa [norm_eq_abs, abs_of_nonneg hC, abs_of_nonneg (by linarith : 0 ≤ x)] using hl
  have := entropy_pos
  push_cast
  calc
    _ ≤ ((H : ℝ) + 1) ^ 2 * (((M : ℝ) + 1) * exp (entropy * sqrt M)) := by
      gcongr; exact card_levelLE_exp M
    _ ≤ ((u ^ 2 + u + 2) * x ^ 2) ^ 2 * (((v ^ 2 + 1) * x ^ 2) * exp (entropy * (v * x))) := by gcongr
    _ = C * x ^ 6 * exp (entropy * (v * x)) := by unfold C; ring
    _ ≤ exp ((A - entropy * v) * x) * exp (entropy * (v * x)) := by gcongr
    _ = _ := by rw [← exp_add]; congr 1; ring

private theorem levelLE_pos (e : ℕ) : 0 < Fintype.card (LevelLE 1 e) :=
  Fintype.card_pos_iff.mpr ⟨⟨⟨[], by simp⟩, by simp [energy]⟩⟩

theorem shifted_of_finite (K : Type*) [Field K] (h : FiniteCrossing K) : ShiftedCrossing K := by
  intro t u α β ht hu hα hβ gap N
  obtain ⟨w, hw, hw'⟩ := exists_between gap
  let s := sqrt (w / (α ^ 2 + β ^ 2))
  have hw₀ : 0 < w := (show 0 < 2 * (t ^ 2 + u ^ 2) by positivity).trans hw
  have hs : 0 < s := by unfold s; positivity
  have hs₂ : s ^ 2 * (α ^ 2 + β ^ 2) = w := by
    rw [show s ^ 2 = w / (α ^ 2 + β ^ 2) from sq_sqrt (by positivity)]
    exact div_mul_cancel₀ _ (by positivity)
  have hs' : s < 1 := by
    have : s ^ 2 < 1 := (mul_lt_mul_iff_left₀ (show 0 < α ^ 2 + β ^ 2 by positivity)).mp
      (by simpa [hs₂] using hw')
    nlinarith
  obtain ⟨c, hc, hc'⟩ := exists_between (mul_lt_of_lt_one_right entropy_pos hs')
  have hc₀ : 0 < c := (mul_pos entropy_pos hs).trans hc
  let Δ := w - 2 * (t ^ 2 + u ^ 2)
  have hΔ : 0 < Δ := sub_pos.mpr hw
  have hcut (v : ℝ) (hv : 0 < v) : entropy * (s * v) < v * c := by
    rw [← mul_assoc, mul_comm v]
    exact mul_lt_mul_of_pos_right hc hv
  obtain ⟨x, hx, hN, hd, ⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩, hM, hL⟩ :=
    ((eventually_ge_atTop 1).and ((eventually_ge_atTop (N / c)).and
      ((eventually_gt_atTop ((u + 3) / Δ)).and ((level_exists ht hc₀ hc').and
        ((level_exists hu hc₀ hc').and ((cut_cost hu (mul_pos hs hα) (hcut α hα)).and
          (cut_cost hu (mul_pos hs hβ) (hcut β hβ)))))))).exists
  let H := ⌈width b 0⌉₊
  let M := ⌊(s * α * x) ^ 2⌋₊
  let L := ⌊(s * β * x) ^ 2⌋₊
  have hH : (H : ℝ) ≤ (u * x) ^ 2 + u * x + 1 := by
    have he : width b 0 = b + sqrt (b : ℝ) := by simp [width]
    have hk : sqrt (b : ℝ) ≤ u * x := sqrt_le_iff.mpr ⟨by positivity, hb⟩
    unfold H
    rw [he]
    linarith only [Nat.ceil_lt_add_one (show 0 ≤ (b : ℝ) + sqrt b by positivity), hk, hb]
  have hin : 2 * a + b + H < M + L := by
    have step := mul_lt_mul_of_pos_right ((div_lt_iff₀ hΔ).mp hd) (by linarith : 0 < x)
    have he : (s * α * x) ^ 2 + (s * β * x) ^ 2 = w * x ^ 2 := by rw [← hs₂]; ring
    have hm : (s * α * x) ^ 2 < (M : ℝ) + 1 := Nat.lt_floor_add_one _
    have hl : (s * β * x) ^ 2 < (L : ℝ) + 1 := Nat.lt_floor_add_one _
    unfold Δ at step
    have : 2 * (a : ℝ) + b + H < M + L := by linarith only [step, hx, he, hm, hl, ha, hb, hH]
    exact_mod_cast this
  have cross := h a b H M L (Nat.le_ceil _) hin
  refine ⟨c * x, _, _, _, _, ?_, Nat.mul_pos (by positivity) (levelLE_pos _),
    Nat.mul_pos (by positivity) (levelLE_pos _), ha', hb', ?_, ?_, cross⟩
  · rw [mul_comm]; exact (div_le_iff₀ hc₀).mp hN
  · rw [← mul_assoc]
    exact hM H M hH (Nat.floor_le (sq_nonneg _))
  · rw [← mul_assoc]
    exact hL H L hH (Nat.floor_le (sq_nonneg _))

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

/-!
# The two local charts of the crossing

At zero, fuse the first two finite sites. Interchanging the middle
blocks gives the expansion at infinity. In either chart the cleared
pole contributes one common polynomial factor at fixed energies.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Crossing

variable (F : Type*) [Field F] {R : Type*} [CommRing R] [Algebra F R]

private def point : Label → Cluster.Leg F 1
  | (.a, x) => .moving 0 (0, x)
  | (.b, x) => .moving 0 (1, x)
  | (.c, x) => .fused (1, x)
  | (.d, x) => .test 0 x

private def charge (f : Bool) : Label → ℕ
  | (.b, x) => exponent f x
  | (.c, x) => exponent (!f) x
  | _ => 0

private theorem coeff_eq (x y : Mode 1) (z : R) :
    coeff x y z = near R x y * z ^ (x.2 + y.2 + 1) := by
  simp only [coeff, near, ite_eq_left (Subsingleton.elim x.1 y.1)]

private theorem translate_one (x y : Mode 1) : translate ((1 : F), x) y = y.2.choose x.2 := by
  simp [translate, Subsingleton.elim x.1 y.1]

private theorem near_swap (x y : Mode 1) :
    (-1 : R) ^ (x.2 + y.2 + 1) * near R x y = -near R y x := by
  simpa only [coeff_eq, one_pow, mul_one, one_mul, mul_comm] using coeff_skew y x (1 : R)

variable (u : R) (N : ℕ) (f : Bool)

private theorem gap_cancel (hu : u ^ N = 0) (x y : Mode 1) :
    gap f u 1 ^ exponent f x * gap f u 1 ^ exponent (!f) y *
      coeff x y (shifted u 1 1 N) = if f then -near R y x else near R x y := by
  have e : exponent f x + exponent (!f) y = x.2 + y.2 + 1 := by
    cases f <;> simp [exponent] <;> omega
  have h : (1 - u ^ 2) * shifted u 1 1 N = 1 := by
    simpa [mul_comm] using shifted_mul u 1 1 N hu
  rw [coeff_eq, ← pow_add, e, mul_comm (near R x y), ← mul_assoc, ← mul_pow]
  cases f with
  | false => simp [gap, h]
  | true =>
    have ht : gap true u 1 * shifted u 1 1 N = -1 := by
      simp only [gap, ↓reduceIte, one_pow, ← neg_sub (1 : R), neg_mul, h]
    simp only [ht, ↓reduceIte, near_swap]

private theorem local_pair (hu : u ^ N = 0) (x y : Label) :
    kernel f u 1 x y = gap f u 1 ^ charge f x * gap f u 1 ^ charge f y *
      Cluster.pair u N (point F x) (point F y) := by
  let P (i j : Corner) := ∀ x y : Mode 1, kernel f u 1 (i, x) (j, y) =
    gap f u 1 ^ charge f (i, x) * gap f u 1 ^ charge f (j, y) *
      Cluster.pair u N (point F (i, x)) (point F (j, y))
  have symm {i j} (h : P i j) : P j i := by
    intro x y
    rw [skew f u 1 (i, y), h, Cluster.pair_skew u N (point F (i, y)), mul_neg]
    ac_rfl
  have hh (i : Corner) : P i i := by
    intro x y
    cases i <;> simp [kernel, upper, Cluster.pair, point, fieldKernel, coeff]
  have ab : P .a .b := by
    intro x y
    simp [kernel, upper, charge, point, Cluster.pair, fieldKernel, coeff_eq, near]
  have ac : P .a .c := by
    intro x y
    have h : shifted u 1 0 N = 1 := by simpa using shifted_mul u 1 0 N hu
    simp [kernel, upper, charge, point, Cluster.pair, Cluster.sep, Cluster.weight, wt, h, coeff_eq]
    ring
  have ad : P .a .d := by
    intro x y
    simp only [kernel, upper, sub_zero, charge, point, Cluster.pair, Cluster.movingDual,
      ↓reduceIte, pow_zero, one_mul, mul_one, translate_zero]
    by_cases h : x = y <;> simp [h, wt, Cluster.weight]
  have bc : P .b .c := by
    intro x y
    simp only [kernel, upper, sub_zero, charge, point, Cluster.pair, Cluster.sep, Cluster.weight,
      wt, sub_zero, inv_one, map_one, one_pow, mul_one]
    rw [← gap_cancel u N f hu]
    ring
  have bd : P .b .d := by
    intro x y
    simp [kernel, upper, charge, point, Cluster.pair, Cluster.movingDual,
      Cluster.weight, wt, translate_one]
    ring
  have cd : P .c .d := by
    intro x y
    simp [kernel, upper, charge, point, Cluster.pair, Cluster.dualCoeff, translate_one]
  obtain ⟨i, x⟩ := x
  obtain ⟨j, y⟩ := y
  suffices P i j from this x y
  cases i <;> cases j <;> first | exact hh _ | assumption | apply symm; assumption

private theorem charge_sum (a b c d : List (Mode 1)) (he : b.length = c.length) :
    ((labels a b c d).map (charge f)).sum = (energy b + energy c) / 2 := by
  have hi (b : List (Mode 1)) :
      2 * (b.map (exponent true)).sum + b.length = energy b ∧
      2 * (b.map (exponent false)).sum = energy b + b.length := by
    induction b with
    | nil => simp [energy]
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, exponent, Bool.false_eq_true, ↓reduceIte,
        List.length_cons, energy] at *
      omega
  have hb := hi b
  have hc := hi c
  cases f <;> simp [labels, tag, charge, Function.comp_def]
  · change (b.map (exponent false)).sum + (c.map (exponent true)).sum = _
    omega
  · change (b.map (exponent true)).sum + (c.map (exponent false)).sum = _
    omega

private theorem prod_pow (q : R) (xs : List Label) :
    (xs.map (fun x => q ^ charge f x)).prod = q ^ (xs.map (charge f)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.prod_cons, ih, pow_add]

private theorem dualCoeff_eq (x : Site F 1) (y : Mode 1) :
    Cluster.dualCoeff x 0 y = algebraMap F R (translate x y) := by
  obtain ⟨c, i⟩ := x
  by_cases h : c = 0
  · subst c
    rw [translate_zero]
    simp [Cluster.dualCoeff, apply_ite (algebraMap F R)]
  · simp [Cluster.dualCoeff, h]

private theorem after_fusion (b c : List (Mode 1)) (d : Wedge 1) :
    wick (Cluster.pair u N)
      (b.map (fun i => .fused ((0 : F), i)) ++ c.map (fun i => .fused (1, i)) ++
        d.val.reverse.map (Cluster.Leg.test 0)) = algebraMap F R (fusion F b c d.val) := by
  let place : Site F 1 ⊕ Mode 1 → Cluster.Leg F 1 := Sum.elim .fused (.test 0)
  have hp (x y : Site F 1 ⊕ Mode 1) :
      Cluster.pair u N (place x) (place y) = algebraMap F R (blockPair x y) := by
    cases x <;> cases y <;> simp [place, Cluster.pair, dualCoeff_eq, blockPair]
  have h := wick_map (Cluster.pair u N) place
    ((offsets F b c).map Sum.inl ++ d.val.reverse.map Sum.inr)
  simp only [hp, ← wick_hom] at h
  rw [← blockCoeff_offsets]
  simpa [blockCoeff, offsets, Function.comp_def, place] using h

/-- In a nilpotent chart the four-site form factors through one mode
space. The shared pole factor depends only on the incident energies. -/
theorem local_chart (hu : u ^ N = 0) (a b c d : Wedge 1) (he : b.val.length = c.val.length) :
    form f u 1 a.val b.val c.val d.val =
      gap f u 1 ^ ((energy b.val + energy c.val) / 2) *
        ∑ z : LevelLE 1 N, u ^ energy z.val.val *
          algebraMap F R (fusion F a.val b.val z.val.val * fusion F z.val.val c.val d.val) := by
  unfold form
  rw [funext fun x => funext (local_pair F u N f hu x), wick_scale_rows,
    prod_pow, charge_sum f _ _ _ _ he, ← wick_map]
  congr 1
  let ys := c.val.map (fun i => Cluster.Leg.fused ((1 : F), i)) ++
    d.val.reverse.map (Cluster.Leg.test (0 : F))
  have ha : (labels a.val b.val c.val d.val).map (point F) =
      (offsets F a.val b.val).map (Cluster.Leg.moving 0) ++ ys := by
    simp [labels, tag, point, offsets, ys, Function.comp_def]
  rw [ha]
  have h := Cluster.block u N (0 : F) hu (offsets F a.val b.val) [] ys (by simp) (by
    simp only [ys, List.forall_mem_append, List.forall_mem_map, Cluster.belongs,
      not_false_eq_true, implies_true, and_self])
  simp only [List.nil_append, blockCoeff_offsets] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_mul, ← mul_assoc, ← after_fusion F u N z.val.val c.val d]
  simp only [ys, List.append_assoc]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Crossing
end

/-! # Factoring the low-degree coefficients in either chart -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Crossing

open Polynomial
variable (F : Type*) [Field F]

def cutWeight (f : Bool) (m t e : ℕ) : F :=
  ∑ i ∈ Finset.range m, (gap f (X : F[X]) 1 ^ t * X ^ e).coeff i

private theorem truncated (f : Bool) (a b c d : Wedge 1) (he : b.val.length = c.val.length)
    (N : ℕ) : X ^ N ∣ form f (X : F[X]) 1 a.val b.val c.val d.val -
      gap f X 1 ^ ((energy b.val + energy c.val) / 2) *
        ∑ z : LevelLE 1 N, X ^ energy z.val.val *
          C (fusion F a.val b.val z.val.val * fusion F z.val.val c.val d.val) := by
  let q := AdjoinRoot.mk (X ^ N : F[X])
  have hu : q X ^ N = 0 := by rw [← map_pow, AdjoinRoot.mk_eq_zero]
  apply AdjoinRoot.mk_eq_mk.mp
  change q _ = q _
  have hg : q (gap f X 1) = gap f (q X) 1 := by cases f <;> simp [gap]
  have hc (z : F) : q (C z) = algebraMap F (AdjoinRoot (X ^ N : F[X])) z := rfl
  simp only [map_form, map_one, map_mul, map_sum, map_pow, hg, hc]
  simpa only [map_mul] using local_chart F (q X) N f hu a b c d he

theorem cut (f : Bool) (a b c d : Wedge 1) (he : b.val.length = c.val.length)
    (m N : ℕ) (hm : m ≤ N) :
    (∑ i ∈ Finset.range m, (form f (X : F[X]) 1 a.val b.val c.val d.val).coeff i) =
      ∑ z : LevelLE 1 N, cutWeight F f m ((energy b.val + energy c.val) / 2) (energy z.val.val) *
        (fusion F a.val b.val z.val.val * fusion F z.val.val c.val d.val) := by
  have h := X_pow_dvd_iff.mp (truncated F f a b c d he N)
  unfold cutWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  specialize h i ((Finset.mem_range.mp hi).trans_le hm)
  rw [coeff_sub, sub_eq_zero, Finset.mul_sum, finsetSum_coeff] at h
  simpa only [← mul_assoc, coeff_mul_C] using h

end OAI.LinearAlgebra.MatrixExponent.Sphere.Crossing
end

/-!
# Shifted crossing by splitting a binary form

At equal coordinates the four-site polynomial is a product of two
pairings. The first coefficients factor across one cut. Read the
remaining coefficients backwards in the other chart for the other
cut. Fusion with vacuum output converts the middle pairing to a wire.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

open Polynomial

namespace Crossing

variable (F : Type*) [Field F]

private theorem eval_one (x y z w : List (Mode 1)) :
    (form false (X : F[X]) 1 x y z w).eval 1 = form false (1 : F) 1 x y z w := by
  simpa using map_form (evalRingHom (1 : F)) false X 1 x y z w

private theorem other (x y z w : Wedge 1) (he : y.val.length = z.val.length)
    (m N : ℕ) (hm : m ≤ N) :
    (∑ i ∈ Finset.range m, (form false 1 (X : F[X]) x.val y.val z.val w.val).coeff i) =
      (-1 : F) ^ (y.val.length * z.val.length) *
        ∑ b : LevelLE 1 N, cutWeight F true m ((energy z.val + energy y.val) / 2) (energy b.val.val) *
          (fusion F x.val z.val b.val.val * fusion F b.val.val y.val w.val) := by
  rw [← cut F true x z y w he.symm m N hm, swap_form, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (-1 : F[X]) ^ (y.val.length * z.val.length) =
    C ((-1 : F) ^ (y.val.length * z.val.length)) by simp, coeff_C_mul]

theorem slice : CrossingSlice F := by
  intro a b c l M N h
  let m := 2 * a + b + c + 1 - M
  refine ⟨fun x y i => cutWeight F false M ((b + c) / 2) (energy i.val.val) * fusion F x.val y.val i.val.val,
    fun w z i => fusion F i.val.val z.val w.val,
    fun x z i => (-1 : F) ^ (l * l) * cutWeight F true m ((c + b) / 2) (energy i.val.val) *
      fusion F x.val z.val i.val.val,
    fun w y i => fusion F i.val.val y.val w.val, ?_⟩
  intro x y z w hx hy hz hw hyl hzl
  have he := hyl.trans hzl.symm
  have eq := (form_degree F x.val y.val z.val w.val he).split M
  rw [eval_one, diagonal F x y z w he, hx, hy, hz, hw,
    show a + b + c + a + 1 - M = m by unfold m; omega,
    cut F false x y z w he M M le_rfl, other F x y z w he m N (by unfold m; omega)] at eq
  simpa only [hy, hz, hyl, hzl, Finset.mul_sum, mul_assoc] using eq

end Crossing

theorem shifted_crossing (K : Type*) [Field K] : ShiftedCrossing K :=
  shifted_of_finite K (finite_of_slice K (Crossing.slice K))

end OAI.LinearAlgebra.MatrixExponent.Sphere
end
