import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement

section
/-! # Dyadic intervals indexed by binary prefixes -/

namespace OAI.LinearAlgebra.MatrixExponent.Packing

abbrev Cell (j : ℕ) := Fin j → ZMod 2

def ancestor {i j : ℕ} (h : i ≤ j) (x : Cell j) : Cell i :=
  fun a => x (Fin.castLE h a)

@[simp] theorem ancestor_self {i : ℕ} (h : i ≤ i) (x : Cell i) : ancestor h x = x := rfl

@[simp] theorem ancestor_ancestor {i j k : ℕ} (h : i ≤ j) (h' : j ≤ k) (x : Cell k) :
    ancestor h (ancestor h' x) = ancestor (h.trans h') x := rfl

theorem card_cell (j : ℕ) : Fintype.card (Cell j) = 2 ^ j := by simp [Cell]

theorem card_prefix {i h : ℕ} (hi : i ≤ h) (c : Cell i) :
    Fintype.card {x : Cell h // ancestor hi x = c} = 2 ^ (h - i) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [Nat.add_sub_cancel_left, ← card_cell]
  let suffix (x : {x : Cell (i + j) // ancestor hi x = c}) : Cell j :=
    fun a => x.1 (Fin.natAdd i a)
  apply Fintype.card_congr (Equiv.ofBijective suffix ?_)
  constructor
  · intro x y e
    apply Subtype.ext
    funext a
    induction a using Fin.addCases with
    | left a => exact (congrFun x.2 a).trans (congrFun y.2 a).symm
    | right a => exact congrFun e a
  · intro z
    exact ⟨⟨Fin.append c z, funext (Fin.append_left' c z)⟩, funext (Fin.append_right c z)⟩

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Second moments of loads at a dyadic depth

Bounds on prefix collisions control both the variance and the contribution
from pairs of distinct blocks. These estimates serve the balanced
partitions and the reservations in the degree reset.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

variable {h : ℕ} (l : Cell h → ℝ) (π : Equiv.Perm (Cell h)) (i : ℕ)

def load (z : Cell i) : ℝ :=
  if hi : i ≤ h then ∑ x, if ancestor hi (π x) = z then l x else 0 else 0

def mean := (∑ x, l x) / (2 : ℝ) ^ i

def variance := ∑ z : Cell i, (load l π i z - mean l i) ^ 2

def cross (z : Cell i) := (load l π i z) ^ 2 - load (fun x => l x ^ 2) π i z

theorem load_nonneg (hl : ∀ x, 0 ≤ l x) (z : Cell i) : 0 ≤ load l π i z := by
  unfold load
  split_ifs
  · exact Finset.sum_nonneg fun x _ => by split_ifs <;> first | exact hl _ | exact le_rfl
  · exact le_rfl

theorem sum_load (hi : i ≤ h) : (∑ z, load l π i z) = ∑ x, l x := by
  simp only [load, dite_eq_left hi]
  rw [Finset.sum_comm]
  simp

theorem sum_cross (hi : i ≤ h) :
    (∑ z, cross l π i z) = (∑ z, (load l π i z) ^ 2) - ∑ x, l x ^ 2 := by
  simp only [cross, Finset.sum_sub_distrib, sum_load _ _ _ hi]

theorem variance_eq (hi : i ≤ h) :
    variance l π i = (∑ z, (load l π i z) ^ 2) - (∑ x, l x) ^ 2 / (2 : ℝ) ^ i := by
  simp only [variance, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, sum_load _ _ _ hi, Finset.sum_const, Finset.card_univ, card_cell,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mean]
  field_simp
  ring

theorem diagonal_le (z : Cell i) {c : ℝ} (hl : ∀ x, 0 ≤ l x ∧ l x ≤ c) :
    load (fun x => l x ^ 2) π i z ≤ c * load l π i z := by
  unfold load
  split_ifs with hi
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    split_ifs
    · exact (pow_two _).trans_le (mul_le_mul_of_nonneg_right (hl x).2 (hl x).1)
    · simp
  · simp

theorem cross_nonneg (hl : ∀ x, 0 ≤ l x) (z : Cell i) : 0 ≤ cross l π i z := by
  unfold cross load
  split_ifs with hi
  · let f (x : Cell h) := if ancestor hi (π x) = z then l x else 0
    have hf x : 0 ≤ f x := by unfold f; split_ifs <;> first | exact hl _ | exact le_rfl
    apply sub_nonneg.mpr
    rw [pow_two, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have hm := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun y _ => hf y) (Finset.mem_univ x)) (hf x)
    by_cases hx : ancestor hi (π x) = z
    · simpa [hx, f, pow_two] using hm
    · simp [hx]
  · simp

theorem square_load (hi : i ≤ h) :
    (∑ z, (load l π i z) ^ 2) =
      ∑ x, ∑ y, if ancestor hi (π x) = ancestor hi (π y) then l x * l y else 0 := by
  simp only [load, dite_eq_left hi, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp [eq_comm, mul_ite]

/-- A uniform family of prefix hash functions. -/
def Mixes {M : Type} [Fintype M] (p : M → Equiv.Perm (Cell h)) : Prop :=
  ∀ (j : ℕ) (hj : j ≤ h) (x y : Cell h), x ≠ y →
    (∑ m : M, if ancestor hj (p m x) = ancestor hj (p m y) then (1 : ℝ) else 0) ≤
      (Fintype.card M : ℝ) / (2 : ℝ) ^ j

variable {M : Type} [Fintype M] {p : M → Equiv.Perm (Cell h)}

private theorem moment_bound (hp : Mixes p) (hl : ∀ x, 0 ≤ l x) (hi : i ≤ h) :
    (∑ m, ∑ z, (load l (p m) i z) ^ 2) ≤
      (Fintype.card M : ℝ) * ((∑ x, l x ^ 2) + (∑ x, l x) ^ 2 / (2 : ℝ) ^ i) := by
  let C : ℝ := Fintype.card M
  calc
    _ ≤ ∑ x, ∑ y, ((if x = y then C * l x ^ 2 else 0) + C / 2 ^ i * (l x * l y)) := by
      simp_rw [square_load l _ i hi]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro y _
      by_cases he : x = y
      · subst y
        simp only [ite_true, ← pow_two, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        apply le_add_of_nonneg_right
        unfold C
        positivity
      · have hb := mul_le_mul_of_nonneg_right (hp i hi x y he) (mul_nonneg (hl x) (hl y))
        rw [Finset.sum_mul] at hb
        simpa [he, ite_mul, C] using hb
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        ← Finset.mul_sum, ← Finset.sum_mul]
      unfold C
      ring

theorem variance_bound (hp : Mixes p) (hl : ∀ x, 0 ≤ l x) (hi : i ≤ h) :
    (∑ m, variance l (p m) i) ≤ (Fintype.card M : ℝ) * ∑ x, l x ^ 2 := by
  simp only [variance_eq _ _ _ hi, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  linarith [moment_bound l i hp hl hi]

theorem cross_bound (hp : Mixes p) (hl : ∀ x, 0 ≤ l x) (hi : i ≤ h) :
    (∑ m, ∑ z, cross l (p m) i z) ≤ (Fintype.card M : ℝ) * ((∑ x, l x) ^ 2 / (2 : ℝ) ^ i) := by
  simp only [sum_cross _ _ _ hi, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  linarith [moment_bound l i hp hl hi]

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-! # Summing loads through successive assignments -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open Finset
open scoped Classical

variable {X Y Z : Type} [Fintype X]

def push (f : X → Y) (l : X → ℝ) (y : Y) := ∑ x, if f x = y then l x else 0

theorem push_nonneg (f : X → Y) (l : X → ℝ) (hl : ∀ x, 0 ≤ l x) (y : Y) :
    0 ≤ push f l y := by
  exact sum_nonneg fun x _ => by split_ifs <;> first | exact hl x | exact le_rfl

theorem push_le_push (f : X → Y) {l m : X → ℝ} (hl : ∀ x, l x ≤ m x) (y : Y) :
    push f l y ≤ push f m y := by
  exact sum_le_sum fun x _ => by split_ifs <;> first | exact hl x | exact le_rfl

theorem sum_push [Fintype Y] (f : X → Y) (l : X → ℝ) :
    (∑ y, push f l y) = ∑ x, l x := by
  unfold push
  rw [sum_comm]
  simp

theorem test_push [Fintype Y] (f : X → Y) (l : X → ℝ) (p : Y → Prop) [DecidablePred p] :
    (∑ y, if p y then push f l y else 0) = ∑ x, if p (f x) then l x else 0 := by
  rw [← sum_filter]
  unfold push
  rw [sum_comm]
  simp

theorem push_comp [Fintype Y] (f : X → Y) (g : Y → Z) (l : X → ℝ) (z : Z) :
    push g (push f l) z = push (g ∘ f) l z :=
  test_push f l (fun y => g y = z)

theorem push_div (f : X → Y) (l : X → ℝ) (r : ℝ) (y : Y) :
    push f (fun x => l x / r) y = push f l y / r := by
  simp only [push, div_eq_mul_inv, sum_mul, ite_mul, zero_mul]

theorem push_fst [Fintype Y] (l : X × Y → ℝ) (x : X) :
    push Prod.fst l x = ∑ y, l (x, y) := by
  unfold push
  rw [Fintype.sum_prod_type, sum_comm]
  simp

theorem push_at [Fintype Y] {W : X → Type} (f : (x : X) → Y → W x)
    (l : X × Y → ℝ) (x : X) (w : W x) :
    push (fun p => (⟨p.1, f p.1 p.2⟩ : Σ x, W x)) l ⟨x, w⟩ =
      push (f x) (fun y => l (x, y)) w := by
  unfold push
  rw [Fintype.sum_prod_type, sum_eq_single x]
  · simp
  · intro y _ hy; simp [hy]
  · simp

theorem push_prefix {h : ℕ} (base : X → ℕ) (hb : ∀ v, base v ≤ h)
    (π : Equiv.Perm (Cell h)) (l : X → Cell h → ℝ) (v : X) (z : Cell (base v)) :
    push (fun p => (⟨p.1, ancestor (hb p.1) (π p.2)⟩ : Σ x, Cell (base x)))
      (Function.uncurry l) ⟨v, z⟩ = load (l v) π (base v) z := by
  rw [push_at (fun v y => ancestor (hb v) (π y))]
  simp only [load, dite_eq_left (hb v), push, Function.uncurry_apply_pair]
  congr! 2

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-! # Counting both ends of a wire, including both incidences of a loop -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V E : Type} [Fintype E]

def degree (pair : E → V × V) (v : V) :=
  Fintype.card {e // (pair e).1 = v} + Fintype.card {e // (pair e).2 = v}

def arityCost (v : V) (p : V × V) : ℕ :=
  (if p.1 = v then 1 else 0) + (if p.2 = v then 1 else 0)

theorem degree_sum (pair : E → V × V) (v : V) :
    degree pair v = ∑ e, arityCost v (pair e) := by
  simp only [degree, Fintype.card_subtype, arityCost, sum_add_distrib, ← sum_filter,
    ← card_eq_sum_ones]

theorem degree_map [Fintype V] {X : Type} (pair : E → V × V) (f : V → X) (z : X) :
    degree (fun e => Prod.map f f (pair e)) z =
      ∑ v, if f v = z then degree pair v else 0 := by
  have aux (t : E → V) : Fintype.card {e // f (t e) = z} =
      ∑ v ∈ univ.filter (fun v => f v = z), Fintype.card {e // t e = v} := by
    simp only [Fintype.card_subtype]
    rw [sum_card_fiberwise_eq_card_filter univ _ t]
    simp
  rw [← sum_filter]
  simp only [degree, sum_add_distrib, ← aux]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-! # Degree and load of a graph under a change of sites -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V W X U : Type} [Fintype U]

/-- Unused sites may coincide with active ones after projection. -/
theorem push_max [Fintype V] (f : V → W) (p : V → Prop) (l : V → ℝ) (B : ℝ)
    (hb : 0 ≤ B) (hs : ∀ v, l v ≤ B) (hz : ∀ v, ¬p v → l v = 0)
    (hi : Set.InjOn f {v | p v}) (w : W) : push f l w ≤ B := by
  unfold push
  by_cases h : ∃ v, p v ∧ f v = w
  · obtain ⟨v, hv, he⟩ := h
    rw [sum_eq_single v]
    · simpa only [he, ite_true] using hs v
    · intro z _ hne
      split_ifs with h
      · exact hz z fun hp => hne (hi hp hv (h.trans he.symm))
      · rfl
    · simp
  · refine le_trans ?_ hb
    refine (sum_eq_zero (fun v _ => ?_)).le
    split_ifs with hv
    · exact hz v fun hp => h ⟨v, hp, hv⟩
    · rfl

theorem degree_le_map [Fintype V] (P : U → V × V) (f : V → W) (p : V → Prop) (u B : ℝ)
    (hb : 0 ≤ B) (hs : ∀ v, degree P v * u ≤ B) (hz : ∀ v, ¬p v → degree P v = 0)
    (hi : Set.InjOn f {v | p v}) (w : W) :
    degree (fun i => Prod.map f f (P i)) w * u ≤ B := by
  have := push_max f p (fun v => degree P v * u) B hb hs
    (fun v hv => by simp [hz v hv]) hi w
  simpa only [degree_map, Nat.cast_sum, sum_mul, Nat.cast_ite, Nat.cast_zero,
    ite_mul, zero_mul, push] using this

theorem degree_partition [Fintype X] (f : U → V × V) (g : X → V × V) (v : V) :
    degree (Sum.elim f g) v = degree f v + degree g v := by
  simp only [degree_sum, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem degree_select [Fintype X] (f : U → V × V) (e : X ↪ U) (v : V) :
    degree (f ∘ e) v ≤ degree f v := by
  simp only [degree_sum, Function.comp_apply]
  rw [← sum_map univ e (fun x => arityCost v (f x))]
  exact sum_le_sum_of_subset (subset_univ _)

theorem degree_push (f : U → Bool → V) (u : ℝ) (v : V) :
    (degree (fun i => (f i false, f i true)) v : ℝ) * u =
      push (Function.uncurry f) (fun _ => u) v := by
  unfold push
  rw [degree_sum, Nat.cast_sum, sum_mul, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  simp [arityCost, ite_mul, add_mul, add_comm]
  congr! 2

end OAI.LinearAlgebra.MatrixExponent.Packing
end

section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

variable {V E F : Type} {a b : Wire} (G : Diagram F a b) {h : ℕ}

/-- Placement of individual stations and partition of all core edges into
uniform bundles. Both ends of an edge are in the same block. -/
structure Bundles (src dst : E → V) (ix : E → Cell h) (u : ℕ) where
  place : G.V → V × Cell h
  bits : G.E ≃ E × Fin u
  left : ∀ e, place (G.source e) = (src (bits e).1, ix (bits e).1)
  right : ∀ e, place (G.target e) = (dst (bits e).1, ix (bits e).1)

end OAI.LinearAlgebra.MatrixExponent.Packing
end
