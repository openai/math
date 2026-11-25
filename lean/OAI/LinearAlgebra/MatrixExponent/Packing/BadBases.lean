import OAI.LinearAlgebra.MatrixExponent.Packing.Occupancy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.LinearAlgebra.MatrixExponent.Packing.Reservations
import OAI.LinearAlgebra.MatrixExponent.Packing.Delivery

section
/-!
# Propagating dyadic splits across a host

An edge with delay `d` moves a split up `2*d` levels. To bound all
propagated marks we sum a geometric majorant over neighbours. This
counts paths with multiplicity and needs no choice of shortest paths.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset

variable {V : Type}

inductive Spread (E : V → Finset V) (d : V → V → ℕ) (M : V → (i : ℕ) → Cell i → Prop) :
    V → (i : ℕ) → Cell i → Prop
  | start {v i z} : M v i z → Spread E d M v i z
  | move {v u i} (h : u ∈ E v) (z : Cell (i + 2 * d v u)) :
      Spread E d M u (i + 2 * d v u) z →
      Spread E d M v i (ancestor (Nat.le_add_right i _) z)

variable {E : V → Finset V} {d : V → V → ℕ} {M : V → (i : ℕ) → Cell i → Prop}

theorem Spread.depth {v i z h} (hz : Spread E d M v i z)
    (bound : ∀ v i z, M v i z → i < h) : i < h := by
  induction hz with
  | start hz => exact bound _ _ _ hz
  | move _ _ _ ih => omega

theorem Spread.up {v i z} (hz : Spread E d M v i z)
    (up : ∀ v i z, M v i z → ∀ j (h : j ≤ i), M v j (ancestor h z)) :
    ∀ j (h : j ≤ i), Spread E d M v j (ancestor h z) := by
  induction hz with
  | start hz => exact fun j h => .start (up _ _ _ hz j h)
  | @move v u i hv z _ ih =>
    intro j h
    exact .move hv (ancestor (Nat.add_le_add_right h (2 * d v u)) z)
      (ih _ (Nat.add_le_add_right h _))

noncomputable section
open Classical

def count (M : V → (i : ℕ) → Cell i → Prop) (v : V) (i : ℕ) : ℝ :=
  ∑ z : Cell i, if M v i z then 1 else 0

private theorem from_move {v i z} (hz : Spread E d M v i z) :
    M v i z ∨ ∃ u ∈ E v, ∃ c : Cell (i + 2 * d v u),
      Spread E d M u _ c ∧ ancestor (Nat.le_add_right i _) c = z := by
  cases hz with
  | start hx => exact .inl hx
  | move e c hx => exact .inr ⟨_, e, c, hx, rfl⟩

theorem count_move (v : V) (i : ℕ) :
    count (Spread E d M) v i ≤ count M v i + ∑ u ∈ E v, count (Spread E d M) u (i + 2 * d v u) := by
  let f (u : V) (c : Cell (i + 2 * d v u)) (z : Cell i) : ℝ :=
    if ancestor (Nat.le_add_right i _) c = z then (if Spread E d M u _ c then 1 else 0) else 0
  have hf (u : V) (c : Cell (i + 2 * d v u)) (z : Cell i) : 0 ≤ f u c z := by unfold f; positivity
  have point (z : Cell i) :
      (if Spread E d M v i z then (1 : ℝ) else 0) ≤
        (if M v i z then 1 else 0) + ∑ u ∈ E v, ∑ c, f u c z := by
    have h₀ : 0 ≤ ∑ u ∈ E v, ∑ c, f u c z := sum_nonneg fun u _ => sum_nonneg fun c _ => hf u c z
    by_cases h : Spread E d M v i z
    · rw [ite_eq_left h]
      rcases from_move h with hz | ⟨u, hu, c, hc, he⟩
      · rw [ite_eq_left hz]; linarith
      · calc
          1 = f u c z := by simp [f, he, hc]
          _ ≤ ∑ c, f u c z := single_le_sum (fun a _ => hf u a z) (mem_univ c)
          _ ≤ ∑ u ∈ E v, ∑ c, f u c z :=
            single_le_sum (f := fun u => ∑ c, f u c z) (fun u _ => sum_nonneg fun c _ => hf u c z) hu
          _ ≤ _ := le_add_of_nonneg_left (by positivity)
    · rw [ite_eq_right h]; positivity
  unfold count
  refine (sum_le_sum (fun z (_ : z ∈ univ) => point z)).trans_eq ?_
  rw [sum_add_distrib, sum_comm]
  congr 1
  apply sum_congr rfl
  intro u _
  rw [sum_comm]
  simp [f]

private def envelope (E : V → Finset V) (d : V → V → ℕ) (x : V → ℝ) : ℕ → V → ℝ
  | 0, _ => 0
  | j + 1, v => x v + ∑ u ∈ E v, envelope E d x j u / 2 ^ (d v u)

private theorem positive {x : V → ℝ} (hx : ∀ v, 0 ≤ x v) (j : ℕ) (v : V) :
    0 ≤ envelope E d x j v := by
  induction j generalizing v with
  | zero => exact le_rfl
  | succ j ih => exact add_nonneg (hx v) (sum_nonneg fun u _ => div_nonneg (ih u) (by positivity))

private theorem mass [Fintype V] {x : V → ℝ} (hx : ∀ v, 0 ≤ x v)
    (hs : ∀ u, ∑ v, (if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0) ≤ 1 / 2) (j : ℕ) :
    ∑ v, envelope E d x j v ≤ 2 * ∑ v, x v := by
  induction j with
  | zero => simp only [envelope, sum_const_zero]; exact mul_nonneg (by norm_num) (sum_nonneg fun v _ => hx v)
  | succ j ih =>
    let Y := envelope E d x j
    have h (v : V) : (∑ u ∈ E v, Y u / (2 : ℝ) ^ (d v u)) =
        ∑ u, (if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0) * Y u := by
      simp [ite_mul, div_eq_mul_inv, mul_comm]
    change (∑ v, (x v + ∑ u ∈ E v, Y u / 2 ^ (d v u))) ≤ _
    simp_rw [sum_add_distrib, h]
    rw [sum_comm]
    simp_rw [← sum_mul]
    have hb : (∑ u, (∑ v, if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0) * Y u) ≤
        ∑ u, (1 / 2 : ℝ) * Y u :=
      sum_le_sum (fun u _ => mul_le_mul_of_nonneg_right (hs u) (positive hx j u))
    rw [← mul_sum] at hb
    change (∑ v, Y v) ≤ _ at ih
    linarith

private theorem majorize {P : Type} [Fintype P] {M : P → V → (i : ℕ) → Cell i → Prop}
    {h : ℕ} {x : V → ℝ} (hx : ∀ v, 0 ≤ x v)
    (hd : ∀ v u, u ∈ E v → 0 < d v u) (hm : ∀ p v i z, M p v i z → i < h)
    (he : ∀ v i, ∑ p, count (M p) v i ≤ (Fintype.card P : ℝ) * 2 * (x v) ^ 2 / (2 : ℝ) ^ i)
    (j i : ℕ) (hij : h ≤ i + j) (v : V) :
    ∑ p, count (Spread E d (M p)) v i ≤
      (Fintype.card P : ℝ) * 2 * (envelope E d x j v) ^ 2 / (2 : ℝ) ^ i := by
  induction j generalizing i v with
  | zero =>
    have no (p : P) (z : Cell i) : ¬Spread E d (M p) v i z :=
      fun hz => by have := hz.depth (hm p); omega
    simp [count, no, envelope]
  | succ j ih =>
    let C := (Fintype.card P : ℝ) * 2 / (2 : ℝ) ^ i
    let y := fun u => envelope E d x j u / (2 : ℝ) ^ (d v u)
    let Y := envelope E d x (j + 1) v
    have hy (u : V) : 0 ≤ y u := div_nonneg (positive hx j u) (by positivity)
    have hsum : 0 ≤ ∑ u ∈ E v, y u := sum_nonneg fun u _ => hy u
    have hdirect : (∑ p, count (M p) v i) ≤ C * Y * x v := calc
      _ ≤ (Fintype.card P : ℝ) * 2 * (x v) ^ 2 / (2 : ℝ) ^ i := he _ _
      _ = C * x v * x v := by unfold C; ring
      _ ≤ _ := by
        have : x v ≤ Y := le_add_of_nonneg_right hsum
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by unfold C; positivity)) (hx v)
    have hedge (u : V) (hu : u ∈ E v) :
        (∑ p, count (Spread E d (M p)) u (i + 2 * d v u)) ≤ C * Y * y u := calc
      _ ≤ (Fintype.card P : ℝ) * 2 * (envelope E d x j u) ^ 2 / (2 : ℝ) ^ (i + 2 * d v u) :=
        ih _ (by have := hd v u hu; omega) u
      _ = C * y u * y u := by
        unfold C y
        rw [pow_add, mul_comm 2 (d v u), pow_mul]
        ring
      _ ≤ _ := by
        have hle : y u ≤ Y := (single_le_sum (fun a _ => hy a) hu).trans (le_add_of_nonneg_left (hx v))
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by unfold C; positivity)) (hy u)
    calc
      _ ≤ ∑ p, (count (M p) v i + ∑ u ∈ E v, count (Spread E d (M p)) u (i + 2 * d v u)) :=
        sum_le_sum fun p _ => count_move v i
      _ ≤ C * Y * x v + ∑ u ∈ E v, C * Y * y u := by
        rw [sum_add_distrib, sum_comm]; exact add_le_add hdirect (sum_le_sum hedge)
      _ = _ := by
        rw [← mul_sum, ← mul_add]
        change C * Y * Y = _
        unfold C Y; ring

-- A telescoping bound switches from the number of cells to the
-- collision estimate as the cell count passes the load envelope.
private def reserve (x t : ℝ) := if t ≤ x then 8 * x - t else 4 * x ^ 2 / t

private theorem spend {x t : ℝ} (ht : 0 < t) :
    min t (2 * x ^ 2 / t) + reserve x (2 * t) ≤ reserve x t := by
  by_cases h : t ≤ x
  · have hu := min_le_left t (2 * x ^ 2 / t)
    by_cases h' : 2 * t ≤ x
    · simp only [reserve, ite_eq_left h, ite_eq_left h']; linarith
    · have : 4 * x ^ 2 / (2 * t) ≤ 4 * x := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith
      simp only [reserve, ite_eq_left h, ite_eq_right h']; linarith
  · have hu := min_le_right t (2 * x ^ 2 / t)
    have h' : ¬ 2 * t ≤ x := by linarith
    simp only [reserve, ite_eq_right h, ite_eq_right h']
    calc
      _ ≤ 2 * x ^ 2 / t + 4 * x ^ 2 / (2 * t) := add_le_add_left hu _
      _ = _ := by ring

private theorem dyadic {x : ℝ} (hx : 0 ≤ x) (h : ℕ) :
    ∑ i ∈ range h, min ((2 : ℝ) ^ i) (2 * x ^ 2 / 2 ^ i) ≤ 8 * x := by
  have hi (i : ℕ) :
      min ((2 : ℝ) ^ i) (2 * x ^ 2 / 2 ^ i) ≤ reserve x (2 ^ i) - reserve x (2 ^ (i + 1)) := by
    rw [le_sub_iff_add_le, pow_succ' (2 : ℝ) i]
    exact spend (x := x) (t := (2 : ℝ) ^ i) (by positivity)
  have hlast : 0 ≤ reserve x (2 ^ h) := by
    unfold reserve
    split <;> first | positivity | linarith
  have hfirst : reserve x 1 ≤ 8 * x := by
    unfold reserve
    split <;> nlinarith
  calc
    _ ≤ ∑ i ∈ range h, (reserve x (2 ^ i) - reserve x (2 ^ (i + 1))) :=
      sum_le_sum (fun i _ => hi i)
    _ = reserve x 1 - reserve x (2 ^ h) := by
      simpa using sum_range_sub' (fun i => reserve x (2 ^ i)) h
    _ ≤ _ := by linarith

/-- A column-sum bound on the delay weights gives an absolute constant,
independent of the number of neighbours and the number of levels. -/
theorem spread_bound {P : Type} [Fintype V] [Fintype P]
    (E : V → Finset V) (d : V → V → ℕ)
    (M : P → V → (i : ℕ) → Cell i → Prop) (x : V → ℝ) (h : ℕ)
    (hx : ∀ v, 0 ≤ x v) (hd : ∀ v u, u ∈ E v → 0 < d v u)
    (hs : ∀ u, ∑ v, (if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0) ≤ 1 / 2)
    (hm : ∀ p v i z, M p v i z → i < h)
    (he : ∀ v i, ∑ p, ∑ z : Cell i, (if M p v i z then (1 : ℝ) else 0) ≤
      (Fintype.card P : ℝ) * 2 * (x v) ^ 2 / (2 : ℝ) ^ i) :
    ∑ p, ∑ v, ∑ i ∈ range h, ∑ z : Cell i, (if Spread E d (M p) v i z then (1 : ℝ) else 0)
      ≤ (Fintype.card P : ℝ) * 16*∑ v, x v := by
  let Y := envelope E d x h
  let N : ℝ := Fintype.card P
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have depth (v : V) (i : ℕ) :
      ∑ p, count (Spread E d (M p)) v i ≤ N * min (2 ^ i) (2 * (Y v) ^ 2 / 2 ^ i) := by
    rw [mul_min_of_nonneg _ _ hN]
    apply le_min
    · calc
        _ ≤ ∑ _p : P, ∑ _z : Cell i, (1 : ℝ) :=
          sum_le_sum fun _ _ => sum_le_sum fun _ _ => by split <;> norm_num
        _ = _ := by simp [N, Cell]
    · calc
        _ ≤ N * 2 * (Y v) ^ 2 / (2 : ℝ) ^ i := majorize hx hd hm he h i (by omega) v
        _ = _ := by ring
  have vertex (v : V) : (∑ p, ∑ i ∈ range h, count (Spread E d (M p)) v i) ≤ N * (8 * Y v) := by
    rw [sum_comm]
    calc
      _ ≤ ∑ i ∈ range h, N * min (2 ^ i) (2 * (Y v) ^ 2 / 2 ^ i) := sum_le_sum fun i _ => depth v i
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (dyadic (positive hx h v) h) hN
  rw [sum_comm]
  calc
    _ ≤ ∑ v, N * (8 * Y v) := sum_le_sum fun v _ => vertex v
    _ ≤ N * (8 * (2 * ∑ v, x v)) := by
      rw [← mul_sum, ← mul_sum]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mass hx hs h) (by norm_num)) hN
    _ = _ := by unfold N; ring

end
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Propagation through fixed bases

Weight the count of splits by the depth below each vertex's base. Moving
a mark across an edge of length `16 * d` costs at least `8 * d` levels
relative to the respective bases, and thus a factor of at least `2 ^ d`.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

private theorem shift_le (f : ℕ → ℝ) (n a : ℕ) (hf : ∀ j, 0 ≤ f j)
    (hz : ∀ j, n ≤ j → f j = 0) :
    ∑ j ∈ range n, f (a + j) ≤ ∑ j ∈ range n, f j := by
  calc
    _ ≤ ∑ j ∈ range (a + n), f j := by
      rw [sum_range_add]
      exact le_add_of_nonneg_left (sum_nonneg fun j _ => hf j)
    _ = _ := by
      rw [add_comm a n, sum_range_add, add_eq_left]
      exact sum_eq_zero fun j _ => hz _ (Nat.le_add_right _ _)

private def weight (j : ℕ) : ℝ := 2 ^ ((j + 7) / 8)

private theorem edge_shift (f : ℕ → ℝ) (n a b d : ℕ)
    (hf : ∀ j, 0 ≤ f j) (hz : ∀ j, n ≤ j → f j = 0) (hab : b ≤ a + 8 * d) :
    ∑ j ∈ range n, weight j * f (a + j + 2 * (8 * d)) ≤
      1 / (2 : ℝ) ^ d * (∑ j ∈ range n, weight j * f (b + j)) := by
  let r := a + 16 * d - b
  have hr : 8 * d ≤ r := by unfold r; omega
  have hw (j : ℕ) : weight j ≤ 1 / (2 : ℝ) ^ d * weight (r + j) := by
    rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
    unfold weight
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ 1 / (2 : ℝ) ^ d * (∑ j ∈ range n, weight (r + j) * f (b + (r + j))) := by
      rw [mul_sum]
      apply sum_le_sum
      intro j _
      rw [show a + j + 2 * (8 * d) = b + (r + j) by unfold r; omega, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hw j) (hf _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (shift_le (fun j => weight j * f (b + j)) n r
      (fun j => mul_nonneg (by unfold weight; positivity) (hf _))
      (fun j hj => by rw [hz (b + j) (by omega), mul_zero])) (by positivity)

variable {V : Type} [Fintype V]

private theorem incoming (E : V → Finset V) (d : V → V → ℕ)
    (budget : ∀ u, ∑ v, (if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0) ≤ 1 / 2)
    (y : V → ℝ) (hy : ∀ u, 0 ≤ y u) :
    (∑ v, ∑ u ∈ E v, 1 / (2 : ℝ) ^ (d v u) * y u) ≤ (1 / 2 : ℝ) * ∑ u, y u := by
  have expand (v : V) : (∑ u ∈ E v, 1 / (2 : ℝ) ^ (d v u) * y u) =
      ∑ u, (if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0) * y u := by simp [ite_mul]
  simp_rw [expand]
  rw [sum_comm, mul_sum]
  simp_rw [← sum_mul]
  exact sum_le_sum fun u _ => mul_le_mul_of_nonneg_right (budget u) (hy u)

/-- Choose base depths from the total normalized loads, before mixing.
In a minimal feasible choice each depth is tight either locally or
along an edge. The incoming weight bound pays for all tight edges. -/
theorem choose_bases (E : V → Finset V) (d : V → V → ℕ)
    (budget : ∀ u, ∑ v, (if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0) ≤ 1 / 2)
    (a b : ℕ) (hab : a ≤ b) (t : V → ℝ) (ht : ∀ v, 0 ≤ t v ∧ t v ≤ (2 : ℝ) ^ b) :
    ∃ base : V → ℕ, (∀ v, a ≤ base v ∧ base v ≤ b ∧ t v ≤ (2 : ℝ) ^ (base v)) ∧
      (∀ v u, u ∈ E v → base u ≤ base v + 8 * d v u) ∧
      (∑ v, (2 : ℝ) ^ (base v)) ≤ 2 * Fintype.card V * (2 : ℝ) ^ a + 4 * (∑ v, t v) := by
  let good (c : V → ℕ) := (∀ v, a ≤ c v ∧ c v ≤ b ∧ t v ≤ (2 : ℝ) ^ (c v)) ∧
    ∀ v u, u ∈ E v → c u ≤ c v + 8 * d v u
  have hex : ∃ n, ∃ c, good c ∧ (∑ v, c v) = n := by
    refine ⟨_, fun _ => b, ⟨fun v => ⟨hab, le_rfl, (ht v).2⟩, ?_⟩, rfl⟩
    exact fun _ _ _ => Nat.le_add_right _ _
  obtain ⟨c, ⟨hc, hadj⟩, hmin⟩ := Nat.find_spec hex
  have tight (v : V) : c v = a ∨ (2 : ℝ) ^ (c v - 1) < t v ∨
      ∃ u ∈ E v, c u = c v + 8 * d v u := by
    by_contra! bad
    obtain ⟨hneq, hsmall, hslack⟩ := bad
    have ha := (hc v).1
    let c' (u : V) := if u = v then c v - 1 else c u
    have hle (u : V) : c' u ≤ c u := by
      by_cases he : u = v <;> simp [c', he]
    have hv : c' v = c v - 1 := ite_eq_left rfl
    have ok : good c' := by
      constructor
      · intro u
        by_cases he : u = v
        · subst u; rw [hv]
          exact ⟨by omega, (Nat.sub_le _ _).trans (hc v).2.1, hsmall⟩
        · simpa only [c', ite_eq_right he] using hc u
      · intro w u hu
        refine (hle u).trans ?_
        by_cases he : w = v
        · subst w
          have := hadj v u hu
          have := hslack u hu
          rw [hv]
          omega
        · simpa only [c', ite_eq_right he] using hadj w u hu
    have hlt : (∑ u, c' u) < ∑ u, c u :=
      sum_lt_sum (fun u _ => hle u) ⟨v, mem_univ v, by rw [hv]; omega⟩
    exact Nat.find_min hex (hlt.trans_eq hmin) ⟨c', ok, rfl⟩
  refine ⟨c, hc, hadj, ?_⟩
  have step (v : V) : (2 : ℝ) ^ (c v) ≤
      (2 : ℝ) ^ a + 2 * t v + ∑ u ∈ E v, 1 / (2 : ℝ) ^ (d v u) * (2 : ℝ) ^ (c u) := by
    have ht' := (ht v).1
    have hf (u : V) : 0 ≤ 1 / (2 : ℝ) ^ (d v u) * (2 : ℝ) ^ (c u) := by positivity
    have hsum := sum_nonneg (fun u (_ : u ∈ E v) => hf u)
    rcases tight v with ha | ht'' | ⟨u, hu, had⟩
    · rw [ha]; linarith
    · have hp : (2 : ℝ) ^ (c v) ≤ (2 : ℝ) ^ (c v - 1) * 2 := by
        rw [← pow_succ]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      linarith [show 0 ≤ (2 : ℝ) ^ a by positivity]
    · refine (le_add_of_nonneg_left (by positivity)).trans' ?_
      calc
        _ ≤ 1 / (2 : ℝ) ^ (d v u) * (2 : ℝ) ^ (c u) := by
          rw [one_div_mul_eq_div, le_div_iff₀ (by positivity), ← pow_add]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ ∑ u ∈ E v, 1 / (2 : ℝ) ^ (d v u) * (2 : ℝ) ^ (c u) :=
          single_le_sum (fun u _ => hf u) hu
  have hstep := sum_le_sum (fun v (_ : v ∈ univ) => step v)
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum] at hstep
  have hedge := incoming E d budget (fun v => (2 : ℝ) ^ (c v)) (fun _ => by positivity)
  linarith

/-- Bound the number of base cells forced to split by the weighted initial
marks within all bases. The constant is independent of the host degree. -/
theorem base_splits (E : V → Finset V) (d : V → V → ℕ)
    (M : V → (i : ℕ) → Cell i → Prop) (base : V → ℕ) (h : ℕ)
    (drop : ∀ v u, u ∈ E v → base u ≤ base v + 8 * d v u)
    (budget : ∀ u, ∑ v, (if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0) ≤ 1 / 2)
    (cut : ∀ v i z, M v i z → i < h + 1) :
    (∑ v, ∑ z, if Spread E (fun v u => 8 * d v u) M v (base v) z then (1 : ℝ) else 0) ≤
      ∑ v, ∑ j ∈ range (h + 1), 2 * (2 : ℝ) ^ ((j + 7) / 8) *
        (∑ z, if M v (base v + j) z then (1 : ℝ) else 0) := by
  let S := Spread E (fun v u => 8 * d v u) M
  let W (N : V → (i : ℕ) → Cell i → Prop) (v : V) :=
    ∑ j ∈ range (h + 1), weight j * count N v (base v + j)
  have hw (j : ℕ) : 0 ≤ weight j := by unfold weight; positivity
  have pos (v : V) (i : ℕ) : 0 ≤ count S v i := sum_nonneg fun _ _ => by positivity
  have high (v : V) (i : ℕ) (hi : h + 1 ≤ i) : count S v i = 0 := by
    have not_marked (z : Cell i) : ¬S v i z := fun hz => hi.not_gt (hz.depth cut)
    simp [count, not_marked]
  have hp (v : V) : 0 ≤ W S v := sum_nonneg fun j _ => mul_nonneg (hw j) (pos _ _)
  have step (v : V) : W S v ≤ W M v + ∑ u ∈ E v, 1 / (2 : ℝ) ^ (d v u) * W S u := by
    calc
      _ ≤ ∑ j ∈ range (h + 1), weight j * (count M v (base v + j) +
          ∑ u ∈ E v, count S u (base v + j + 2 * (8 * d v u))) :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (count_move _ _) (hw j)
      _ ≤ _ := by
        simp_rw [mul_add, sum_add_distrib, mul_sum]
        rw [sum_comm]
        exact add_le_add_right (sum_le_sum fun u hu =>
          edge_shift _ _ _ _ _ (pos u) (high u) (drop v u hu)) _
  have edge := incoming E d budget (W S) hp
  calc
    _ ≤ ∑ v, W S v := by
      apply sum_le_sum
      intro v _
      have := single_le_sum (s := range (h + 1))
        (fun j _ => mul_nonneg (hw j) (pos v (base v + j))) (mem_range.mpr (Nat.zero_lt_succ h))
      change count S v (base v) ≤ W S v
      simpa only [W, weight, Nat.zero_add, Nat.reduceDiv, pow_zero, one_mul, Nat.add_zero] using this
    _ ≤ 2 * ∑ v, W M v := by
      have := sum_le_sum (fun v (_ : v ∈ univ) => step v)
      rw [sum_add_distrib] at this
      linarith
    _ = _ := by simp only [W, weight, count, mul_sum, mul_assoc]

end OAI.LinearAlgebra.MatrixExponent.Packing
end

section
/-!
# Initial marks in the dyadic tree

A heavy cell carries more than one unit of normalized load. Since no
block carries more than half a unit, at least half a unit of ordered
cross products lies in this cell. Only pairwise collisions are needed
to bound the mean number of initial marks.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Packing

open scoped Classical
variable {h i j : ℕ}

/-- Load is normalized by the capacity of a colony. -/
def heavy (l : Cell h → ℝ) (π : Equiv.Perm (Cell h)) (i : ℕ) (z : Cell i) : Prop :=
  ∃ hi : i ≤ h, 1 < ∑ x, if ancestor hi (π x) = z then l x else 0

theorem heavy.ancestor {l : Cell h → ℝ} (hl : ∀ x, 0 ≤ l x) {π : Equiv.Perm (Cell h)}
    {z : Cell j} (hz : heavy l π j z) (hi : i ≤ j) : heavy l π i (ancestor hi z) := by
  obtain ⟨hj, hsum⟩ := hz
  refine ⟨hi.trans hj, hsum.trans_le (Finset.sum_le_sum fun x _ => ?_)⟩
  by_cases hx : Packing.ancestor hj (π x) = z
  · have : Packing.ancestor (hi.trans hj) (π x) = Packing.ancestor hi z :=
      congrArg (Packing.ancestor hi) hx
    simp [hx, this]
  · simp only [ite_eq_right hx]
    split_ifs <;> first | exact hl _ | rfl

theorem heavy.lt {l : Cell h → ℝ} (hl : ∀ x, l x ≤ 1) {π : Equiv.Perm (Cell h)}
    {z : Cell i} (hz : heavy l π i z) : i < h := by
  obtain ⟨hi, hsum⟩ := hz
  refine lt_of_le_of_ne hi ?_
  rintro rfl
  simp only [ancestor_self, ← π.eq_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
  exact (hl _).not_gt hsum

/-- If each block occupies at most a reciprocal power of two units, the
finest levels need no splits. -/
theorem heavy.depth {l : Cell h → ℝ} {π : Equiv.Perm (Cell h)} {z : Cell i} {k : ℕ}
    (hk : k ≤ h) (hl : ∀ x, l x ≤ 1 / (2 : ℝ) ^ k) (hz : heavy l π i z) :
    i < h - k := by
  obtain ⟨hi, hsum⟩ := hz
  by_contra! hd
  have hr : (2 : ℝ) ^ (h - i) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
  apply hsum.not_ge
  calc
    _ ≤ ∑ x, (if Packing.ancestor hi (π x) = z then (1 : ℝ) else 0) * (1 / 2 ^ k) := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs <;> simp only [one_mul, zero_mul, le_refl, hl]
    _ = (2 : ℝ) ^ (h - i) / 2 ^ k := by
      rw [← Finset.sum_mul, Equiv.sum_comp π (fun x => if Packing.ancestor hi x = z then (1 : ℝ) else 0),
        Finset.sum_boole, ← Fintype.card_subtype, card_prefix]
      simp [div_eq_mul_inv]
    _ ≤ 1 := (div_le_one (by positivity)).mpr hr

theorem heavy_bound {M : Type} [Fintype M] (l : Cell h → ℝ) (hl : ∀ x, 0 ≤ l x ∧ l x ≤ 1 / 2)
    (π : M → Equiv.Perm (Cell h)) (hπ : Mixes π) (i : ℕ) :
    (∑ m : M, ∑ z : Cell i, if heavy l (π m) i z then (1 : ℝ) else 0) ≤
      (Fintype.card M : ℝ) * 2 * (∑ x, l x) ^ 2 / (2 : ℝ) ^ i := by
  by_cases hi : i ≤ h
  swap
  · have hn m z : ¬ heavy l (π m) i z := fun h => hi h.choose
    simp only [hn, ite_false, Finset.sum_const_zero]
    positivity
  have hl₀ x := (hl x).1
  calc
    _ ≤ 2 * ∑ m, ∑ z, cross l (π m) i z := by
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro z _
      split_ifs with hz
      · have hb : 1 < load l (π m) i z := by simpa [load, hi] using hz.choose_spec
        unfold cross
        nlinarith [diagonal_le l (π m) i z hl]
      · exact mul_nonneg (by norm_num) (cross_nonneg l (π m) i hl₀ z)
    _ ≤ 2 * ((Fintype.card M : ℝ) * ((∑ x, l x) ^ 2 / (2 : ℝ) ^ i)) :=
      mul_le_mul_of_nonneg_left (cross_bound l i hπ hl₀ hi) (by norm_num)
    _ = _ := by ring

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# A fixed menu of mixers for every block length

The number of candidates is at most the block count. Repetitions and
unused entries are harmless because the election minimizes a score.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

private theorem menu_exists (h : ℕ) :
    ∃ π : Fin (2 ^ h) → (Cell h ≃ₗ[ZMod 2] Cell h),
      ∃ (P : Type) (_ : Fintype P) (_ : Nonempty P) (f : P → Fin (2 ^ h)),
        Mixes (fun p => (π (f p)).toEquiv) := by
  obtain ⟨P, _, _, s, hs, hlin, hcol⟩ := mixer h
  choose g hg using hlin
  obtain ⟨f⟩ : Nonempty (P ↪ Fin (2 ^ h)) := Function.Embedding.nonempty_of_card_le (by simpa)
  let π i := if hi : ∃ q, f q = i then g hi.choose else LinearEquiv.refl _ _
  have he q : (π (f q)).toEquiv = s q := by
    have hq : ∃ t, f t = f q := ⟨q, rfl⟩
    simpa only [π, dite_eq_left hq, f.injective hq.choose_spec] using hg q
  exact ⟨π, P, inferInstance, inferInstance, f, by simpa only [he] using hcol⟩

def menu (h : ℕ) := (menu_exists h).choose

theorem menu_samples (h : ℕ) : ∃ (P : Type) (_ : Fintype P) (_ : Nonempty P)
    (f : P → Fin (2 ^ h)), Mixes (fun p => (menu h (f p)).toEquiv) :=
  (menu_exists h).choose_spec

variable {V : Type} {h : ℕ} (E : V → Finset V) (d : V → V → ℕ)
  (l : V → Cell h → ℝ) (p : Fin (2 ^ h))

def marks := Spread E d (fun v => heavy (l v) (menu h p).toEquiv)

def splits (v : V) := ∑ i ∈ range h, (univ.filter (marks E d l p v i)).card

theorem splits_le (v : V) : splits E d l p v < 2 ^ h := by
  have sum (n : ℕ) : (∑ i ∈ range n, (2 : ℕ) ^ i) < 2 ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, pow_succ]; omega
  refine lt_of_le_of_lt (sum_le_sum ?_) (sum h)
  intro i _
  rw [← card_cell]
  exact card_filter_le _ _

def best [Fintype V] : Prop := ∀ q, ∑ v, splits E d l p v ≤ ∑ v, splits E d l q v

theorem best_exists [Fintype V] : ∃ p, best E d l p := by
  obtain ⟨p, _, hp⟩ := univ.exists_min_image (fun p => ∑ v, splits E d l p v) univ_nonempty
  exact ⟨p, fun q => hp _ (mem_univ q)⟩

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Bad bases in a degree reset

Index contacts by a family and a binary cell within it. Only their two
endpoints are charged on overflow. All positions and contacts use the
same permutation of the blocks.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open Finset
open scoped Classical

private theorem incident {X Y : Type} [Fintype X] [Fintype Y]
    (endpt : Y → Bool → X) (bad : Y → Prop) :
    (∑ x, if ∃ y b, bad y ∧ endpt y b = x then (1 : ℝ) else 0) ≤
      2 * ∑ y, if bad y then (1 : ℝ) else 0 := by
  let f (x : X) (p : Y × Bool) := if bad p.1 ∧ endpt p.1 p.2 = x then (1 : ℝ) else 0
  have hf x p : 0 ≤ f x p := by unfold f; split_ifs <;> norm_num
  calc
    _ ≤ ∑ x, ∑ p, f x p := by
      apply sum_le_sum
      intro x _
      split_ifs with hx
      · obtain ⟨y, b, hy, hb⟩ := hx
        have he : f x (y, b) = 1 := ite_eq_left ⟨hy, hb⟩
        rw [← he]
        exact single_le_sum (fun p _ => hf x p) (mem_univ (y, b))
      · exact sum_nonneg fun p _ => hf x p
    _ = _ := by
      rw [sum_comm, Fintype.sum_prod_type, mul_sum]
      apply sum_congr rfl
      intro y _
      by_cases hy : bad y <;> simp [f, hy]

private theorem charge {X Y : Type} [Fintype X] [Fintype Y]
    (endpt : Y → Bool → X) (mass : X → ℝ) (split : X → Prop) (spill : Y → Prop) :
    (∑ x, if split x ∨ ∃ y b, spill y ∧ endpt y b = x then mass x else 0) ≤
      (∑ x, if 2 < mass x then mass x else 0) +
      2 * (∑ x, if split x then (1 : ℝ) else 0) + 4 * ∑ y, if spill y then (1 : ℝ) else 0 := by
  let hit x := ∃ y b, spill y ∧ endpt y b = x
  calc
    _ ≤ ∑ x, ((if 2 < mass x then mass x else 0) +
          2 * (if split x then (1 : ℝ) else 0) + 2 * (if hit x then (1 : ℝ) else 0)) := by
      apply sum_le_sum
      intro x _
      change (if split x ∨ hit x then mass x else 0) ≤ _
      by_cases hs : split x <;> by_cases hh : hit x <;>
        simp only [hs, hh, or_true, or_false, ite_true, ite_false] <;> split_ifs <;> linarith
    _ ≤ _ := by
      rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
      have := incident endpt spill
      dsimp only [hit]
      linarith

variable {V A : Type} [Fintype V] [Fintype A] {h k : ℕ}
variable (E : V → Finset V) (d : V → V → ℕ) (base : V → ℕ) (q : A → ℕ)
variable (endpt : (Σ c, Cell (q c)) → Bool → Σ v, Cell (base v))
variable (l : V → Cell h → ℝ) (y : A → Cell h → ℝ) (g : ℝ)
variable (π : Equiv.Perm (Cell h))

/-- A split propagated from a cell of load greater than two, or an
endpoint of a contact with load exceeding its mean by more than `1/g`. -/
def BadBase (z : Σ v, Cell (base v)) : Prop :=
  Spread E (fun v u => 8 * d v u) (fun v i z => 2 < load (l v) π i z) z.1 (base z.1) z.2 ∨
  ∃ c b, mean (y c.1) (q c.1) + 1 / g < load (y c.1) π (q c.1) c.2 ∧ endpt c b = z

def badLoad : ℝ :=
  ∑ z, if BadBase E d base q endpt l y g π z then load (l z.1) π (base z.1) z.2 else 0

private theorem charge_splits
    (drop : ∀ v u, u ∈ E v → base u ≤ base v + 8 * d v u)
    (budget : ∀ u, ∑ v, (if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0) ≤ 1 / 2) :
    badLoad E d base q endpt l y g π ≤
      3 * (∑ v, ∑ j ∈ range (h + 1), resetWeight j * excess (l v) π (base v + j)) +
        4 * ∑ c, spills (y c) π (q c) g := by
  let mark v i z := 2 < load (l v) π i z
  have cut v i z (hz : mark v i z) : i < h + 1 := by
    by_contra! bad
    norm_num [mark, load, show ¬ i ≤ h by omega] at hz
  let split (z : Σ v, Cell (base v)) :=
    Spread E (fun v u => 8 * d v u) mark z.1 (base z.1) z.2
  let spill (c : Σ c, Cell (q c)) :=
    mean (y c.1) (q c.1) + 1 / g < load (y c.1) π (q c.1) c.2
  let mass (z : Σ v, Cell (base v)) := load (l z.1) π (base z.1) z.2
  let Q v j := resetWeight j * excess (l v) π (base v + j)
  have hQ v j : 0 ≤ Q v j := by
    unfold Q resetWeight excess
    apply mul_nonneg (by positivity)
    exact sum_nonneg fun z _ => by split_ifs <;> linarith
  have hs : (∑ z, if split z then (1 : ℝ) else 0) ≤ ∑ v, ∑ j ∈ range (h + 1), Q v j := by
    rw [Fintype.sum_sigma]
    apply (base_splits E d mark base h drop budget cut).trans
    apply sum_le_sum
    intro v _
    apply sum_le_sum
    intro j _
    rw [mul_comm 2, mul_assoc]
    exact mul_le_mul_of_nonneg_left (overload_count (l v) π _) (by positivity)
  have hb : (∑ z, if 2 < mass z then mass z else 0) ≤ ∑ v, ∑ j ∈ range (h + 1), Q v j := by
    rw [Fintype.sum_sigma]
    apply sum_le_sum
    intro v _
    have hzero : Q v 0 = excess (l v) π (base v) := by simp [Q, resetWeight]
    exact hzero.symm.trans_le (single_le_sum (fun j _ => hQ v j) (mem_range.mpr (Nat.zero_lt_succ h)))
  have hc : (∑ c, if spill c then (1 : ℝ) else 0) = ∑ c, spills (y c) π (q c) g := by
    rw [Fintype.sum_sigma]
    rfl
  refine le_trans ?_ ((charge endpt mass split spill).trans ?_)
  · unfold badLoad BadBase split spill mass mark
    apply sum_le_sum
    intro z _
    split_ifs <;> rfl
  rw [hc]
  unfold Q at hs hb
  linarith

/-- This quadratic upper bound on the exceptional load can be minimized
using aggregated difference counts. -/
def score (k : ℕ) :=
  3 * (∑ v, ∑ j ∈ range (h + 1), resetWeight j * estimate (l v) π k (base v) j) +
    4 * ∑ c, g ^ 2 * variance (y c) π (q c)

theorem bad_le_score
    (drop : ∀ v u, u ∈ E v → base u ≤ base v + 8 * d v u)
    (budget : ∀ u, ∑ v, (if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0) ≤ 1 / 2)
    (hl : ∀ v x, 0 ≤ l v x ∧ l v x ≤ 1 / (2 : ℝ) ^ k)
    (hb : ∀ v, ∑ x, l v x ≤ (2 : ℝ) ^ (base v)) (hg : 0 < g) :
    badLoad E d base q endpt l y g π ≤ score base q l y g π k := by
  refine (charge_splits E d base q endpt l y g π drop budget).trans ?_
  unfold score
  apply add_le_add
  · refine mul_le_mul_of_nonneg_left (sum_le_sum fun v _ => sum_le_sum fun j _ => ?_) (by norm_num)
    exact mul_le_mul_of_nonneg_left (excess_le_estimate (l v) π (hl v) (hb v) j)
      (by unfold resetWeight; positivity)
  · exact mul_le_mul_of_nonneg_left (sum_le_sum fun c _ => spills_variance _ _ _ hg) (by norm_num)

theorem exists_score
    (hl : ∀ v x, 0 ≤ l v x ∧ l v x ≤ 1 / (2 : ℝ) ^ k)
    (hy : ∀ c x, 0 ≤ y c x ∧ y c x ≤ 1 / (2 : ℝ) ^ k)
    (hb : ∀ v, ∑ x, l v x ≤ (2 : ℝ) ^ (base v))
    (hq : ∀ c, q c ≤ h) :
    ∃ i : Fin (2 ^ h),
      score base q l y g (menu h i).toEquiv k ≤
        144 * resetWeight k / (2 : ℝ) ^ k * (∑ v, ∑ x, l v x) +
        4 * g ^ 2 / (2 : ℝ) ^ k * (∑ c, ∑ x, y c x) := by
  obtain ⟨M, _, _, idx, hp⟩ := menu_samples h
  let p (m : M) := (menu h (idx m)).toEquiv
  let Q m v := ∑ j ∈ range (h + 1), resetWeight j * estimate (l v) (p m) k (base v) j
  let S m c := g ^ 2 * variance (y c) (p m) (q c)
  let L := 48 * resetWeight k / (2 : ℝ) ^ k * (∑ v, ∑ x, l v x)
  let Y := g ^ 2 / (2 : ℝ) ^ k * (∑ c, ∑ x, y c x)
  have hQ : (∑ m, ∑ v, Q m v) ≤ Fintype.card M * L := by
    unfold L
    rw [sum_comm, ← mul_assoc, mul_sum]
    exact sum_le_sum fun v _ => weighted_estimate (l v) hp (hl v) (hb v) (h + 1)
  have hS : (∑ m, ∑ c, S m c) ≤ Fintype.card M * Y := by
    unfold Y
    rw [sum_comm, ← mul_assoc, mul_sum]
    exact sum_le_sum fun c _ => spill_estimate (y c) _ hp (hq c) (hy c) g
  have havg : (∑ m, score base q l y g (p m) k) ≤ ∑ _m : M, (3 * L + 4 * Y) := calc
    _ = ∑ m, (3 * (∑ v, Q m v) + 4 * (∑ c, S m c)) := rfl
    _ ≤ _ := by
      simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
      linarith
  obtain ⟨m, _, hm⟩ := exists_le_of_sum_le univ_nonempty havg
  refine ⟨idx m, ?_⟩
  exact hm.trans_eq (by unfold L Y; ring)

/-- A single linear mixer bounds the total load of all bad bases.
The estimate is independent of the number of tether neighbors. -/
theorem bad_bases
    (drop : ∀ v u, u ∈ E v → base u ≤ base v + 8 * d v u)
    (budget : ∀ u, ∑ v, (if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0) ≤ 1 / 2)
    (hl : ∀ v x, 0 ≤ l v x ∧ l v x ≤ 1 / (2 : ℝ) ^ k)
    (hy : ∀ c x, 0 ≤ y c x ∧ y c x ≤ 1 / (2 : ℝ) ^ k)
    (hb : ∀ v, ∑ x, l v x ≤ (2 : ℝ) ^ (base v))
    (hq : ∀ c, q c ≤ h) (hg : 0 < g) :
    ∃ f : Cell h ≃ₗ[ZMod 2] Cell h,
      badLoad E d base q endpt l y g f.toEquiv ≤
        144 * resetWeight k / (2 : ℝ) ^ k * (∑ v, ∑ x, l v x) +
        4 * g ^ 2 / (2 : ℝ) ^ k * (∑ c, ∑ x, y c x) := by
  obtain ⟨f, hf⟩ := exists_score base q l y g hl hy hb hq
  exact ⟨menu h f, (bad_le_score E d base q endpt l y g (menu h f).toEquiv drop budget hl hb hg).trans hf⟩

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Balanced dyadic partitions

The vertices share a single linear permutation of the block indices.
Loads are normalized by the capacity of one part. In the paper's
notation the minimum length is `A = 2 ^ k` and the edge delay is `2 * d`.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V : Type} [Fintype V] {h k : ℕ}

/-- The count is bounded across all vertices. Each label has exactly the
indicated prefix as its fiber, with bounded load and length at least `2 ^ k`.
The depth comparison applies in both directions on an undirected edge. -/
theorem balanced_partition (E : V → Finset V) (d : V → V → ℕ)
    (hd : ∀ v u, u ∈ E v → 0 < d v u)
    (hs : ∀ u, ∑ v, (if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0) ≤ 1 / 2)
    (hk : 1 ≤ k) (hkh : k ≤ h) (l : V → Cell h → ℝ)
    (hl : ∀ v x, 0 ≤ l v x ∧ l v x ≤ 1 / (2 : ℝ) ^ k)
    (pick : Fin (2 ^ h)) (opt : best E d l pick) :
    let π := menu h pick
    let parts := fun v => leaves (marks E d l pick v) h
    let label := fun v x => leafAt (marks E d l pick v) (π x)
    (∑ v, ((parts v).card : ℝ)) ≤ Fintype.card V + 16 * (∑ v, ∑ x, l v x) ∧
    (∀ v x, label v x ∈ parts v) ∧
    (∀ v c, c ∈ parts v →
      c.1 ≤ h - k ∧ (∃ hi : c.1 ≤ h, ∀ x, label v x = c ↔ ancestor hi (π x) = c.2) ∧
      2 ^ k ≤ (univ.filter fun x => label v x = c).card ∧
      (∑ x, if label v x = c then l v x else 0) ≤ 1) ∧
    (∀ v u, u ∈ E v → ∀ x, (label u x).1 ≤ (label v x).1 + 2 * d v u) := by
  obtain ⟨P, _, _, sample, hcol⟩ := menu_samples h
  let f (p : P) := (menu h (sample p)).toEquiv
  let M (p : P) (v : V) := heavy (l v) (f p)
  have depth (π : Equiv.Perm (Cell h)) v i z (hz : heavy (l v) π i z) : i < h - k :=
    heavy.depth hkh (fun x => (hl v x).2) hz
  have half (v : V) (x : Cell h) : 0 ≤ l v x ∧ l v x ≤ 1 / 2 := by
    refine ⟨(hl v x).1, (hl v x).2.trans (one_div_le_one_div_of_le (by norm_num) ?_)⟩
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
  have hb := spread_bound E d M (fun v => ∑ x, l v x) h
    (fun v => sum_nonneg fun x _ => (hl v x).1) hd hs
    (fun p v i z hz => (depth (f p) v i z hz).trans_le (Nat.sub_le _ _))
    (fun v i => heavy_bound (l v) (half v) f hcol i)
  have havg : (∑ p, ∑ v, ∑ i ∈ range h, ∑ z : Cell i,
      if Spread E d (M p) v i z then (1 : ℝ) else 0) ≤ ∑ _p : P, 16 * (∑ v, ∑ x, l v x) := by
    simpa only [sum_const, card_univ, nsmul_eq_mul, mul_assoc] using hb
  obtain ⟨p, _, hp⟩ := exists_le_of_sum_le univ_nonempty havg
  let π := menu h pick
  let S := marks E d l pick
  have hopt : (∑ v, ∑ i ∈ range h, ∑ z, if S v i z then (1 : ℝ) else 0) ≤
      16 * ∑ v, ∑ x, l v x := by
    have hu := Nat.cast_le (α := ℝ) |>.mpr (opt (sample p))
    simp only [splits, Nat.cast_sum, ← sum_boole] at hu
    exact hu.trans hp
  have stop (v : V) (z : Cell h) : ¬S v h z :=
    fun hz => (Nat.sub_le h k).not_gt (hz.depth (depth π.toEquiv))
  have closed (v : V) (i : ℕ) (_hi : i ≤ h) (c : Cell i) (hm : S v i c) : Reached (S v) i c := by
    intro j hj
    exact hm.up (fun u _ _ hu _ hi => heavy.ancestor (fun x => (hl u x).1) hu hi) j hj.le
  change (∑ v, ((leaves (S v) h).card : ℝ)) ≤ _ ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have count (v : V) : ((leaves (S v) h).card : ℝ) =
        1 + ∑ i ∈ range h, ∑ z : Cell i, if S v i z then (1 : ℝ) else 0 := by
      rw [card_leaves _ (closed v) (stop v), Nat.cast_add, Nat.cast_one, Nat.cast_sum]
      simp only [sum_boole]
    simp only [count, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
    exact add_le_add_right hopt _
  · exact fun v x => leafAt_mem _ _ (stop v _)
  · rintro v ⟨i, c⟩ hc
    obtain ⟨hi, reached, unmarked⟩ := (mem_leaves (S v) _).mp hc
    have small : i ≤ h - k := by
      by_contra! bad
      exact lt_irrefl _ ((reached _ bad).depth (depth π.toEquiv))
    have fiber (x : Cell h) : leafAt (S v) (π x) = ⟨i, c⟩ ↔ ancestor hi (π x) = c :=
      leafAt_eq_iff _ _ hi ⟨reached, unmarked⟩
    refine ⟨small, ⟨hi, ?_⟩, ?_, ?_⟩
    · exact fiber
    · change 2 ^ k ≤ (univ.filter fun x => leafAt (S v) (π.toEquiv x) = ⟨i, c⟩).card
      rw [card_leafAt _ _ hc]
      exact Nat.pow_le_pow_right (by decide) (by omega : k ≤ h - i)
    · apply le_of_not_gt
      intro bad
      change 1 < ∑ x, if leafAt (S v) (π x) = ⟨i, c⟩ then l v x else 0 at bad
      apply unmarked
      apply Spread.start
      exact ⟨hi, by simpa only [fiber, π, LinearEquiv.coe_toEquiv] using bad⟩
  · intro v u hu x
    exact leafDepth_le_add (S u) (S v) (2 * d v u)
      (fun _ _ c hc => Spread.move hu c hc) (π x)

end OAI.LinearAlgebra.MatrixExponent.Packing
end
