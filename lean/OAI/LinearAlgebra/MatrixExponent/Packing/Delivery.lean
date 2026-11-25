import OAI.LinearAlgebra.MatrixExponent.Packing.Projection
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import OAI.LinearAlgebra.MatrixExponent.Packing.Occupancy
import OAI.LinearAlgebra.MatrixExponent.Packing.Reservations
import OAI.LinearAlgebra.MatrixExponent.Packing.Suffix

/-!
# Terminal loads at a good base

Loads and reserved capacities are measured in units of `F B`. The
reservation slots depend only on capacities. The assignment of units
to slots on a contact can be used at both ends of that contact.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {T : Type} [Fintype T] {Y : ℕ}

private theorem assign_load (l : T → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hl : ∀ t, 0 ≤ l t ∧ l t ≤ D) (hY : 0 < Y) :
    ∃ p : T → Fin Y, ∀ i, (∑ t, if p t = i then l t else 0) * Y ≤ (∑ t, l t) + D * Y := by
  have : Nonempty (Fin Y) := ⟨⟨0, hY⟩⟩
  have aux (s : Finset T) : ∃ p : T → Fin Y, ∀ i,
      (∑ t ∈ s, if p t = i then l t else 0) * Y ≤ (∑ t ∈ s, l t) + D * Y := by
    induction s using Finset.induction with
    | empty => exact ⟨fun _ => ⟨0, hY⟩, fun _ => by simp [mul_nonneg hD]⟩
    | @insert t s ht ih =>
      obtain ⟨p, hp⟩ := ih
      have avg : (∑ i : Fin Y, (∑ a ∈ s, if p a = i then l a else 0) * Y) ≤
          ∑ _i : Fin Y, ∑ a ∈ s, l a := by
        rw [← sum_mul, sum_comm]
        simp [mul_comm]
      obtain ⟨j, _, hj⟩ := exists_le_of_sum_le univ_nonempty avg
      refine ⟨Function.update p t j, fun i => ?_⟩
      have same : (∑ a ∈ s, if Function.update p t j a = i then l a else 0) =
          ∑ a ∈ s, if p a = i then l a else 0 := by
        refine sum_congr rfl fun a ha => ?_
        rw [Function.update_of_ne (show a ≠ t from fun e => ht (e ▸ ha))]
      rw [sum_insert ht, sum_insert ht, Function.update_self, same]
      by_cases he : j = i
      · subst i
        rw [ite_eq_left rfl, add_mul]
        have := mul_le_mul_of_nonneg_right (hl t).2 (Nat.cast_nonneg Y)
        linarith [(hl t).1]
      · rw [ite_eq_right he, zero_add]
        linarith [hp i, (hl t).1]
  exact aux univ

/-- Assign each old tensor whole to one input terminal. -/
theorem input_terminals (hY : 0 < Y) (l : T → ℝ) (hs : ∑ t, l t ≤ 2)
    (hl : ∀ t, 0 ≤ l t ∧ l t * Y ≤ 1) :
    ∃ p : T → Fin Y, ∀ i, (∑ t, if p t = i then l t else 0) * Y ≤ 3 := by
  have hy : (0 : ℝ) < Y := Nat.cast_pos.mpr hY
  obtain ⟨p, hp⟩ := assign_load l (1 / Y) (by positivity)
    (fun t => ⟨(hl t).1, (le_div_iff₀ hy).mpr (hl t).2⟩) hY
  rw [div_mul_cancel₀ _ hy.ne'] at hp
  exact ⟨p, fun i => by linarith [hp i]⟩

/-- Reserve disjoint output terminals using the contact capacities alone. -/
theorem reserve_terminals (c : T → ℝ) (hc : ∀ t, 0 ≤ c t)
    (hs : ∑ t, c t ≤ 2) (hcount : 4 * Fintype.card T ≤ Y) :
    Nonempty ((Σ t, Fin ⌈c t * Y / 8⌉₊) ↪ Fin Y) := by
  apply Function.Embedding.nonempty_of_card_le
  simp only [Fintype.card_sigma, Fintype.card_fin]
  have hy : (0 : ℝ) ≤ Y := Nat.cast_nonneg _
  have hnum : (4 : ℝ) * Fintype.card T ≤ Y := by exact_mod_cast hcount
  have ht (t : T) : (⌈c t * Y / 8⌉₊ : ℝ) ≤ c t * Y / 8 + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (hc t) hy) (by norm_num))).le
  have hsum := sum_le_sum (fun t (_ : t ∈ univ) => ht t)
  rw [sum_add_distrib, ← sum_div, ← sum_mul, sum_const, card_univ, nsmul_eq_mul, mul_one] at hsum
  have := mul_le_mul_of_nonneg_right hs hy
  exact_mod_cast (show (∑ t, (⌈c t * Y / 8⌉₊ : ℝ)) ≤ Y by linarith)

/-- One slot choice per unit suffices at both endpoints of a contact. -/
theorem contact_terminals (hY : 0 < Y) (l : T → ℝ) (c : ℝ) (hc : 0 < c)
    (hs : ∑ t, l t ≤ c) (hl : ∀ t, 0 ≤ l t ∧ l t * Y ≤ 1) :
    ∃ p : T → Fin ⌈c * Y / 8⌉₊, ∀ i, (∑ t, if p t = i then l t else 0) * Y ≤ 9 := by
  have hy : (0 : ℝ) < Y := Nat.cast_pos.mpr hY
  let r := ⌈c * Y / 8⌉₊
  have hr : 0 < r := Nat.ceil_pos.mpr (by positivity)
  obtain ⟨p, hp⟩ := assign_load l (1 / Y) (by positivity)
    (fun t => ⟨(hl t).1, (le_div_iff₀ hy).mpr (hl t).2⟩) hr
  refine ⟨p, fun i => le_of_mul_le_mul_right ?_ (Nat.cast_pos.mpr hr : (0 : ℝ) < r)⟩
  have hslot : c * Y / 8 ≤ (r : ℝ) := Nat.le_ceil _
  have hload := mul_le_mul_of_nonneg_right (hp i) hy.le
  have hsum := mul_le_mul_of_nonneg_right hs hy.le
  rw [add_mul, mul_right_comm (1 / (Y : ℝ)), div_mul_cancel₀ _ hy.ne', one_mul] at hload
  linarith

/-- Place a good base's demand matrix on permutations with total normalized
width at most ten. Each layer has `Y` rows of `w` ports of width `u`. -/
theorem good_base_layers (hY : 0 < Y) {w : ℕ} (hw : 0 < w) (u : ℝ) (hu : 0 < u)
    (overhead : (Y : ℝ) ^ 2 * w * u ≤ 1) (a : Fin Y → Fin Y → ℕ)
    (rows : ∀ i, (∑ j, (a i j : ℝ)) * Y * u ≤ 9)
    (cols : ∀ j, (∑ i, (a i j : ℝ)) * Y * u ≤ 9) :
    ∃ (n : ℕ) (σ : Fin n → Equiv.Perm (Fin Y)), (n : ℝ) * Y * w * u ≤ 10 ∧
      ∀ i j, Nonempty (Fin (a i j) ↪ {t // σ t i = j} × Fin w) := by
  have hpos : 0 < (Y : ℝ) * u := mul_pos (Nat.cast_pos.mpr hY) hu
  let U := ⌊9 / ((Y : ℝ) * u)⌋₊
  have small (g : Fin Y → ℕ) (hg : (∑ i, (g i : ℝ)) * Y * u ≤ 9) : ∑ i, g i ≤ U := by
    apply Nat.le_floor
    rw [le_div_iff₀ hpos, Nat.cast_sum, ← mul_assoc]
    exact hg
  obtain ⟨σ, hσ⟩ := rotor_placement a U w hw (fun i => small _ (rows i)) (fun j => small _ (cols j))
  refine ⟨_, σ, ?_, hσ⟩
  have hU : (U : ℝ) * Y * u ≤ 9 * 1 := by
    rw [mul_assoc, mul_one, ← le_div_iff₀ hpos]
    exact Nat.floor_le (by positivity)
  simpa only [Fintype.card_fin, mul_one] using rotor_cost U Y w u 1 hu.le hU overhead

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-! # Consistent delivery slots at both ends of each contact -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

/-- Assign a slot to each unit once, independently of the endpoint. A
contact carrying no units needs no slots, even when its capacity is zero. -/
theorem delivery_slots {A W : Type} [Fintype A] (edge : A → W) (cap : W → ℝ)
    (Y : ℕ) (hY : 0 < Y) (u : ℝ) (hu : 0 < u) (hunit : u * Y ≤ 1)
    (bound : ∀ w, (∑ a, if edge a = w then u else 0) ≤ cap w) :
    ∃ s : A → ℕ, (∀ a, s a < ⌈cap (edge a) * Y / 8⌉₊) ∧
      (∀ w k, (∑ a, if edge a = w ∧ s a = k then u else 0) * Y ≤ 9) := by
  have assign (w : W) :
      ∃ t : A → ℕ, (∀ a, edge a = w → t a < ⌈cap w * Y / 8⌉₊) ∧
        ∀ k, (∑ a, if edge a = w ∧ t a = k then u else 0) * Y ≤ 9 := by
    by_cases hw : ∃ a, edge a = w
    · let l (a : A) := if edge a = w then u else 0
      have hl (a : A) : 0 ≤ l a ∧ l a * Y ≤ 1 := by
        by_cases ha : edge a = w <;> simp [l, ha, hunit, hu.le]
      have hc : 0 < cap w := by
        obtain ⟨a, ha⟩ := hw
        exact lt_of_lt_of_le (sum_pos' (fun i _ => (hl i).1)
          ⟨a, mem_univ a, by simpa [l, ha] using hu⟩) (bound w)
      obtain ⟨p, hp⟩ := contact_terminals hY l (cap w) hc (bound w) hl
      refine ⟨fun a => (p a).val, fun a _ => (p a).isLt, ?_⟩
      intro k
      by_cases hk : k < ⌈cap w * Y / 8⌉₊
      · simpa only [and_comm (a := edge _ = w), ite_and, l, Fin.ext_iff] using hp ⟨k, hk⟩
      · have hn (a : A) : (p a).val ≠ k := fun e => hk (e ▸ (p a).isLt)
        simp [hn]
    · push Not at hw
      exact ⟨fun _ => 0, by simp [hw], by simp [hw]⟩
  choose t ht hcap using assign
  refine ⟨fun a => t (edge a) a, fun a => ht _ a rfl, fun w k => ?_⟩
  have he (a : A) : (edge a = w ∧ t (edge a) a = k) ↔ (edge a = w ∧ t w a = k) := by
    by_cases ha : edge a = w <;> simp [ha]
  simpa only [he] using hcap w k

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Leaves of a dyadic partition

A mark splits its cell into two children. Following the prefix of a point
until the first unsplit cell gives its unique leaf.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable (M : (i : ℕ) → Cell i → Prop) {h i : ℕ}

/-- The cells reached by splitting marked cells, including the root. -/
def Reached (i : ℕ) (c : Cell i) : Prop :=
  ∀ j (hj : j < i), M j (ancestor hj.le c)

def Leaf (i : ℕ) (c : Cell i) : Prop :=
  Reached M i c ∧ ¬M i c

def leaves (h : ℕ) : Finset (Σ i, Cell i) :=
  (range (h + 1)).sigma fun i => univ.filter (Leaf M i)

@[simp] theorem mem_leaves (c : Σ i, Cell i) :
    c ∈ leaves M h ↔ c.1 ≤ h ∧ Leaf M c.1 c.2 := by
  simp [leaves]

private theorem stop_exists (x : Cell h) :
    ∃ i, ∀ hi : i < h, ¬M i (ancestor hi.le x) :=
  ⟨h, fun hi => (lt_irrefl h hi).elim⟩

/-- Stop at the first unmarked prefix, or at full depth. -/
def leafDepth (x : Cell h) : ℕ :=
  Nat.find (stop_exists M x)

theorem leafDepth_le (x : Cell h) : leafDepth M x ≤ h :=
  Nat.find_min' (stop_exists M x) fun hi => (lt_irrefl h hi).elim

theorem leafDepth_le_of_unmarked (x : Cell h) (hi : i ≤ h) (hc : ¬M i (ancestor hi x)) :
    leafDepth M x ≤ i :=
  Nat.find_min' (stop_exists M x) fun _ => hc

theorem marked_before_leaf (x : Cell h) (hi : i ≤ h) (hd : i < leafDepth M x) :
    M i (ancestor hi x) := by
  by_contra hn
  exact hd.not_ge (leafDepth_le_of_unmarked M x hi hn)

theorem leafDepth_spec (x : Cell h) (hstop : ¬M h x) :
    Leaf M (leafDepth M x) (ancestor (leafDepth_le M x) x) := by
  refine ⟨fun j hj => marked_before_leaf M x (hj.le.trans (leafDepth_le M x)) hj, ?_⟩
  have hm : ∀ i (hi : i ≤ h), i = h → ¬M i (ancestor hi x) := by
    rintro _ _ rfl
    exact hstop
  rcases (leafDepth_le M x).lt_or_eq with hl | he
  · exact Nat.find_spec (stop_exists M x) hl
  · exact hm _ _ he

def leafAt (x : Cell h) : Σ i, Cell i :=
  ⟨leafDepth M x, ancestor (leafDepth_le M x) x⟩

theorem leafAt_mem (x : Cell h) (hstop : ¬M h x) :
    leafAt M x ∈ leaves M h :=
  (mem_leaves M _).mpr ⟨leafDepth_le M x, leafDepth_spec M x hstop⟩

/-- The fiber over a leaf consists of precisely the points with that prefix. -/
theorem leafAt_eq_iff (x : Cell h) {c : Cell i} (hi : i ≤ h) (hl : Leaf M i c) :
    leafAt M x = ⟨i, c⟩ ↔ ancestor hi x = c := by
  constructor
  · intro he
    have hd : leafDepth M x = i := congrArg Sigma.fst he
    subst i
    exact eq_of_heq (Sigma.mk.inj he).2
  · rintro rfl
    have hd : leafDepth M x = i := by
      refine le_antisymm (leafDepth_le_of_unmarked M x hi hl.2) (le_of_not_gt ?_)
      intro hlt
      exact Nat.find_spec (stop_exists M x) (hlt.trans_le hi) (hl.1 _ hlt)
    subst i
    rfl

/-- A leaf of depth `i` contains exactly `2 ^ (h-i)` points, even
after a common permutation of the indices. -/
theorem card_leafAt (π : Equiv.Perm (Cell h)) {c : Σ i, Cell i} (hc : c ∈ leaves M h) :
    (univ.filter fun x => leafAt M (π x) = c).card = 2 ^ (h - c.1) := by
  obtain ⟨i, c⟩ := c
  obtain ⟨hi, hl⟩ := (mem_leaves M _).mp hc
  rw [← card_prefix hi c, Fintype.card_subtype]
  apply card_equiv π
  intro x
  simpa only [mem_filter, mem_univ, true_and] using leafAt_eq_iff M (π x) hi hl

/-- A split propagated up by `d` levels costs at most `d` levels of depth
at a common point. -/
theorem leafDepth_le_add (N : (i : ℕ) → Cell i → Prop) (d : ℕ)
    (propagate : ∀ i, i + d < h → ∀ c : Cell (i + d),
      M (i + d) c → N i (ancestor (Nat.le_add_right i d) c))
    (x : Cell h) : leafDepth M x ≤ leafDepth N x + d := by
  apply le_of_not_gt
  intro bad
  have hi := bad.trans_le (leafDepth_le M x)
  have hm := marked_before_leaf M x hi.le bad
  exact Nat.find_spec (stop_exists N x) ((Nat.le_add_right _ _).trans_lt hi)
    (propagate _ hi _ hm)

private theorem split_level (hc : ∀ c, M i c → Reached M i c) :
    (univ.filter (M i)).card + (univ.filter (Leaf M i)).card =
      (univ.filter (Reached M i)).card := by
  let s := univ.filter (Reached M i)
  have hm : s.filter (M i) = univ.filter (M i) := by
    ext c
    simp only [s, mem_filter, mem_univ, true_and]
    exact ⟨And.right, fun h => ⟨hc c h, h⟩⟩
  have hl : s.filter (fun c => ¬M i c) = univ.filter (Leaf M i) := by
    ext c
    simp [s, Leaf]
  rw [← hm, ← hl]
  exact card_filter_add_card_filter_not _

private theorem reached_succ (hc : ∀ c, M i c → Reached M i c) :
    (univ.filter (Reached M (i + 1))).card = 2 * (univ.filter (M i)).card := by
  have he : (univ.filter (Reached M (i + 1))).card =
      ((univ : Finset (ZMod 2)) ×ˢ univ.filter (M i)).card := by
    apply card_equiv (Fin.snocEquiv (fun _ : Fin (i + 1) => ZMod 2)).symm
    intro c
    simp only [mem_filter, mem_univ, true_and, mem_product]
    change Reached M (i + 1) c ↔ M i (ancestor (Nat.le_succ i) c)
    refine ⟨fun h => h i (Nat.lt_succ_self i), fun hm j hj => ?_⟩
    rcases (Nat.le_of_lt_succ hj).lt_or_eq with hl | rfl
    · exact hc _ hm j hl
    · exact hm
  simpa using he

/-- Each marked cell adds one leaf. -/
theorem card_leaves (closed : ∀ i, i ≤ h → ∀ c, M i c → Reached M i c)
    (stop : ∀ c, ¬M h c) :
    (leaves M h).card = 1 + ∑ i ∈ range h, (univ.filter (M i)).card := by
  have aux : ∀ k, k ≤ h →
      (leaves M k).card + (univ.filter (M k)).card =
        1 + ∑ i ∈ range k, (univ.filter (M i)).card := by
    intro k hk
    induction k with
    | zero =>
      have he := split_level M (closed _ hk)
      have hr : univ.filter (Reached M 0) = univ := by ext; simp [Reached]
      rw [hr] at he
      simpa [leaves, card_sigma, add_comm] using he
    | succ k ih =>
      have hp := ih ((Nat.le_succ k).trans hk)
      have he := split_level M (closed _ hk)
      rw [reached_succ M (closed _ ((Nat.le_succ k).trans hk))] at he
      simp only [leaves, card_sigma] at hp ⊢
      rw [sum_range_succ, sum_range_succ (fun i => (univ.filter (M i)).card)]
      omega
  simpa [stop] using aux h le_rfl

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Units routed through a good base

The demand units are individually named. After assigning input items and
reserving output terminals, place each unit in a distinct port at each end
of its permutation layer.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {Y w : ℕ} {A T O : Type} [Fintype A] [Fintype T]

private theorem route_layers (hY : 0 < Y) (hw : 0 < w) (u : ℝ) (hu : 0 < u)
    (overhead : (Y : ℝ) ^ 2 * w * u ≤ 1) (p q : A → Fin Y)
    (hp : ∀ i, (∑ a, if p a = i then u else 0) * Y ≤ 9)
    (hq : ∀ j, (∑ a, if q a = j then u else 0) * Y ≤ 9) :
    ∃ (n : ℕ) (σ : Fin n → Equiv.Perm (Fin Y)) (r : A → Fin n × Fin w),
      (n : ℝ) * Y * w * u ≤ 10 ∧
      (∀ a, σ (r a).1 (p a) = q a) ∧
      Function.Injective (fun a => (p a, r a)) ∧ Function.Injective (fun a => (q a, r a)) := by
  let m (i j : Fin Y) := (univ.filter fun a => p a = i ∧ q a = j).card
  have count (i j : Fin Y) : (m i j : ℝ) * u = ∑ a, if p a = i ∧ q a = j then u else 0 := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
  have rows i : (∑ j, (m i j : ℝ)) * Y * u ≤ 9 := by
    rw [mul_right_comm, sum_mul]
    simp_rw [count]
    rw [sum_comm]
    simpa [and_comm (a := p _ = i), ite_and] using hp i
  have cols j : (∑ i, (m i j : ℝ)) * Y * u ≤ 9 := by
    rw [mul_right_comm, sum_mul]
    simp_rw [count]
    rw [sum_comm]
    simpa [ite_and] using hq j
  obtain ⟨n, σ, hcost, layers⟩ := good_base_layers hY hw u hu overhead m rows cols
  have slots i j : ∃ f : {a // p a = i ∧ q a = j} → Fin n × Fin w,
      Function.Injective f ∧ ∀ a, σ (f a).1 i = j := by
    obtain ⟨e⟩ := layers i j
    let g := (Fintype.equivFinOfCardEq
      (show Fintype.card {a // p a = i ∧ q a = j} = m i j from Fintype.card_subtype _)).toEmbedding.trans e
    refine ⟨fun a => ((g a).1.val, (g a).2), ?_, fun a => (g a).1.property⟩
    intro a b eq
    exact g.injective (Prod.ext (Subtype.ext (Prod.mk.inj eq).1) (Prod.mk.inj eq).2)
  choose f hf hs using slots
  let r (a : A) := f (p a) (q a) ⟨a, rfl, rfl⟩
  have hr a : σ (r a).1 (p a) = q a := hs _ _ _
  have he a i j (hi : p a = i) (hj : q a = j) : r a = f i j ⟨a, hi, hj⟩ := by
    subst i; subst j; rfl
  have inj : Function.Injective (fun a => (p a, r a)) := by
    intro a b eq
    obtain ⟨hi, heq⟩ := Prod.mk.inj eq
    have hj : q a = q b := by rw [← hr a, ← hr b, heq, hi]
    rw [he a _ _ hi hj, he b _ _ rfl rfl] at heq
    exact congrArg Subtype.val (hf _ _ heq)
  refine ⟨n, σ, r, hcost, hr, inj, ?_⟩
  intro a b eq
  obtain ⟨hj, heq⟩ := Prod.mk.inj eq
  rw [← hr a, ← hr b, heq] at hj
  exact inj (Prod.ext ((σ _).injective hj) heq)

/-- Route named units, keeping all input items whole and respecting the
predetermined assignment to reserved output slots. -/
theorem route_good_base (hY : 0 < Y) (hw : 0 < w) (u : ℝ) (hu : 0 < u)
    (overhead : (Y : ℝ) ^ 2 * w * u ≤ 1) (src : A → T) (dst : A → O) (out : O ↪ Fin Y)
    (l : T → ℝ) (total : ∑ t, l t ≤ 2) (item : ∀ t, 0 ≤ l t ∧ l t * Y ≤ 1)
    (hs : ∀ t, (∑ a, if src a = t then u else 0) ≤ l t)
    (hd : ∀ o, (∑ a, if dst a = o then u else 0) * Y ≤ 9) :
    ∃ (p : T → Fin Y) (n : ℕ) (σ : Fin n → Equiv.Perm (Fin Y)) (r : A → Fin n × Fin w),
      (∀ i, (∑ t, if p t = i then l t else 0) * Y ≤ 3) ∧ (n : ℝ) * Y * w * u ≤ 10 ∧
      (∀ a, σ (r a).1 (p (src a)) = out (dst a)) ∧
      Function.Injective (fun a => (p (src a), r a)) ∧
      Function.Injective (fun a => (out (dst a), r a)) := by
  obtain ⟨p, hp⟩ := input_terminals hY l total item
  have source i : (∑ a, if p (src a) = i then u else 0) * Y ≤ 9 := by
    refine le_trans ?_ ((hp i).trans (by norm_num : (3 : ℝ) ≤ 9))
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    calc
      _ = ∑ t, ∑ a, if src a = t then (if p t = i then u else 0) else 0 := by
        rw [sum_comm]
        simp
      _ ≤ _ := by
        refine sum_le_sum fun t _ => ?_
        split_ifs with h
        · exact hs t
        · simp
  have dest j : (∑ a, if out (dst a) = j then u else 0) * Y ≤ 9 := by
    by_cases hr : ∃ o, out o = j
    · obtain ⟨o, rfl⟩ := hr
      simpa only [out.injective.eq_iff] using hd o
    · push Not at hr
      simp [hr]
  obtain ⟨n, σ, r, hh⟩ := route_layers hY hw u hu overhead _ _ source dest
  exact ⟨p, n, σ, r, hp, hh⟩

variable {V : Type}

/-- Each contact between two base cells has a slot at either endpoint. -/
abbrev BaseContact (base : V → ℕ) (ends : A → Bool → V) (v : V) (z : Cell (base v)) :=
  {e : Σ c : A, Bool × Cell (contactDepth base ends c) //
    contactEnd base ends ⟨e.1, e.2.2⟩ e.2.1 = ⟨v, z⟩}

/-- The capacities at both ends of a contact prescribe the same number
of slots. This reservation precedes the choice of a permutation. -/
theorem reserve_base (base : V → ℕ) (ends : A → Bool → V) (v : V) (z : Cell (base v))
    (s : ℕ) (D : ℝ) (hD : 0 < D) (y : A → ℝ) (hy : ∀ c, 0 ≤ y c)
    (gap : ∀ c t, ends c t = v → contactDepth base ends c ≤ base v + s)
    (degree : (∑ c, ∑ t : Bool, if ends c t = v then (1 : ℝ) else 0) ≤ D)
    (mass : (∑ c, ∑ t : Bool, if ends c t = v then y c else 0) ≤ (2 : ℝ) ^ (base v))
    (enough : 4 * (D * (2 : ℝ) ^ s) ≤ Y) :
    let cap := fun c => y c / (2 : ℝ) ^ (contactDepth base ends c) + 1 / (D * (2 : ℝ) ^ s)
    Nonempty ((Σ e : BaseContact base ends v z, Fin ⌈cap e.val.1 * Y / 8⌉₊) ↪ Fin Y) := by
  intro cap
  let C := BaseContact base ends v z
  have sum_contacts (l : A → ℝ) : (∑ e : C, l e.val.1) =
      ∑ c, ∑ t, ∑ w, if contactEnd base ends ⟨c, w⟩ t = ⟨v, z⟩ then l c else 0 := by
    let p (e : Σ c : A, Bool × Cell (contactDepth base ends c)) :=
      contactEnd base ends ⟨e.1, e.2.2⟩ e.2.1 = ⟨v, z⟩
    rw [← sum_subtype (univ.filter p) (fun _ => mem_filter_univ _) (fun e => l e.1)]
    simp only [sum_filter, Fintype.sum_sigma, Fintype.sum_prod_type, p]
  apply reserve_terminals (fun e : C => cap e.val.1)
  · intro e
    have := hy e.val.1
    unfold cap
    positivity
  · rw [sum_contacts]
    exact reservation_bound base ends y v z s D hD gap degree mass
  · have hc : (Fintype.card C : ℝ) ≤ D * (2 : ℝ) ^ s := by
      have hb := reservation_count base ends v z s D gap degree
      rw [← sum_contacts (fun _ => 1)] at hb
      simpa using hb
    exact_mod_cast (show (4 : ℝ) * Fintype.card C ≤ Y by linarith)

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Routing all good units through reserved output terminals

Choose the same link slot at both ends, then apply the per-base routing
theorem independently at each leaf. No rotor layers are needed on leaves
without good demand.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open Finset
open scoped Classical

theorem sub_sum {P : Type} [Fintype P] (p : P → Prop) [DecidablePred p] (l : P → ℝ) :
    (∑ t : {i // p i}, l t.val) = ∑ t, if p t then l t else 0 := by
  rw [← sum_subtype (univ.filter p) (fun _ => mem_filter_univ _) l, sum_filter]

private theorem units_mono {A B : Type} [Fintype A] [Fintype B]
    (u : ℝ) (hu : 0 ≤ u) (s : A → Prop) (t : B → Prop) [DecidablePred t]
    (f : A → B) (hs : ∀ a, s a → t (f a))
    (hi : ∀ a b, s a → s b → f a = f b → a = b) :
    (∑ a, if s a then u else 0) ≤ ∑ b, if t b then u else 0 := by
  simp only [← sum_filter, sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card_of_injOn f ?_ ?_)) hu
  · intro a ha
    exact mem_filter_univ _ |>.mpr (hs a ((mem_filter.mp ha).2))
  · intro a ha b hb he
    exact hi a b (mem_filter.mp ha).2 (mem_filter.mp hb).2 he

variable {P U X W : Type} [Fintype P] [Fintype U]

omit [Fintype P] in
/-- Bounds at either end of a routing problem, independent of the
particular balanced choice of slots. -/
theorem delivery_bound (leaf : P → X) (point : U → Bool → P) (good : U → Prop)
    (edge : U → W) (outLeaf : W → Bool → X) (cap : W → ℝ) (Y : ℕ) (l : P → ℝ) (u : ℝ)
    (hu : 0 < u) (agree : ∀ a, good a → ∀ t, leaf (point a t) = outLeaf (edge a) t)
    (slot : ∀ a : {i // good i}, Fin ⌈cap (edge a.val) * Y / 8⌉₊)
    (hs : ∀ p, push (Function.uncurry point) (fun _ => u) p ≤ l p)
    (bound : ∀ i k,
      (∑ a : {a // good a}, if edge a.val = i ∧ (slot a).val = k then u else 0) * Y ≤ 9)
    (x : X) :
    let src (q : GoodEnd leaf point good x) : {p // leaf p = x} :=
      ⟨point q.val.1.val q.val.2, q.property⟩
    let dst := portOf leaf point good edge outLeaf cap Y agree slot (x := x)
    (∀ t, push src (fun _ => u) t ≤ l t.val) ∧ (∀ o, push dst (fun _ => u) o * Y ≤ 9) := by
  let T x := {p // leaf p = x}
  let Q x := GoodEnd leaf point good x
  let src x (q : Q x) : T x := ⟨point q.val.1.val q.val.2, q.property⟩
  let dst x (q : Q x) := portOf leaf point good edge outLeaf cap Y agree slot q
  have srcBound x (t : T x) : push (src x) (fun _ => u) t ≤ l t.val := by
    apply le_trans _ (hs t.val)
    apply units_mono u hu.le _ _ (fun q : Q x => (q.val.1.val, q.val.2))
    · intro q hq
      exact congrArg Subtype.val hq
    · intro a b _ _ h
      exact Subtype.ext (Prod.ext (Subtype.ext (Prod.mk.inj h).1) (Prod.mk.inj h).2)
  have dstBound x (o : Port outLeaf cap Y x) :
      push (dst x) (fun _ => u) o * Y ≤ 9 := by
    apply le_trans _ (bound o.1.val.1 o.2.val)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg Y)
    apply units_mono u hu.le _ _ (fun q : Q x => q.val.1)
    · intro q hq
      exact ⟨congrArg (fun a => a.1.val.1) hq, congrArg (fun a => a.2.val) hq⟩
    · intro a b ha hb h
      exact Subtype.ext (Prod.ext h (congrArg (fun a => a.1.val.2) (ha.trans hb.symm)))
  exact ⟨srcBound x, dstBound x⟩

/-- All widths are measured in units of the common base capacity. -/
theorem deliver (leaf : P → X) (point : U → Bool → P) (good : U → Prop)
    (edge : U → W) (outLeaf : W → Bool → X) (cap : W → ℝ) (Y w : ℕ)
    (out : ∀ x, Port outLeaf cap Y x ↪ Fin Y) (l : P → ℝ) (u : ℝ)
    (hY : 0 < Y) (hw : 0 < w) (hu : 0 < u) (overhead : (Y : ℝ) ^ 2 * w * u ≤ 1)
    (agree : ∀ a, good a → ∀ t, leaf (point a t) = outLeaf (edge a) t)
    (total : ∀ x, push leaf l x ≤ 2) (item : ∀ p, 0 ≤ l p ∧ l p * Y ≤ 1)
    (hs : ∀ p, push (Function.uncurry point) (fun _ => u) p ≤ l p)
    (hd : ∀ i, push edge (fun a => if good a then u else 0) i ≤ cap i) :
    Nonempty (Delivery leaf point good edge outLeaf cap Y w out l u) := by
  have hunit : u * Y ≤ 1 := calc
    _ ≤ (Y : ℝ) ^ 2 * w * u := by
      rw [mul_comm u]
      apply mul_le_mul_of_nonneg_right _ hu.le
      exact_mod_cast (show Y ≤ Y ^ 2 * w from (by nlinarith [Nat.mul_le_mul_left (Y ^ 2) hw]))
    _ ≤ 1 := overhead
  let A := {i // good i}
  have hcap (i : W) : (∑ a : A, if edge a.val = i then u else 0) ≤ cap i := by
    apply le_trans _ (hd i)
    rw [sub_sum good (fun a => if edge a = i then u else 0)]
    exact sum_le_sum fun a _ => by dsimp; split_ifs <;> rfl
  obtain ⟨s, hslot, bound⟩ := delivery_slots (fun a : A => edge a.val) cap Y hY u hu hunit hcap
  let slot (a : A) : Fin ⌈cap (edge a.val) * Y / 8⌉₊ := ⟨s a, hslot a⟩
  let T x := {p // leaf p = x}
  let Q x := GoodEnd leaf point good x
  let src x (q : Q x) : T x := ⟨point q.val.1.val q.val.2, q.property⟩
  let dst x (q : Q x) := portOf leaf point good edge outLeaf cap Y agree slot q
  have hroute := delivery_bound leaf point good edge outLeaf cap Y l u hu agree slot hs bound
  have route (x : X) :
      ∃ (p : T x → Fin Y) (n : ℕ) (σ : Fin n → Equiv.Perm (Fin Y)) (r : Q x → Fin n × Fin w),
        (∀ i, (∑ t, if p t = i then l t.val else 0) * Y ≤ 3) ∧
        (n : ℝ) * Y * w * u ≤ 10 ∧ (IsEmpty (Q x) → n = 0) ∧
        (∀ a, σ (r a).1 (p (src x a)) = out x (dst x a)) ∧
        Function.Injective (fun a => (p (src x a), r a)) ∧
        Function.Injective (fun a => (out x (dst x a), r a)) := by
    obtain ⟨p, n, σ, r, hp, hn, hr⟩ := route_good_base hY hw u hu overhead
      (src x) (dst x) (out x) (fun t => l t.val)
      ((sub_sum _ _).le.trans (total x)) (fun t => item t.val) (hroute x).1 (hroute x).2
    by_cases h : IsEmpty (Q x)
    · exact ⟨p, 0, Fin.elim0, isEmptyElim, hp, by simp, fun _ => rfl,
        isEmptyElim, isEmptyElim, isEmptyElim⟩
    · exact ⟨p, n, σ, r, hp, hn, fun he => (h he).elim, hr⟩
  choose p n σ r hp hn he hr hi ho using route
  let terminal (a : P) := p (leaf a) ⟨a, rfl⟩
  have ht x (t : T x) : terminal t.val = p x t := by
    rcases t with ⟨a, rfl⟩
    rfl
  have hq x (q : Q x) : terminal (point q.val.1.val q.val.2) = p x (src x q) := ht x (src x q)
  refine ⟨⟨agree, slot, terminal, n, σ, r, ?_, hn, he, ?_, ?_, ho⟩⟩
  · intro x i
    have h := hp x i
    simp_rw [← ht x] at h
    rw [sub_sum (fun t => leaf t = x) (fun t => if terminal t = i then l t else 0)] at h
    simpa only [push, Prod.mk.injEq, ite_and] using h
  · intro x q
    rw [hq]
    exact hr x q
  · intro x
    simpa only [hq] using hi x

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-! # Placing bases and their adaptive leaves on the common host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open Classical Finset

variable {V : Type} {h : ℕ}

def baseSite (base : V → ℕ) (hb : ∀ v, base v ≤ h) (z : Σ v, Cell (base v)) : Site V h :=
  (z.1, ⟨⟨base z.1, Nat.lt_succ_of_le (hb z.1)⟩, z.2⟩)

theorem baseSite_injective (base : V → ℕ) (hb : ∀ v, base v ≤ h) :
    Function.Injective (baseSite base hb) := by
  rintro ⟨v, x⟩ ⟨w, y⟩ he
  have hv : v = w := congrArg Prod.fst he
  subst w
  have : x = y := by simpa [baseSite] using he
  subst y
  rfl

abbrev Link {A : Type} (base : V → ℕ) (ends : A → Bool → V) :=
  Σ c, Cell (contactDepth base ends c)

abbrev outLeaf {A : Type} (base : V → ℕ) (ends : A → Bool → V) (hb : ∀ v, base v ≤ h)
    (z : Link base ends) (t : Bool) := baseSite base hb (contactEnd base ends z t)

abbrev Slots {A : Type} (base : V → ℕ) (ends : A → Bool → V) (hb : ∀ v, base v ≤ h)
    (capacity : A → ℝ) (Y : ℕ) := Port (outLeaf base ends hb) (fun z => capacity z.1) Y

def prefixSite (base : V → ℕ) (hb : ∀ v, base v ≤ h)
    (π : Equiv.Perm (Cell h)) (x : V × Cell h) : Σ v, Cell (base v) :=
  ⟨x.1, ancestor (hb x.1) (π x.2)⟩

variable (M : V → (i : ℕ) → Cell i → Prop) (π : Equiv.Perm (Cell h))

def leafSite (x : V × Cell h) : Site V h :=
  (x.1, ⟨⟨leafDepth (M x.1) (π x.2), Nat.lt_succ_of_le (leafDepth_le _ _)⟩,
    ancestor (leafDepth_le (M x.1) (π x.2)) (π x.2)⟩)

theorem leafSite_contains (x : V × Cell h) : (leafSite M π x).contains (π x.2) := rfl

private theorem site_ext (p q : Site V h) (hv : p.1 = q.1)
    (hc : (⟨p.depth, p.2.2⟩ : Σ i, Cell i) = ⟨q.depth, q.2.2⟩) : p = q := by
  obtain ⟨u, ⟨⟨i, hi⟩, x⟩⟩ := p
  obtain ⟨v, ⟨⟨j, hj⟩, y⟩⟩ := q
  cases hv
  cases hc
  rfl

theorem leafSite_prefix (base : V → ℕ) (hb : ∀ v, base v ≤ h) (p : V × Cell h)
    (hl : Leaf (M p.1) (base p.1) (ancestor (hb p.1) (π p.2))) :
    leafSite M π p = baseSite base hb (prefixSite base hb π p) := by
  exact site_ext _ _ rfl ((leafAt_eq_iff (M p.1) _ _ hl).mpr rfl)

/-- Slots in the common host that are not used in this group have zero load. -/
theorem leafSite_mass [Fintype V] (l : V → Cell h → ℝ)
    (hm : ∀ v x, leafAt (M v) (π x) ∈ leaves (M v) h)
    (hl : ∀ v c, c ∈ leaves (M v) h →
      (∑ x, if leafAt (M v) (π x) = c then l v x else 0) ≤ 2) (p : Site V h) :
    push (leafSite M π) (Function.uncurry l) p ≤ 2 := by
  let c : Σ i, Cell i := ⟨p.depth, p.2.2⟩
  have he x : leafSite M π (p.1, x) = p ↔ leafAt (M p.1) (π x) = c := by
    refine ⟨fun e => ?_, fun h => site_ext _ _ rfl h⟩
    exact congrArg (fun q : Site V h => (⟨q.depth, q.2.2⟩ : Σ i, Cell i)) e
  unfold push
  rw [Fintype.sum_prod_type, sum_eq_single p.1]
  · simp only [he, Function.uncurry_apply_pair]
    by_cases hc : c ∈ leaves (M p.1) h
    · exact hl p.1 c hc
    · have hn x : leafAt (M p.1) (π x) ≠ c := fun eq => hc (eq ▸ hm _ x)
      simp [hn]
  · intro v _ hv
    have hn x : leafSite M π (v, x) ≠ p := fun eq => hv (congrArg Prod.fst eq)
    simp [hn]
  · simp

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Uniform reservations across groups

Choose output terminal numbers using only the relative contact address.
At any given absolute base the relative slot map is injective, even
though all groups share the same terminal numbers.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V A : Type} {h Y : ℕ} {base : V → ℕ} {ends : A → Bool → V}
  {hb : ∀ v, base v ≤ h} {cap : A → ℝ}

theorem drop_contact (a : ℕ) (hb : ∀ v, base v ≤ h) (z : Link base ends) (t : Bool) :
    Site.drop a (outLeaf base ends hb z t) =
      outLeaf (relBase a base) ends (relHi a hb) (dropContact a z) t := rfl

/-- Local slot numbers are preserved under removal of the group prefix. -/
def dropSlot (a : ℕ) (lo : ∀ v, a ≤ base v) (x : Site V h) :
    Slots base ends hb cap Y x ↪ Slots (relBase a base) ends (relHi a hb) cap Y (x.drop a) where
  toFun p := ⟨⟨(dropContact a p.1.val.1, p.1.val.2),
    (drop_contact a hb _ _).symm.trans (congrArg (Site.drop a) p.1.property)⟩, p.2⟩
  inj' := by
    rintro ⟨⟨⟨e, t⟩, he⟩, i⟩ ⟨⟨⟨f, s⟩, hf⟩, j⟩ eq
    obtain ⟨hz, hij⟩ := Sigma.mk.inj eq
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (congrArg Subtype.val hz)
    have : e = f := dropContact_inj a lo t hr (baseSite_injective _ _ (he.trans hf.symm))
    subst f
    cases eq_of_heq hij
    rfl

def liftSlots (a : ℕ) (lo : ∀ v, a ≤ base v)
    (o : ∀ x, Slots (relBase a base) ends (relHi a hb) cap Y x ↪ Fin Y)
    (x : Site V h) : Slots base ends hb cap Y x ↪ Fin Y :=
  (dropSlot a lo x).trans (o (x.drop a))

private def toBaseContact (v : V) (z : Cell (base v)) :
    Slots base ends hb cap Y (baseSite base hb ⟨v, z⟩) ↪
      Σ e : BaseContact base ends v z, Fin ⌈cap e.val.1 * Y / 8⌉₊ where
  toFun p := ⟨⟨⟨p.1.val.1.1, p.1.val.2, p.1.val.1.2⟩, baseSite_injective _ _ p.1.property⟩, p.2⟩
  inj' := by
    rintro ⟨⟨⟨⟨c, b⟩, t⟩, he⟩, i⟩ ⟨⟨⟨⟨d, w⟩, s⟩, hf⟩, j⟩ eq
    obtain ⟨hz, hij⟩ := Sigma.mk.inj eq
    obtain ⟨rfl, hts⟩ := Sigma.mk.inj (congrArg Subtype.val hz)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hts)
    cases eq_of_heq hij
    rfl

variable [Fintype A] (base : V → ℕ) (ends : A → Bool → V) (hb : ∀ v, base v ≤ h)
  (s : ℕ) (D : ℝ) (hD : 0 < D) (y : A → ℝ) (hy : ∀ c, 0 ≤ y c)
  (gap : ∀ c t, contactDepth base ends c ≤ base (ends c t) + s)
  (degree : ∀ v, (∑ c, ∑ t : Bool, if ends c t = v then (1 : ℝ) else 0) ≤ D)
  (mass : ∀ v, (∑ c, ∑ t : Bool, if ends c t = v then y c else 0) ≤ (2 : ℝ) ^ (base v))
  (enough : 4 * (D * (2 : ℝ) ^ s) ≤ Y)

include hD hy gap degree mass enough

theorem slots_exist (x : Site V h) :
    let capacity := fun c => y c / (2 : ℝ) ^ (contactDepth base ends c) + 1 / (D * (2 : ℝ) ^ s)
    Nonempty (Slots base ends hb capacity Y x ↪ Fin Y) := by
  intro capacity
  by_cases h : ∃ z, baseSite base hb z = x
  · obtain ⟨⟨v, z⟩, rfl⟩ := h
    obtain ⟨f⟩ := reserve_base base ends v z s D hD y hy (fun c t e => e ▸ gap c t)
      (degree v) (mass v) enough
    exact ⟨(toBaseContact v z).trans f⟩
  · have : IsEmpty (Slots base ends hb capacity Y x) := ⟨fun p => h ⟨_, p.1.property⟩⟩
    exact ⟨⟨isEmptyElim, isEmptyElim⟩⟩

theorem relative_slots (a : ℕ) (lo : ∀ v, a ≤ base v) (x : Site V (h - a)) :
    let capacity := fun c => y c / (2 : ℝ) ^ (contactDepth base ends c) + 1 / (D * (2 : ℝ) ^ s)
    Nonempty (Slots (relBase a base) ends (relHi a hb) capacity Y x ↪ Fin Y) := by
  intro capacity
  let m := fun c => y c / (2 : ℝ) ^ a
  have hg c t : contactDepth (relBase a base) ends c ≤ relBase a base (ends c t) + s := by
    rw [relDepth, relBase]
    have := gap c t
    omega
  have hm v : (∑ c, ∑ t : Bool, if ends c t = v then m c else 0) ≤
      (2 : ℝ) ^ (relBase a base v) := by
    have hx := div_le_div_of_nonneg_right (mass v) (show 0 ≤ (2 : ℝ) ^ a by positivity)
    simpa only [m, zero_mul, relBase, pow_sub₀ (2 : ℝ) (by norm_num) (lo v), div_eq_mul_inv,
      sum_mul, ite_mul] using hx
  have eqn : capacity = fun c =>
      m c / (2 : ℝ) ^ (contactDepth (relBase a base) ends c) + 1 / (D * (2 : ℝ) ^ s) := by
    funext c
    have hc := (lo _).trans (le_contactDepth base ends c false)
    unfold capacity m
    rw [div_div, ← pow_add, relDepth, Nat.add_sub_of_le hc]
  rw [eqn]
  exact slots_exist (relBase a base) ends (relHi a hb) s D hD m (fun c => div_nonneg (hy c)
    (by positivity)) hg degree hm enough x

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Shared direct links on the reset host

An output terminal used by a good contact has a unique peer. The
involution depends only on the reservations, and pairs the same
relative terminals in all groups when the reservations are lifted.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open scoped Classical

variable {P U X W : Type} {outLeaf : W → Bool → X} {cap : W → ℝ} {Y w : ℕ}
  (out : ∀ x, Port outLeaf cap Y x ↪ Fin Y)

private abbrev Socket (cap : W → ℝ) (Y : ℕ) := (Σ c, Fin ⌈cap c * Y / 8⌉₊) × Bool

private def socket {x : X} (p : Port outLeaf cap Y x) : Socket cap Y :=
  (⟨p.1.val.1, p.2⟩, p.1.val.2)

private def attach (p : Socket cap Y) : X × Fin Y :=
  (outLeaf p.1.1 p.2, out _ ⟨⟨(p.1.1, p.2), rfl⟩, p.1.2⟩)

private theorem attach_socket {x : X} (p : Port outLeaf cap Y x) :
    attach out (socket p) = (x, out x p) := by
  rcases p with ⟨⟨⟨c, t⟩, rfl⟩, i⟩
  rfl

private theorem attach_inj : Function.Injective (attach out) := by
  have key {x y : X} (p : Port outLeaf cap Y x) (q : Port outLeaf cap Y y)
      (h : (x, out x p) = (y, out y q)) : socket p = socket q := by
    obtain ⟨rfl, he⟩ := Prod.mk.inj h
    rw [(out x).injective he]
  intro p q h
  exact key _ _ h

/-- This involution fixes unused terminals. -/
def peer (z : X × Fin Y) : X × Fin Y :=
  if h : ∃ p, attach out p = z then attach out (h.choose.1, !h.choose.2) else z

private theorem peer_attach (p : Socket cap Y) :
    peer out (attach out p) = attach out (p.1, !p.2) := by
  have h : ∃ q, attach out q = attach out p := ⟨p, rfl⟩
  rw [peer, dite_eq_left h, attach_inj out h.choose_spec]

theorem peer_involutive : Function.Involutive (peer out) := by
  intro z
  by_cases h : ∃ p, attach out p = z
  · obtain ⟨p, rfl⟩ := h
    rw [peer_attach, peer_attach, Bool.not_not]
  · have he : peer out z = z := dite_eq_right h
    rw [he, he]

namespace Delivery
variable [Fintype P] {leaf : P → X} {point : U → Bool → P} {good : U → Prop}
  {edge : U → W} {out} {l : P → ℝ} {u : ℝ}
  (d : Delivery leaf point good edge outLeaf cap Y w out l u)

def plug (q : {i // good i}) (t : Bool) : X × Fin Y :=
  (leaf (point q.val t), out _ (portOf leaf point good edge outLeaf cap Y d.agree d.slot
    ⟨(q, t), rfl⟩))

private theorem plug_eq (q : {i // good i}) (t : Bool) :
    d.plug q t = attach out (⟨edge q.val, d.slot q⟩, t) :=
  (attach_socket out (portOf leaf point good edge outLeaf cap Y d.agree d.slot
    ⟨(q, t), rfl⟩)).symm

theorem peer_link (q : {i // good i}) (t : Bool) :
    peer out (d.plug q t) = d.plug q (!t) := by rw [plug_eq, peer_attach, plug_eq]

end Delivery

variable {V A : Type} {h a : ℕ} {base : V → ℕ} {ends : A → Bool → V}
  {hb : ∀ v, base v ≤ h} {capacity : A → ℝ} {lo : ∀ v, a ≤ base v}
  {o : ∀ x, Slots (relBase a base) ends (relHi a hb) capacity Y x ↪ Fin Y}
  [Fintype P] {leaf : P → Site V h} {point : U → Bool → P} {good : U → Prop}
  {edge : U → Link base ends} {l : P → ℝ} {u : ℝ}

theorem Delivery.peer_relative
    (d : Delivery leaf point good edge (Packing.outLeaf base ends hb) (fun z => capacity z.1)
      Y w (liftSlots a lo o) l u) (q : {i // good i}) (t : Bool) :
    peer o (Prod.map (Site.drop a) id (d.plug q t)) =
      Prod.map (Site.drop a) id (d.plug q (!t)) := by
  have he (t : Bool) : Prod.map (Site.drop a) id (d.plug q t) =
      attach o (⟨dropContact a (edge q.val), d.slot q⟩, t) := by
    let p := portOf leaf point good edge _ (fun z => capacity z.1) Y d.agree d.slot ⟨(q, t), rfl⟩
    exact (attach_socket o (dropSlot a lo _ p)).symm
  rw [he, peer_attach, he]

end OAI.LinearAlgebra.MatrixExponent.Packing
end
