import OAI.LinearAlgebra.MatrixExponent.Packing.BadBases
import OAI.LinearAlgebra.MatrixExponent.Packing.Reservations
import OAI.LinearAlgebra.MatrixExponent.Packing.Delivery
import OAI.LinearAlgebra.MatrixExponent.Packing.Suffix

/-!
# Selecting bases and a common mixer

The total exceptional load can be made arbitrarily small. The length
parameter `k` is fixed before the group size, graph and loads. The
delay bound `s` is only imposed on core contacts.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open Finset
open scoped Classical

/-- Quantitative bad-base estimate with loads normalized by `FB`.
The maximum base length is `2^(h-a)` and the minimum is `F = 2^k`. -/
theorem reset_bases (j s : ℕ) (D ε : ℝ) (hD : 0 < D) (hε : 0 < ε) :
    ∃ k ≥ j, ∀ (V A : Type) [Fintype V] [Fintype A] (h a : ℕ), a + k ≤ h →
    ∀ (E : V → Finset V) (d : V → V → ℕ) (ends : A → Bool → V)
      (l : V → Cell h → ℝ) (y : A → Cell h → ℝ),
    (∀ u, ∑ v, (if u ∈ E v then 1 / (2 : ℝ) ^ (d v u) else 0) ≤ 1 / 2) →
    (∀ c t, ends c (!t) ∈ E (ends c t) ∧ 8 * d (ends c t) (ends c (!t)) ≤ s) →
    (∀ v, (∑ c, ∑ t : Bool, if ends c t = v then (1 : ℝ) else 0) ≤ D) →
    (∀ v x, 0 ≤ l v x ∧ l v x ≤ 1 / (2 : ℝ) ^ k) →
    (∀ c x, 0 ≤ y c x ∧ y c x ≤ 1 / (2 : ℝ) ^ k) →
    (∀ v, (∑ c, ∑ t : Bool, if ends c t = v then ∑ x, y c x else 0) ≤ ∑ x, l v x) →
    let g := D * (2 : ℝ) ^ s
    ∃ (base : V → ℕ) (f : Cell h ≃ₗ[ZMod 2] Cell h),
      (∀ v, a ≤ base v ∧ base v ≤ h - k ∧ (∑ x, l v x) ≤ (2 : ℝ) ^ (base v)) ∧
      (∀ v u, u ∈ E v → base u ≤ base v + 8 * d v u) ∧
      (∑ v, (2 : ℝ) ^ (base v)) ≤ 2 * Fintype.card V * (2 : ℝ) ^ a + 4 * (∑ v, ∑ x, l v x) ∧
      (∀ v (z : Cell (base v)),
        (∑ c, ∑ t, ∑ w, if contactEnd base ends ⟨c, w⟩ t = ⟨v, z⟩ then (1 : ℝ) else 0) ≤ g ∧
        (∑ c, ∑ t, ∑ w, if contactEnd base ends ⟨c, w⟩ t = ⟨v, z⟩
          then mean (y c) (contactDepth base ends c) + 1 / g else 0) ≤ 2) ∧
      badLoad E d base (contactDepth base ends) (contactEnd base ends) l y g f.toEquiv ≤
        ε * (∑ v, ∑ x, l v x) := by
  obtain ⟨k, hk, small⟩ := small_resetWeight (D * (2 : ℝ) ^ s) ε hε j
  refine ⟨k, hk, ?_⟩
  intro V A _ _ h a ha E d ends l y budget hadj degree hl hy incident g
  have hg : 0 < g := by unfold g; positivity
  have mass v : 0 ≤ ∑ x, l v x := sum_nonneg fun x _ => (hl v x).1
  have lim v : (∑ x, l v x) ≤ (2 : ℝ) ^ (h - k) := calc
    _ ≤ ∑ _x : Cell h, 1 / (2 : ℝ) ^ k := sum_le_sum (fun x _ => (hl v x).2)
    _ = _ := by
      simp only [sum_const, card_univ, card_cell, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
        mul_one_div, div_eq_iff (by positivity : (2 : ℝ) ^ k ≠ 0), ← pow_add,
        Nat.sub_add_cancel (by omega : k ≤ h)]
  obtain ⟨base, hb, drop, count⟩ := choose_bases E d budget a (h - k) (by omega)
    (fun v => ∑ x, l v x) (fun v => ⟨mass v, lim v⟩)
  have hq c : contactDepth base ends c ≤ h := by
    exact max_le ((hb _).2.1.trans (Nat.sub_le _ _)) ((hb _).2.1.trans (Nat.sub_le _ _))
  obtain ⟨f, hf⟩ := bad_bases E d base (contactDepth base ends) (contactEnd base ends) l y g
    drop budget hl hy (fun v => (hb v).2.2) hq hg
  refine ⟨base, f, hb, drop, count, ?_, hf.trans ?_⟩
  · intro v z
    have gap c t (ht : ends c t = v) : contactDepth base ends c ≤ base v + s := by
      subst v
      obtain ⟨he, hs⟩ := hadj c t
      have hdrop := (drop _ _ he).trans (Nat.add_le_add_left hs _)
      cases t <;> simp_all only [Bool.not_false, Bool.not_true, contactDepth] <;> omega
    exact ⟨reservation_count base ends v z s D gap (degree v),
      reservation_bound base ends (fun c => ∑ x, y c x) v z s D hD gap (degree v)
        ((incident v).trans (hb v).2.2)⟩
  · have total : (∑ c, ∑ x, y c x) ≤ ∑ v, ∑ x, l v x := by
      apply le_trans _ (sum_le_sum (s := univ) fun v _ => incident v)
      rw [sum_comm (s := (univ : Finset V))]
      apply sum_le_sum
      intro c _
      rw [sum_comm (s := (univ : Finset V))]
      simp only [sum_ite_eq, mem_univ, ite_true]
      exact single_le_sum (fun _ _ => sum_nonneg fun x _ => (hy c x).1) (mem_univ false)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right small (sum_nonneg fun v _ => mass v))
    rw [add_mul]
    exact add_le_add_right (mul_le_mul_of_nonneg_left total (by positivity)) _

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Subdivision of reset bases

Force all cells above each base to split. Below it, split only if the
load is above twice the normalized capacity or a neighbor forces the split.
Good bases survive unchanged.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open Finset
open scoped Classical

variable {V : Type} {h k : ℕ}
variable (E : V → Finset V) (d : V → V → ℕ) (base : V → ℕ)
variable (l : V → Cell h → ℝ) (π : Equiv.Perm (Cell h))

def ResetSplit (v : V) (i : ℕ) (z : Cell i) : Prop :=
  i < base v ∨ Spread E (fun v u => 8 * d v u) (fun v i z => 2 < load (l v) π i z) v i z

theorem reset_leaves (hk : k ≤ h) (hb : ∀ v, base v ≤ h - k)
    (drop : ∀ v u, u ∈ E v → base u ≤ base v + 8 * d v u)
    (hl : ∀ v x, l v x ≤ 1 / (2 : ℝ) ^ k) :
    let M := ResetSplit E d base l π
    (∀ v x, leafAt (M v) (π x) ∈ leaves (M v) h) ∧
    (∀ v c, c ∈ leaves (M v) h →
      base v ≤ c.1 ∧ c.1 ≤ h - k ∧ (∃ hi : c.1 ≤ h,
        ∀ x, leafAt (M v) (π x) = c ↔ ancestor hi (π x) = c.2) ∧
        2 ^ k ≤ (univ.filter fun x => leafAt (M v) (π x) = c).card ∧
        (∑ x, if leafAt (M v) (π x) = c then l v x else 0) ≤ 2) ∧
    (∀ v u, u ∈ E v → ∀ x : Cell h, leafDepth (M u) x ≤ leafDepth (M v) x + 16 * d v u) := by
  intro M
  have high v i z (hm : 2 < load (l v) π i z) : i < h - k := by
    unfold load at hm
    split_ifs at hm with hi
    · exact heavy.depth hk (hl v) ⟨hi, lt_trans (by norm_num) hm⟩
    · norm_num at hm
  have small v i z (hm : M v i z) : i < h - k := by
    rcases hm with hh | hh
    · exact hh.trans_le (hb v)
    · exact hh.depth high
  have stop v x : ¬M v h x := fun hc => (Nat.sub_le h k).not_gt (small _ _ _ hc)
  refine ⟨fun v x => leafAt_mem _ _ (stop v _), ?_, ?_⟩
  · rintro v ⟨i, z⟩ hc
    obtain ⟨hi, reached, unmarked⟩ := (mem_leaves (M v) _).mp hc
    have hj : i ≤ h - k := by
      by_contra! bad
      exact lt_irrefl _ (small _ _ _ (reached _ bad))
    have fiber (x : Cell h) : leafAt (M v) (π x) = ⟨i, z⟩ ↔ ancestor hi (π x) = z :=
      leafAt_eq_iff _ _ hi ⟨reached, unmarked⟩
    refine ⟨le_of_not_gt fun hh => unmarked (.inl hh), hj, ⟨hi, fiber⟩, ?_, ?_⟩
    · rw [card_leafAt _ _ hc]
      exact Nat.pow_le_pow_right (by decide) (by omega : k ≤ h - i)
    · have hload : load (l v) π i z ≤ 2 :=
        le_of_not_gt fun hh => unmarked (.inr (.start hh))
      simpa only [load, dite_eq_left hi, fiber] using hload
  · intro v u hu x
    rw [show 16 * d v u = 2 * (8 * d v u) by omega]
    apply leafDepth_le_add
    intro i _ c hc
    rcases hc with hh | hh
    · left
      have := drop v u hu
      omega
    · exact .inr (.move (d := fun v u => 8 * d v u) (M := fun v i z => 2 < load (l v) π i z) hu c hh)

theorem good_leaf {A : Type} (q : A → ℕ) (endpt : (Σ c, Cell (q c)) → Bool → Σ v, Cell (base v))
    (y : A → Cell h → ℝ) (g : ℝ) (v : V) (z : Cell (base v))
    (good : ¬BadBase E d base q endpt l y g π ⟨v, z⟩) :
    Leaf (ResetSplit E d base l π v) (base v) z := by
  refine ⟨fun _ hi => .inl hi, ?_⟩
  rintro (hh | hh)
  · exact lt_irrefl _ hh
  · exact good (.inl hh)

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Packing one dyadic group

Use the two host degree bounds separately. Only the core degree enters
the bound on the number of destinations of one source part.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V : Type} [Fintype V] {h k : ℕ}

/-- At depth `i`, at most `2 ^ s` destination parts meet a given
source part if they all have depth at most `i + s`. -/
theorem neighbors_le (π : Cell h → Cell h) (a b : Cell h → Σ i, Cell i)
    (c : Σ i, Cell i) (hc : c.1 ≤ h)
    (ha : ∀ x, a x = c → ancestor hc (π x) = c.2)
    (hb : ∀ x, ∃ hj : (b x).1 ≤ h, ∀ y, b y = b x ↔ ancestor hj (π y) = (b x).2)
    (s : ℕ) (hd : ∀ x, a x = c → (b x).1 ≤ c.1 + s) :
    ((univ.filter fun x => a x = c).image b).card ≤ 2 ^ s := by
  let T := (univ.filter fun x => a x = c).image b
  have rep (z : T) : ∃ x, a x = c ∧ b x = z.val := by
    simpa only [T, mem_image, mem_filter, mem_univ, true_and] using z.property
  choose p hp hq using rep
  let code (z : T) : Cell s := fun j =>
    if hj : c.1 + j.val < h then π (p z) ⟨c.1 + j.val, hj⟩ else 0
  have inj : Function.Injective code := by
    intro z w he
    obtain ⟨hj, hf⟩ := hb (p w)
    have hle := hd _ (hp w)
    apply Subtype.ext
    rw [← hq z, ← hq w, hf, ← (hf _).mp rfl]
    funext j
    by_cases hi : j.val < c.1
    · exact congrFun ((ha _ (hp z)).trans (ha _ (hp w)).symm) ⟨j.val, hi⟩
    · have hh : c.1 + (j.val - c.1) = j.val := by omega
      have e := congrFun he ⟨j.val - c.1, by omega⟩
      simpa [code, hh, j.isLt.trans_le hj, ancestor, Fin.castLE] using e
  simpa only [Fintype.card_coe, card_cell] using Fintype.card_le_of_injective code inj

private theorem weight_quarter (s : Finset V) (D m : ℕ) (hD : 0 < D)
    (hs : s.card ≤ D) (hm : 2 ≤ m) :
    (∑ v, if v ∈ s then 1 / (2 : ℝ) ^ (m * Nat.clog 2 (2 * D)) else 0) ≤ 1 / 4 := by
  let n := Nat.clog 2 (2 * D)
  have hn : 1 ≤ n := Nat.clog_pos (by decide) (by omega)
  have hp : 4 * D ≤ 2 ^ (m * n) := calc
    4 * D = (2 * D) * 2 := by omega
    _ ≤ (2 ^ n) * 2 := Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)
    _ ≤ 2 ^ (m * n) := Nat.pow_le_pow_right (by decide : 0 < 2)
      ((show n + 1 ≤ 2 * n by omega).trans (Nat.mul_le_mul_right _ hm))
  have hc : (s.card : ℝ) * 4 ≤ (2 : ℝ) ^ (m * n) := by
    exact_mod_cast (show s.card * 4 ≤ 2 ^ (m * n) by omega)
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, mul_one_div,
    div_le_div_iff₀ (by positivity) (by norm_num), one_mul]
  exact hc

/-- Each of the core and tether classes consumes at most a quarter of
the incoming weight budget. -/
theorem edge_weight_sum (E C : V → Finset V) (Δ D m : ℕ) (hΔ : 0 < Δ) (hD : 0 < D)
    (eSym : ∀ v u, u ∈ E v → v ∈ E u) (cSym : ∀ v u, u ∈ C v → v ∈ C u)
    (eDeg : ∀ v, (E v).card ≤ D) (cDeg : ∀ v, (C v).card ≤ Δ) (hm : 2 ≤ m) (u : V) :
    (∑ v, if u ∈ E v then
      1 / (2 : ℝ) ^ (m * Nat.clog 2 (2 * if u ∈ C v then Δ else D)) else 0) ≤ 1 / 2 := by
  let w (n : ℕ) := 1 / (2 : ℝ) ^ (m * Nat.clog 2 (2 * n))
  have hw (n : ℕ) : 0 ≤ w n := by unfold w; positivity
  calc
    _ ≤ ∑ v, ((if v ∈ C u then w Δ else 0) + (if v ∈ E u then w D else 0)) := by
      apply sum_le_sum
      intro v _
      by_cases he : u ∈ E v
      · by_cases hc : u ∈ C v
        · simp [he, hc, cSym _ _ hc, eSym _ _ he, w]
        · have hnc : v ∉ C u := fun hx => hc (cSym _ _ hx)
          simp [he, hc, hnc, eSym _ _ he, w]
      · rw [ite_eq_right he]
        exact add_nonneg (ite_nonneg (hw _) le_rfl) (ite_nonneg (hw _) le_rfl)
    _ ≤ 1 / 4 + 1 / 4 := by
      rw [sum_add_distrib]
      exact add_le_add (weight_quarter _ _ _ hΔ (cDeg u) hm)
        (weight_quarter _ _ _ hD (eDeg u) hm)
    _ = _ := by norm_num

def delay (C : V → Finset V) (Δ D : ℕ) (v u : V) :=
  32 * Nat.clog 2 (2 * if u ∈ C v then Δ else D)

def relative (k : ℕ) (B : ℝ) (l : V → Cell h → ℝ) (v : V) (x : Cell h) :=
  l v x / ((2 : ℝ) ^ k * B)

/-- Use any minimizer of the total propagated split count. -/
def groupBy (E C : V → Finset V) (Δ D : ℕ) (hΔ : 0 < Δ) (hD : 0 < D)
    (eSym : ∀ v u, u ∈ E v → v ∈ E u) (cSym : ∀ v u, u ∈ C v → v ∈ C u)
    (sub : ∀ v, C v ⊆ E v) (eDeg : ∀ v, (E v).card ≤ D) (cDeg : ∀ v, (C v).card ≤ Δ)
    (hk : 1 ≤ k) (hkh : k ≤ h) (B : ℝ) (hB : 0 < B)
    (l : V → Cell h → ℝ) (hl : ∀ v x, 0 ≤ l v x ∧ l v x ≤ B)
    (pick : Fin (2 ^ h)) (opt : best E (delay C Δ D) (relative k B l) pick) :
    Grouping E C Δ D k B l := by
  let d (v u : V) := 32 * Nat.clog 2 (2 * if u ∈ C v then Δ else D)
  have hd (v u : V) (_ : u ∈ E v) : 0 < d v u := by
    apply Nat.mul_pos (by decide : 0 < 32)
    apply Nat.clog_pos (by decide)
    split_ifs <;> omega
  let b := (2 : ℝ) ^ k * B
  have hb : 0 < b := mul_pos (by positivity) hB
  have hn v x : 0 ≤ l v x / b ∧ l v x / b ≤ 1 / (2 : ℝ) ^ k := by
    refine ⟨div_nonneg (hl v x).1 hb.le, (div_le_iff₀ hb).mpr ?_⟩
    simpa [b, ← mul_assoc] using (hl v x).2
  let π := menu h pick
  let M := marks E d (fun v x => l v x / b) pick
  let parts v := leaves (M v) h
  let label v x := leafAt (M v) (π x)
  have ok := balanced_partition E d hd
    (edge_weight_sum E C Δ D 32 hΔ hD eSym cSym eDeg cDeg (by decide)) hk hkh _ hn pick opt
  have total := ok.1
  have mem := ok.2.1
  have part := ok.2.2.1
  have edge := ok.2.2.2
  have hedge v u (hu : u ∈ E v) x : (label u x).1 ≤ (label v x).1 +
      64 * Nat.clog 2 (2 * if u ∈ C v then Δ else D) := by
    simpa only [d, ← mul_assoc, Nat.reduceMul] using edge v u hu x
  refine ⟨π, parts, label, ?_, mem, ?_, hedge, ?_⟩
  · change (∑ v, ((parts v).card : ℝ)) ≤ _ at total
    simpa only [div_eq_mul_inv, ← sum_mul, mul_assoc, b] using total
  · intro v c hc
    obtain ⟨hdepth, pref, hsize, hload⟩ := part v c hc
    refine ⟨hdepth, pref, hsize, (div_le_one hb).mp ?_⟩
    change (∑ x, if label v x = c then l v x / b else 0) ≤ 1 at hload
    simpa only [div_eq_mul_inv, sum_mul, ite_mul, zero_mul] using hload
  · intro v c hc
    obtain ⟨hi, hp⟩ := (part v c hc).2.1
    calc
      _ ≤ ∑ _u ∈ C v, 2 ^ (64 * Nat.clog 2 (2 * Δ)) := by
        refine sum_le_sum fun u hu => neighbors_le π _ _ c hi (fun x => (hp x).mp)
          (fun x => (part u _ (mem u x)).2.1) _ ?_
        intro x hx
        change label v x = c at hx
        simpa only [ite_eq_left hu, hx] using hedge v u (sub v hu) x
      _ ≤ _ := by
        rw [sum_const, Nat.nsmul_eq_mul]
        exact Nat.mul_le_mul_right _ (cDeg v)

theorem pack_group (E C : V → Finset V) (Δ D : ℕ) (hΔ : 0 < Δ) (hD : 0 < D)
    (eSym : ∀ v u, u ∈ E v → v ∈ E u) (cSym : ∀ v u, u ∈ C v → v ∈ C u)
    (sub : ∀ v, C v ⊆ E v) (eDeg : ∀ v, (E v).card ≤ D) (cDeg : ∀ v, (C v).card ≤ Δ)
    (hk : 1 ≤ k) (hkh : k ≤ h) (B : ℝ) (hB : 0 < B)
    (l : V → Cell h → ℝ) (hl : ∀ v x, 0 ≤ l v x ∧ l v x ≤ B) :
    Nonempty (Grouping E C Δ D k B l) := by
  obtain ⟨p, hp⟩ := best_exists E (delay C Δ D) (relative k B l)
  exact ⟨groupBy E C Δ D hΔ hD eSym cSym sub eDeg cDeg hk hkh B hB l hl p hp⟩

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Distributing indivisible core wire units

A unit belongs to one block and one oriented contact. Both counts of the
same units are needed: load at a contact for reserving links and load
at the endpoint occurrences for packing whole tensors.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open Finset
open scoped Classical

variable {V A U : Type} {h : ℕ}

structure Demands (V A U : Type) (h : ℕ) where
  ends : A → Bool → V
  contact : U → A
  ix : U → Cell h

namespace Demands

variable (T : Demands V A U h)

def point (i : U) (t : Bool) := (T.ends (T.contact i) t, T.ix i)

def edge (i : U) := (T.contact i, T.ix i)

variable [Fintype U]

def amounts (u : ℝ) (c : A) (x : Cell h) := push T.edge (fun _ => u) (c, x)

def incident (u : ℝ) (v : V) (x : Cell h) :=
  push (Function.uncurry T.point) (fun _ => u) (v, x)

theorem incident_eq [Fintype A] (u : ℝ) (v : V) (x : Cell h) :
    T.incident u v x = ∑ c, ∑ t, if T.ends c t = v then T.amounts u c x else 0 := by
  unfold incident push
  rw [Fintype.sum_prod_type, sum_comm, sum_comm (s := (univ : Finset A))]
  apply sum_congr rfl
  intro t _
  have he := test_push T.edge (fun _ => u) (fun q => T.ends q.1 t = v ∧ q.2 = x)
  rw [Fintype.sum_prod_type] at he
  change (∑ c, ∑ z, if T.ends c t = v ∧ z = x then T.amounts u c z else 0) = _ at he
  simp only [ite_and, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true] at he
  refine (sum_congr rfl ?_).trans he.symm
  intro i _
  simp only [Function.uncurry_apply_pair, point, edge, Prod.mk.injEq, ite_and]
  congr! 2

theorem amount_le [Fintype A] (u : ℝ) (hu : 0 ≤ u) (c : A) (t : Bool) (x : Cell h) :
    T.amounts u c x ≤ T.incident u (T.ends c t) x := by
  let f c' t' := if T.ends c' t' = T.ends c t then T.amounts u c' x else 0
  have hf c' t' : 0 ≤ f c' t' := by
    unfold f
    split_ifs
    · exact push_nonneg _ _ (fun _ => hu) _
    · exact le_rfl
  rw [incident_eq]
  change _ ≤ ∑ c', ∑ t', f c' t'
  calc
    _ = f c t := (ite_eq_left rfl).symm
    _ ≤ ∑ t', f c t' := single_le_sum (fun t' _ => hf c t') (mem_univ t)
    _ ≤ _ := single_le_sum (fun c' _ => sum_nonneg fun t' _ => hf c' t') (mem_univ c)

theorem sum_incident [Fintype A] (u : ℝ) (v : V) :
    (∑ c, ∑ t : Bool, if T.ends c t = v then ∑ x, T.amounts u c x else 0) =
    ∑ x, T.incident u v x := by
  simp_rw [incident_eq]
  rw [sum_comm (s := (univ : Finset (Cell h)))]
  apply sum_congr rfl
  intro c _
  rw [sum_comm (s := (univ : Finset (Cell h)))]
  simp only [sum_ite_irrel, sum_const_zero]

variable (base : V → ℕ) (hb : ∀ v, base v ≤ h) (π : Equiv.Perm (Cell h))

omit [Fintype U] in
include hb in
theorem contact_le (c : A) : contactDepth base T.ends c ≤ h := max_le (hb _) (hb _)

def link (i : U) : Link base T.ends :=
  prefixSite _ (T.contact_le base hb) π (T.edge i)

omit [Fintype U] in
theorem link_end (i : U) (t : Bool) :
    contactEnd base T.ends (T.link base hb π i) t = prefixSite base hb π (T.point i t) := rfl

theorem link_load [Fintype A] (u : ℝ) (z : Link base T.ends) :
    push (T.link base hb π) (fun _ => u) z =
      load (T.amounts u z.1) π (contactDepth base T.ends z.1) z.2 := by
  change push (prefixSite _ (T.contact_le base hb) π ∘ T.edge) _ _ = _
  rw [← push_comp]
  exact push_prefix _ (T.contact_le base hb) π (T.amounts u) z.1 z.2

end Demands
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# A reset schedule for individual wire units

Transfer the exceptional load bound to actual demands. A contact between
good bases fits its predetermined capacity. Assign each old occurrence
to a leaf, preserving both endpoints of every such contact.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V A U : Type} {h a k : ℕ} [Fintype V] [Fintype U]

structure Schedule (T : Demands V A U h) (E : V → Finset V) (d : V → V → ℕ)
    (a k : ℕ) (l : V → Cell h → ℝ) (u g ε : ℝ) where
  base : V → ℕ
  π : Cell h ≃ₗ[ZMod 2] Cell h
  lo : ∀ v, a ≤ base v
  hi : ∀ v, base v ≤ h - k
  mean : ∀ v, (∑ x, l v x) ≤ (2 : ℝ) ^ (base v)
  drop : ∀ v w, w ∈ E v → base w ≤ base v + 8 * d v w
  count : (∑ v, (2 : ℝ) ^ (base v)) ≤ 2 * Fintype.card V * (2 : ℝ) ^ a + 4 * (∑ v, ∑ x, l v x)
  bad : badLoad E d base (contactDepth base T.ends) (contactEnd base T.ends)
          l (T.amounts u) g π.toEquiv ≤ ε * (∑ v, ∑ x, l v x)
  sizes : ∀ v x, 0 ≤ l v x ∧ l v x ≤ 1 / (2 : ℝ) ^ k
  mass : ∀ v x, T.incident u v x ≤ l v x
  block : a + k ≤ h
  width : 0 < u
  margin : 0 < g

namespace Schedule

variable {T : Demands V A U h} {E : V → Finset V} {d : V → V → ℕ}
variable {l : V → Cell h → ℝ} {u g ε : ℝ} (Z : Schedule T E d a k l u g ε)

theorem depth (v : V) : Z.base v ≤ h := (Z.hi v).trans (Nat.sub_le _ _)

abbrev baseOf := prefixSite Z.base Z.depth Z.π.toEquiv
abbrev link := T.link Z.base Z.depth Z.π.toEquiv
abbrev mark := ResetSplit E d Z.base l Z.π.toEquiv
abbrev leaf := leafSite Z.mark Z.π.toEquiv
abbrev outlet := outLeaf Z.base T.ends Z.depth

def capacity (c : A) := Packing.mean (T.amounts u c) (contactDepth Z.base T.ends c) + 1 / g
def failed := BadBase E d Z.base (contactDepth Z.base T.ends) (contactEnd Z.base T.ends)
  l (T.amounts u) g Z.π.toEquiv
def good (i : U) := ∀ t : Bool, ¬Z.failed (Z.baseOf (T.point i t))

theorem capacity_pos (c : A) : 0 < Z.capacity c := by
  have hpos x : 0 ≤ T.amounts u c x := push_nonneg _ _ (fun _ => Z.width.le) _
  exact add_pos_of_nonneg_of_pos (div_nonneg (sum_nonneg fun x _ => hpos x) (by positivity))
    (one_div_pos.mpr Z.margin)

theorem routes (i : U) (hi : Z.good i) (t : Bool) :
    Z.leaf (T.point i t) = Z.outlet (Z.link i) t := by
  have hn := hi t
  have he := good_leaf E d Z.base l Z.π.toEquiv _ _ (T.amounts u) g _ _ hn
  exact leafSite_prefix _ _ _ _ _ he

theorem at_leaf (z : Site V h) : push Z.leaf (Function.uncurry l) z ≤ 2 := by
  obtain ⟨hm, hl, _⟩ := reset_leaves E d Z.base l Z.π.toEquiv (by have := Z.block; omega)
    Z.hi Z.drop (fun v x => (Z.sizes v x).2)
  exact leafSite_mass _ _ _ hm (fun v c h => (hl v c h).2.2.2.2) z

theorem at_link [Fintype A] (z : Link Z.base T.ends) :
    push Z.link (fun i => if Z.good i then u else 0) z ≤ Z.capacity z.1 := by
  by_cases hz : ∃ i, Z.link i = z ∧ Z.good i
  · obtain ⟨i, rfl, hi⟩ := hz
    refine (push_le_push _ (m := fun _ => u) (fun j => by split_ifs <;> first | rfl | exact Z.width.le) _).trans ?_
    rw [show push Z.link _ _ = _ from T.link_load Z.base Z.depth Z.π.toEquiv u (Z.link i)]
    exact le_of_not_gt fun over => hi false (.inr ⟨Z.link i, false, over, rfl⟩)
  · have he : push Z.link (fun i => if Z.good i then u else 0) z = 0 := by
      apply sum_eq_zero
      intro i _
      dsimp only
      split_ifs with h₁ h₂
      · exact (hz ⟨i, h₁, h₂⟩).elim
      · rfl
      · rfl
    exact he.trans_le (Z.capacity_pos _).le

/-- Charge each unit using an exceptional route to at least one failed endpoint. -/
theorem exceptional :
    (∑ i, if Z.good i then 0 else u) ≤ ε * (∑ v, ∑ x, l v x) := by
  let f := Z.baseOf ∘ Function.uncurry T.point
  have hv (z : Σ v, Cell (Z.base v)) : push f (fun _ => u) z ≤
      load (l z.1) Z.π.toEquiv (Z.base z.1) z.2 := by
    rw [show push f (fun _ => u) z = _ from (push_comp _ _ _ _).symm]
    refine (push_le_push _ (m := Function.uncurry l) (fun x => Z.mass x.1 x.2) _).trans_eq ?_
    exact push_prefix Z.base Z.depth Z.π.toEquiv l z.1 z.2
  calc
    _ ≤ ∑ q : U × Bool, if Z.failed (f q) then u else 0 := by
      rw [Fintype.sum_prod_type]
      apply sum_le_sum
      intro i _
      have hp t : 0 ≤ if Z.failed (f (i, t)) then u else 0 := by
        split_ifs <;> first | exact Z.width.le | rfl
      split_ifs with hi
      · exact sum_nonneg fun t _ => hp t
      · unfold good at hi
        push Not at hi
        obtain ⟨t, ht⟩ := hi
        have := single_le_sum (fun t _ => hp t) (mem_univ t)
        exact (ite_eq_left ht).symm.trans_le this
    _ ≤ badLoad E d Z.base _ _ l (T.amounts u) g Z.π.toEquiv := by
      rw [← test_push f (fun _ => u)]
      apply sum_le_sum
      intro z _
      change (if Z.failed z then _ else 0) ≤ if Z.failed z then _ else 0
      split_ifs <;> first | exact hv z | rfl
    _ ≤ _ := Z.bad

end Schedule
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Reset routing over all groups at once

Each old contact carries named units on specified blocks. Active terminals,
layers and the mixer are chosen using all blocks. The allowable links
between terminals use only the contact means and the relative addresses.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

namespace Schedule

variable {V A U : Type} [Fintype V] [Fintype U] {h a k : ℕ}
variable {T : Demands V A U h} {E : V → Finset V} {d : V → V → ℕ}
variable {l : V → Cell h → ℝ} {u g ε : ℝ} (Z : Schedule T E d a k l u g ε)

abbrev Plugs (Y : ℕ) :=
  ∀ x, Slots (relBase a Z.base) T.ends (relHi a Z.depth) Z.capacity Y x ↪ Fin Y

abbrev Dispatch {Y : ℕ} (o : Z.Plugs Y) (w : ℕ) :=
  Delivery Z.leaf T.point Z.good Z.link Z.outlet (fun z => Z.capacity z.1)
    Y w (liftSlots a Z.lo o) (Function.uncurry l) u

theorem dispatch [Fintype A] {Y w : ℕ} (o : Z.Plugs Y) (hY : 0 < Y) (hw : 0 < w)
    (space : Y ^ 2 * w ≤ 2 ^ k) (unit : u ≤ 1 / (2 : ℝ) ^ k) : Nonempty (Z.Dispatch o w) := by
  have hy : 1 ≤ (Y : ℝ) := by exact_mod_cast hY
  have hw' : 1 ≤ (w : ℝ) := by exact_mod_cast hw
  have space' : (Y : ℝ) ^ 2 * w ≤ (2 : ℝ) ^ k := by exact_mod_cast space
  have uy : (Y : ℝ) ≤ (2 : ℝ) ^ k := by
    apply le_trans _ space'
    nlinarith [mul_nonneg (sq_nonneg (Y : ℝ)) (sub_nonneg.mpr hw')]
  have overhead : (Y : ℝ) ^ 2 * w * u ≤ 1 := calc
    _ ≤ (2 : ℝ) ^ k * u := mul_le_mul_of_nonneg_right space' Z.width.le
    _ ≤ _ := by rw [mul_comm]; exact (le_div_iff₀ (by positivity)).mp unit
  apply deliver _ _ _ _ _ _ _ _ _ _ _ hY hw Z.width overhead Z.routes Z.at_leaf
  · rintro ⟨v, x⟩
    obtain ⟨hl, hh⟩ := Z.sizes v x
    exact ⟨hl, (mul_le_mul_of_nonneg_left uy hl).trans ((le_div_iff₀ (by positivity)).mp hh)⟩
  · exact fun p => Z.mass p.1 p.2
  · exact Z.at_link

end Schedule

/-- The only delay and degree assumptions on contacts are for the core.
Tether edges enter via the geometric budget, independent of their number. -/
theorem reset_schedule (Y w s : ℕ) (D ε : ℝ) (hY : 0 < Y) (hw : 0 < w)
    (hD : 0 < D) (hε : 0 < ε) (enough : 4 * (D * (2 : ℝ) ^ s) ≤ Y) :
    ∃ k, Y ^ 2 * w ≤ 2 ^ k ∧
    ∀ (V A U : Type) [Fintype V] [Fintype A] [Fintype U] (h a : ℕ), a + k ≤ h →
    ∀ (T : Demands V A U h) (E : V → Finset V) (d : V → V → ℕ) (l : V → Cell h → ℝ) (u : ℝ),
    (∀ t, ∑ v, (if t ∈ E v then 1 / (2 : ℝ) ^ (d v t) else 0) ≤ 1 / 2) →
    (∀ c t, T.ends c (!t) ∈ E (T.ends c t) ∧ 8 * d (T.ends c t) (T.ends c (!t)) ≤ s) →
    (∀ v, (∑ c, ∑ t : Bool, if T.ends c t = v then (1 : ℝ) else 0) ≤ D) →
    (∀ v x, 0 ≤ l v x ∧ l v x ≤ 1 / (2 : ℝ) ^ k) →
    0 < u → u ≤ 1 / (2 : ℝ) ^ k → (∀ v x, T.incident u v x ≤ l v x) →
    ∃ (Z : Schedule T E d a k l u (D * (2 : ℝ) ^ s) ε) (o : Z.Plugs Y),
      Nonempty (Z.Dispatch o w) := by
  obtain ⟨k, hk, hex⟩ := reset_bases (Y ^ 2 * w) s D ε hD hε
  have space : Y ^ 2 * w ≤ 2 ^ k := hk.trans Nat.lt_two_pow_self.le
  refine ⟨k, space, ?_⟩
  intro V A U _ _ _ h a ha T E d l u budget adj degree hl hu hu' inc
  have hy c x : 0 ≤ T.amounts u c x ∧ T.amounts u c x ≤ 1 / (2 : ℝ) ^ k :=
    ⟨push_nonneg _ _ (fun _ => hu.le) _,
      ((T.amount_le u hu.le c false x).trans (inc _ x)).trans (hl _ x).2⟩
  have hm v : (∑ c, ∑ t : Bool, if T.ends c t = v then ∑ x, T.amounts u c x else 0) ≤
      ∑ x, l v x := by
    rw [T.sum_incident]
    exact sum_le_sum (fun x _ => inc v x)
  obtain ⟨base, π, hb, drop, count, _, bad⟩ :=
    hex V A h a ha E d T.ends l (T.amounts u) budget adj degree hl hy hm
  let Z : Schedule T E d a k l u (D * (2 : ℝ) ^ s) ε :=
    ⟨base, π, fun v => (hb v).1, fun v => (hb v).2.1, fun v => (hb v).2.2, drop, count,
      bad, hl, inc, ha, hu, by positivity⟩
  have gap c t : contactDepth base T.ends c ≤ base (T.ends c t) + s := by
    obtain ⟨he, hs⟩ := adj c t
    have hx := (drop _ _ he).trans (Nat.add_le_add_left hs _)
    cases t <;> simp_all only [Bool.not_false, Bool.not_true, contactDepth] <;> omega
  let o : Z.Plugs Y := fun x => Classical.choice
    (relative_slots base T.ends Z.depth s D hD (fun c => ∑ x, T.amounts u c x)
      (fun c => sum_nonneg fun x _ => (hy c x).1) gap degree (fun v => (hm v).trans (hb v).2.2)
      enough a Z.lo x)
  exact ⟨Z, o, Z.dispatch o hY hw space hu'⟩

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Applying the reset to a host graph

Count each oriented core contact separately. This costs a factor of two
in the degree, absorbed by using the tighter base-depth difference.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V U : Type} {h : ℕ}

abbrev CoreContact (C : V → Finset V) := {p : V × V // p.2 ∈ C p.1}

def unitEnds {C : V → Finset V} (c : CoreContact C) (t : Bool) :=
  if t then c.val.2 else c.val.1

def coreDemands {src dst : U → V} (ix : U → Cell h) {C : V → Finset V}
    (edge : ∀ i, dst i ∈ C (src i)) : Demands V (CoreContact C) U h :=
  ⟨unitEnds, fun i => ⟨(src i, dst i), edge i⟩, ix⟩

def resetDelay (C : V → Finset V) (Δ D : ℕ) (v z : V) :=
  4 * Nat.clog 2 (2 * if z ∈ C v then Δ else D)

def reserveCount (Δ : ℕ) := 2 * (Δ : ℝ) * (2 : ℝ) ^ (32 * Nat.clog 2 (2 * Δ))

private theorem reserve_le (Δ : ℕ) (hΔ : 0 < Δ) : reserveCount Δ ≤ coreBins Δ := by
  have : 1 ≤ Nat.clog 2 (2 * Δ) := Nat.clog_pos (by decide) (by omega)
  unfold reserveCount coreBins
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm 2 (Δ : ℝ), mul_assoc, ← pow_succ']
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (Nat.cast_nonneg _)

private theorem unitEnds_mem {C : V → Finset V} (cs : ∀ v w, w ∈ C v → v ∈ C w)
    (c : CoreContact C) (t : Bool) :
    unitEnds c (!t) ∈ C (unitEnds c t) := by
  cases t
  · exact c.2
  · exact cs _ _ c.2

private theorem degree_core [Fintype V] (C : V → Finset V)
    (cs : ∀ v w, w ∈ C v → v ∈ C w) (v : V) :
    (∑ c : CoreContact C, ∑ t : Bool, if unitEnds c t = v then (1 : ℝ) else 0) ≤
      2 * (C v).card := by
  have one (t : Bool) : (∑ c : CoreContact C, if unitEnds c t = v then (1 : ℝ) else 0) ≤
      (C v).card := by
    let f (c : {c : CoreContact C // unitEnds c t = v}) : C v :=
      ⟨unitEnds c.val (!t), by simpa only [c.2] using unitEnds_mem cs c.val t⟩
    have inj : Function.Injective f := by
      intro c d he
      have h₁ : unitEnds c.val (!t) = unitEnds d.val (!t) := congrArg Subtype.val he
      have h₂ := c.2.trans d.2.symm
      refine Subtype.ext (Subtype.ext ?_)
      cases t
      · exact Prod.ext h₂ h₁
      · exact Prod.ext h₁ h₂
    rw [sum_boole, ← Fintype.card_subtype, Nat.cast_le, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective f inj
  rw [sum_comm]
  simpa using sum_le_sum (s := univ) (fun t _ => one t)

theorem core_schedule (Y w Δ : ℕ) (ε : ℝ) (hY : 0 < Y) (hw : 0 < w)
    (hΔ : 0 < Δ) (hε : 0 < ε) (enough : 4 * coreBins Δ ≤ Y) :
    ∃ k, Y ^ 2 * w ≤ 2 ^ k ∧
    ∀ (V U : Type) [Fintype V] [Fintype U] (h a D : ℕ), a + k ≤ h → Δ ≤ D →
    ∀ (N C : V → Finset V) (src dst : U → V) (ix : U → Cell h) (edge : ∀ i, dst i ∈ C (src i)),
    (∀ v z, z ∈ N v → v ∈ N z) → (∀ v z, z ∈ C v → v ∈ C z) →
    (∀ v, C v ⊆ N v) → (∀ v, (N v).card ≤ D) → (∀ v, (C v).card ≤ Δ) →
    ∀ (l : V → Cell h → ℝ) (u : ℝ), (∀ v x, 0 ≤ l v x ∧ l v x ≤ 1 / (2 : ℝ) ^ k) →
    0 < u → u ≤ 1 / (2 : ℝ) ^ k → (∀ v x, (coreDemands ix edge).incident u v x ≤ l v x) →
    ∃ (Z : Schedule (coreDemands ix edge) N (resetDelay C Δ D) a k l u (reserveCount Δ) ε)
      (o : Z.Plugs Y), Nonempty (Z.Dispatch o w) := by
  have en : 4 * reserveCount Δ ≤ (Y : ℝ) :=
    (mul_le_mul_of_nonneg_left (reserve_le Δ hΔ) (by norm_num)).trans (by exact_mod_cast enough)
  obtain ⟨k, hk, exe⟩ := reset_schedule Y w (32 * Nat.clog 2 (2 * Δ)) (2 * Δ) ε
    hY hw (by positivity) hε en
  refine ⟨k, hk, ?_⟩
  intro V U _ _ h a D ha hD N C src dst ix edge ns cs sub ndeg cdeg l u hl hu hu' inc
  refine exe V _ U h a ha (coreDemands ix edge) N (resetDelay C Δ D) l u
    (edge_weight_sum N C Δ D 4 hΔ (hΔ.trans_le hD) ns cs ndeg cdeg (by decide)) ?_ ?_ hl hu hu' inc
  · intro c t
    have hm := unitEnds_mem cs c t
    exact ⟨sub _ hm, by simp only [resetDelay, coreDemands, hm, ite_true]; omega⟩
  · exact fun v => (degree_core C cs v).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (cdeg v)) (by norm_num))

/-- Every schedule with the stated margin admits relative reservations,
including the schedule elected by the integer controller. -/
theorem Schedule.reserve {V U : Type} [Fintype V] [Fintype U] {h a k Δ D Y : ℕ}
    {N C : V → Finset V} {src dst : U → V} {ix : U → Cell h}
    {edge : ∀ i, dst i ∈ C (src i)} {l : V → Cell h → ℝ} {u g ε : ℝ}
    (Z : Schedule (coreDemands ix edge) N (resetDelay C Δ D) a k l u g ε)
    (cs : ∀ v z, z ∈ C v → v ∈ C z) (sub : ∀ v, C v ⊆ N v)
    (hΔ : 0 < Δ) (deg : ∀ v, (C v).card ≤ Δ) (enough : 4 * coreBins Δ ≤ Y)
    (margin : g = reserveCount Δ) (x : Site V (h - a)) :
    Nonempty (Slots (relBase a Z.base) unitEnds (relHi a Z.depth) Z.capacity Y x ↪ Fin Y) := by
  subst g
  let s := 32 * Nat.clog 2 (2 * Δ)
  let T := coreDemands ix edge
  have gap c t : contactDepth Z.base T.ends c ≤ Z.base (T.ends c t) + s := by
    have he := unitEnds_mem cs c t
    have hx := Z.drop _ _ (sub _ he)
    simp only [resetDelay, he, ite_true] at hx
    cases t <;> simp only [Bool.not_false, Bool.not_true, contactDepth, T, coreDemands, s] at * <;> omega
  have mass v : (∑ c, ∑ t : Bool, if T.ends c t = v then ∑ x, T.amounts u c x else 0) ≤
      (2 : ℝ) ^ (Z.base v) := by
    rw [T.sum_incident]
    exact (sum_le_sum (fun x _ => Z.mass v x)).trans (Z.mean v)
  have en : 4 * reserveCount Δ ≤ (Y : ℝ) :=
    (mul_le_mul_of_nonneg_left (reserve_le Δ hΔ) (by norm_num)).trans (by exact_mod_cast enough)
  exact relative_slots Z.base T.ends Z.depth s (2 * Δ) (by positivity) (fun c => ∑ x, T.amounts u c x)
    (fun c => sum_nonneg fun x _ => push_nonneg _ _ (fun _ => Z.width.le) _)
    gap (fun v => (degree_core C cs v).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (deg v)) (by norm_num))) mass en a Z.lo x

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Geometry of reset terminals

An absolute leaf address splits into a group index and a site in the
common host. Contacts within a group respect the corresponding host
adjacencies, using the smaller bound on core contacts.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V : Type} {h : ℕ}

def Site.group (a : ℕ) (p : Site V h) : Cell a :=
  if ha : a ≤ p.depth then ancestor ha p.2.2 else 0

theorem Site.group_drop {a : ℕ} {p q : Site V h} (hp : a ≤ p.depth) (hq : a ≤ q.depth)
    (e : p.group a = q.group a) (d : p.drop a = q.drop a) : p = q := by
  exact Site.drop_injective a hp hq (by simpa [Site.group, hp, hq] using e) d

variable [Fintype V] {A U : Type} [Fintype U] {a k : ℕ}
variable {T : Demands V A U h} {N : V → Finset V} {d : V → V → ℕ}
variable {l : V → Cell h → ℝ} {u g ε : ℝ}

namespace Schedule
variable (Z : Schedule T N d a k l u g ε)

theorem leaf_depth (p : V × Cell h) : a ≤ (Z.leaf p).depth := by
  obtain ⟨mem, bound, _⟩ := reset_leaves N d Z.base l Z.π.toEquiv
    (by have := Z.block; omega) Z.hi Z.drop (fun v x => (Z.sizes v x).2)
  exact (Z.lo p.1).trans (bound _ _ (mem p.1 p.2)).1

def group (x : Cell h) : Cell a := ancestor (by have := Z.block; omega) (Z.π x)

theorem leaf_group (p : V × Cell h) : (Z.leaf p).group a = Z.group p.2 := by
  rw [Site.group, dite_eq_left (Z.leaf_depth p)]
  rfl

theorem group_end (e : U) (t : Bool) :
    (Z.leaf (T.point e t)).group a = Z.group (T.ix e) := Z.leaf_group _

theorem leaf_gap {v z : V} (hz : z ∈ N v) (x : Cell h) :
    (Z.leaf (z, x)).depth ≤ (Z.leaf (v, x)).depth + 16 * d v z := by
  obtain ⟨_, _, gap⟩ := reset_leaves N d Z.base l Z.π.toEquiv
    (by have := Z.block; omega) Z.hi Z.drop (fun v x => (Z.sizes v x).2)
  exact gap v z hz (Z.π x)

theorem leaf_near {C : V → Finset V} {Δ D : ℕ}
    (Z : Schedule T N (resetDelay C Δ D) a k l u g ε)
    {P : V → Finset V} {L : ℕ} (sym : ∀ v z, z ∈ P v → v ∈ P z)
    (sub : ∀ v, P v ⊆ N v) (bound : ∀ v z, z ∈ P v → (if z ∈ C v then Δ else D) ≤ L)
    {v z : V} (hz : z ∈ P v) (x : Cell h) :
    (Z.leaf (z, x)).drop a ∈ near P L ((Z.leaf (v, x)).drop a) := by
  apply drop_near
  have gap v z (he : z ∈ P v) :
      (Z.leaf (z, x)).depth ≤ (Z.leaf (v, x)).depth + 64 * Nat.clog 2 (2 * L) := by
    have hm := Z.leaf_gap (sub v he) x
    have hs := Nat.clog_mono_right 2 (Nat.mul_le_mul_left 2 (bound v z he))
    refine hm.trans (Nat.add_le_add_left ?_ _)
    unfold resetDelay
    omega
  exact (mem_near _ _ _ _).mpr (.inr ⟨hz, ⟨_, leafSite_contains _ _ _, leafSite_contains _ _ _⟩,
    gap z v (sym _ _ hz), gap v z hz⟩)

end Schedule

/-- All terminals of possible neighboring leaves are eligible. -/
def terminalNear (P : V → Finset V) (L Y : ℕ) (x : Site V h × Fin Y) :=
  near P L x.1 ×ˢ (univ : Finset (Fin Y))

theorem terminal_symm {P : V → Finset V} (sym : ∀ v z, z ∈ P v → v ∈ P z)
    (L Y : ℕ) (x y : Site V h × Fin Y) (hy : y ∈ terminalNear P L Y x) :
    x ∈ terminalNear P L Y y :=
  mem_product.mpr ⟨near_symm sym _ _ _ (mem_product.mp hy).1, mem_univ _⟩

def terminalWidth (L Y : ℕ) := (4 * L) ^ 300 * Y

theorem terminal_card (P : V → Finset V) (L Y : ℕ) (hL : 0 < L) (deg : ∀ v, (P v).card ≤ L)
    (x : Site V h × Fin Y) : (terminalNear P L Y x).card ≤ terminalWidth L Y := by
  rw [terminalNear, card_product, card_univ, Fintype.card_fin]
  exact Nat.mul_le_mul_right _ (near_card _ _ hL deg _)

end OAI.LinearAlgebra.MatrixExponent.Packing
end
