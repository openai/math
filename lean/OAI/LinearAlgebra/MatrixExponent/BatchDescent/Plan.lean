import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Pieces
import Mathlib.Algebra.BigOperators.Fin
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dictionary

section
/-!
# Dyadic scales for the many-list descent

The beat count grows like a small fixed multiple of the logarithm of
the tag width. A quadratic exponent in that count is still affordable
for replication, while exponential losses must fit in the width.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Filter

theorem scales (B J : ℕ) (hB : 0 < B) :
    ∀ᶠ w : ℕ in atTop, ∃ j : ℕ, J ≤ j ∧ 1 ≤ j ∧ 2 ^ (B * j) ≤ w ∧ w ≤ 2 ^ (2 * B * j) := by
  filter_upwards [eventually_ge_atTop (2 ^ (B * (J + 1)))] with w hw
  have hw' : 0 < w := (pow_pos (by decide : 0 < 2) _).trans_le hw
  let j := Nat.log 2 w / B
  have low : J + 1 ≤ j := (Nat.le_div_iff_mul_le hB).mpr (by
    rw [mul_comm]
    exact Nat.le_log_of_pow_le (by decide) hw)
  have h₁ : B * j ≤ Nat.log 2 w := Nat.mul_div_le _ _
  have h₂ : Nat.log 2 w < (j + 1) * B := (Nat.div_lt_iff_lt_mul hB).mp (Nat.lt_succ_self j)
  have h₃ : Nat.log 2 w + 1 ≤ 2 * B * j := by nlinarith
  exact ⟨j, by omega, by omega,
    (Nat.pow_le_pow_right (by decide) h₁).trans (Nat.pow_log_le_self 2 hw'.ne'),
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) w).le.trans
      (Nat.pow_le_pow_right (by decide) h₃)⟩

private theorem cube_le {j : ℕ} (hj : 16 ≤ j) : j ^ 3 ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    calc
      _ ≤ 2 * j ^ 3 := by nlinarith [Nat.mul_le_mul_left (j ^ 2) hj]
      _ ≤ _ := by rw [pow_succ' 2 j]; gcongr

theorem replication {κ : ℝ} (hk : 0 < κ) (v : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ w : ℕ, 2 ^ j ≤ w →
      (2 : ℝ) ^ (v * j ^ 2 : ℕ) ≤ ((2 : ℝ) ^ w : ℝ) ^ κ := by
  obtain ⟨J, hJ⟩ := exists_nat_gt ((v : ℝ) / κ)
  filter_upwards [eventually_ge_atTop 16, eventually_ge_atTop J] with j hj hj' w hw
  rw [← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h : (v : ℝ) ≤ j * κ := (div_le_iff₀ hk).mp (hJ.le.trans (Nat.cast_le.mpr hj'))
  have hpow : (j : ℝ) ^ 3 ≤ w := by exact_mod_cast (cube_le hj).trans hw
  push_cast
  calc
    _ ≤ (j * κ) * (j : ℝ) ^ 2 := by gcongr
    _ = (j : ℝ) ^ 3 * κ := by ring
    _ ≤ _ := by gcongr

theorem saving {B j w : ℕ} (hB : 0 < B) (hw : 1 ≤ w) (hu : w ≤ 2 ^ (2 * B * j)) :
    (1 / 2 : ℝ) ^ j ≤ (w : ℝ) ^ (-(1 / (2 * B : ℝ))) := by
  have hb : 0 < (B : ℝ) := Nat.cast_pos.mpr hB
  have hp : (w : ℝ) ^ (1 / (2 * B : ℝ)) ≤ (2 : ℝ) ^ j := calc
    _ ≤ ((2 : ℝ) ^ (2 * B * j : ℕ) : ℝ) ^ (1 / (2 * B : ℝ)) := by gcongr; exact_mod_cast hu
    _ = _ := by
      rw [← Real.rpow_natCast_mul (by norm_num)]
      have : ((2 * B * j : ℕ) : ℝ) * (1 / (2 * B : ℝ)) = j := by push_cast; field_simp
      rw [this, Real.rpow_natCast]
  rw [one_div_pow, Real.rpow_neg (Nat.cast_nonneg _), ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hp

/-- Round the slot width down to a multiple of the bin size. Keeping
half of the available space suffices for a uniform per-bit bound. -/
theorem fill {q W w : ℕ} (hq : 0 < q) (hW : 0 < W) (hw : 32 * q * W ≤ w) :
    ∃ z, 0 < z ∧ W ∣ z ∧ 16 * q * z ≤ w ∧ w ≤ 32 * q * z := by
  let b := 16 * q * W
  have hb : 0 < b := by unfold b; positivity
  have hbig : 2 * b ≤ w := by unfold b; nlinarith only [hw]
  let l := w / b
  have hl : 2 ≤ l := (Nat.le_div_iff_mul_le hb).mpr hbig
  refine ⟨W * l, by positivity, dvd_mul_right _ _, ?_, ?_⟩
  · rw [← mul_assoc]; exact Nat.mul_div_le w b
  · have ht : w < (l + 1) * b := (Nat.div_lt_iff_lt_mul hb).mp (Nat.lt_succ_self l)
    calc
      _ ≤ (l + 1) * b := ht.le
      _ ≤ 2 * l * b := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by unfold b; ring

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-! # Combining the core and exterior port inventories -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows

variable {H m d e : ℕ} (l : Inventory H m d) (r : Inventory H m e)

def append : Inventory H m (d + e) := fun i j => Fin.append (l i j) (r i j)

@[simp] theorem append_left (i j k) : append l r i j (Fin.castAdd e k) = l i j k := by
  simp [append]

@[simp] theorem append_right (i j k) : append l r i j (Fin.natAdd d k) = r i j k := by
  simp [append]

@[simp] theorem arity_append (i j) : arity (append l r i) j = arity (l i) j + arity (r i) j := by
  simp [arity, Fin.sum_univ_add]

private def lift {d' : ℕ} (l' : Inventory H m d') (f : Fin d ↪ Fin d')
    (hf : ∀ i j k, l' i j (f k) = l i j k) : Endpoints l ↪ Endpoints l' where
  toFun x := ⟨x.1, x.2.1, f x.2.2.1, x.2.2.2.cast (hf _ _ _).symm⟩
  inj' := by
    rintro ⟨i, j, k, b⟩ ⟨i', j', k', b'⟩ he
    have hi : i = i' := congrArg Sigma.fst he
    have hj : j = j' := congrArg (fun x => x.2.1) he
    have hk : k = k' := f.injective (congrArg (fun x => x.2.2.1) he)
    subst i'; subst j'; subst k'
    have hb : b = b' := Fin.ext (congrArg (fun x => x.2.2.2.val) he)
    subst b'
    rfl

private theorem rank_lift {d' : ℕ} (l' : Inventory H m d') (f : Fin d ↪ Fin d')
    (hf : ∀ i j k, l' i j (f k) = l i j k) (x : Endpoints l) :
    rank l' (lift l l' f hf x) = rank l x := by
  have he : port (l' x.1) (f x.2.2.1) = port (l x.1) x.2.2.1 :=
    funext fun k => hf _ k _
  change start (port (l' x.1) (f x.2.2.1)) _ + _ = _
  rw [he]
  rfl

def extendL : Endpoints l ↪ Endpoints (append l r) :=
  lift l _ (Fin.castAddEmb e) (append_left l r)

def extendR : Endpoints r ↪ Endpoints (append l r) :=
  lift r _ (Fin.natAddEmb d) (append_right l r)

@[simp] theorem rank_extendL (x : Endpoints l) : rank (append l r) (extendL l r x) = rank l x :=
  rank_lift ..

@[simp] theorem rank_extendR (x : Endpoints r) : rank (append l r) (extendR l r x) = rank r x :=
  rank_lift ..

theorem channels_disjoint (x : Endpoints l) (y : Endpoints r) :
    (extendL l r x).2.2.1 ≠ (extendR l r y).2.2.1 := by
  intro he
  have hx := x.2.2.1.isLt
  have hh : x.2.2.1.val = d + y.2.2.1.val := congrArg Fin.val he
  omega

noncomputable def combined : Endpoints l ⊕ Endpoints r ≃ Endpoints (append l r) :=
  Equiv.ofBijective (Sum.elim (extendL l r) (extendR l r)) (by
    constructor
    · rintro (x|x) (y|y) he
      · exact congrArg Sum.inl ((extendL l r).injective he)
      · exact (channels_disjoint l r x y (congrArg (fun x => x.2.2.1) he)).elim
      · exact (channels_disjoint l r y x (congrArg (fun x => x.2.2.1) he.symm)).elim
      · exact congrArg Sum.inr ((extendR l r).injective he)
    · rintro ⟨i, j, k, b⟩
      induction k using Fin.addCases with
      | left k => exact ⟨.inl ⟨i, j, k, b.cast (append_left ..)⟩, rfl⟩
      | right k => exact ⟨.inr ⟨i, j, k, b.cast (append_right ..)⟩, rfl⟩)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end

section
/-!
# Ordering internal channels

An oriented lane identifies its two hosts and its direction. Within a
lane order bundles by block, breaking ties by an edge key. Hence each
end computes the same ordinal in its own lane, including for loops.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows

structure Channels (E : Type) (H m d : ℕ) where
  host : Bool → E → Fin H
  block : E → Fin m
  lane : Bool → E → Fin d
  key : E → ℕ
  lanes : ∀ i j b c, (host b i = host c j ∧ lane b i = lane c j) ↔
    b = c ∧ host false i = host false j ∧ host true i = host true j
  unique : ∀ i j, host false i = host false j → block i = block j → key i = key j → i = j

namespace Channels

open Finset
variable {E : Type} [Fintype E] {H m d : ℕ} (A : Channels E H m d)

def position (x : E × Bool) := (A.host x.2 x.1, A.block x.1, A.lane x.2 x.1)

def pool (p : Fin H × Fin m × Fin d) := univ.filter (fun x => A.position x = p)

def inventory : Inventory H m d := fun a b c => (A.pool (a, b, c)).card

def prior (x : E × Bool) :=
  ((A.pool (A.position x)).filter (fun y => A.key y.1 < A.key x.1)).card

private theorem prior_lt (x : E × Bool) :
    A.prior x < A.inventory (A.host x.2 x.1) (A.block x.1) (A.lane x.2 x.1) := by
  apply card_lt_card
  refine (ssubset_iff_of_subset (filter_subset _ _)).mpr ⟨x, ?_, ?_⟩
  · simp [pool]
  · simp

private theorem prior_mono (x y : E × Bool) (he : A.position x = A.position y)
    (hl : A.key x.1 < A.key y.1) : A.prior x < A.prior y := by
  unfold prior
  rw [← he]
  apply card_lt_card
  refine (ssubset_iff_of_subset ?_).mpr ⟨x, by simp [pool, hl], by simp⟩
  intro i hi
  exact mem_filter.mpr ⟨(mem_filter.mp hi).1, (mem_filter.mp hi).2.trans hl⟩

private def assign (x : E × Bool) : Endpoints A.inventory :=
  ⟨A.host x.2 x.1, A.block x.1, A.lane x.2 x.1, ⟨A.prior x, A.prior_lt x⟩⟩

private theorem assign_injective : Function.Injective A.assign := by
  intro x y h
  have hp : A.position x = A.position y :=
    congrArg (fun p : Endpoints A.inventory => (p.1, p.2.1, p.2.2.1)) h
  have he : A.prior x = A.prior y := congrArg (fun p => p.2.2.2.val) h
  have hk : A.key x.1 = A.key y.1 := by
    rcases lt_trichotomy (A.key x.1) (A.key y.1) with l | l | l
    · exact ((A.prior_mono x y hp l).ne he).elim
    · exact l
    · exact ((A.prior_mono y x hp.symm l).ne he.symm).elim
  obtain ⟨hb, h₁, _⟩ := (A.lanes x.1 y.1 x.2 y.2).mp
    ⟨congrArg Prod.fst hp, congrArg (·.2.2) hp⟩
  exact Prod.ext (A.unique _ _ h₁ (congrArg (·.2.1) hp) hk) hb

private theorem card_endpoints : Fintype.card (E × Bool) = Fintype.card (Endpoints A.inventory) := by
  have he := card_eq_sum_card_fiberwise (s := univ) (f := A.position) (fun i _ => mem_univ _)
  rw [Fintype.sum_prod_type] at he
  simp only [card_univ, Fintype.sum_prod_type] at he
  unfold Endpoints Slots Blocks
  simp_rw [Fintype.card_sigma, Fintype.card_fin]
  exact he

noncomputable def point : E × Bool ≃ Endpoints A.inventory :=
  Equiv.ofBijective A.assign ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨A.assign_injective, A.card_endpoints⟩)

theorem point_val (i : E) (b : Bool) : A.point (i, b) =
    ⟨A.host b i, A.block i, A.lane b i, ⟨A.prior (i, b), A.prior_lt (i, b)⟩⟩ := rfl

def family (i : E) (v : Fin m) : Finset E :=
  univ.filter fun j => A.host false j = A.host false i ∧ A.host true j = A.host true i ∧ A.block j = v

private def flag (b : Bool) : E ↪ E × Bool := ⟨fun i => (i, b), fun _ _ h => congrArg Prod.fst h⟩

private theorem pool_at (i : E) (b : Bool) (v : Fin m) :
    A.pool (A.host b i, v, A.lane b i) = (A.family i v).map (flag b) := by
  ext ⟨j, c⟩
  simp only [pool, position, family, mem_filter, mem_univ, true_and, Prod.mk.injEq, mem_map]
  constructor
  · rintro ⟨hs, hv, hp⟩
    obtain ⟨rfl, he, he'⟩ := (A.lanes _ _ _ _).mp ⟨hs, hp⟩
    exact ⟨j, ⟨he, he', hv⟩, rfl⟩
  · rintro ⟨x, ⟨hs, ht, hv⟩, eq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    obtain ⟨hs', hp⟩ := (A.lanes x i b b).mpr ⟨rfl, hs, ht⟩
    exact ⟨hs', hv, hp⟩

theorem inventory_at (i : E) (b : Bool) (v : Fin m) :
    A.inventory (A.host b i) v (A.lane b i) = (A.family i v).card := by
  rw [inventory, pool_at, card_map]

theorem prior_at (i : E) (b : Bool) :
    A.prior (i, b) = ((A.family i (A.block i)).filter (fun j => A.key j < A.key i)).card := by
  rw [prior, position, pool_at, filter_map, card_map]
  rfl

theorem rank_eq (i : E) (b : Bool) :
    rank A.inventory (A.point (i, b)) = rank A.inventory (A.point (i, false)) := by
  have he : port (A.inventory (A.host b i)) (A.lane b i) =
      port (A.inventory (A.host false i)) (A.lane false i) := by
    funext v
    simp only [port, inventory_at]
  simp only [rank, point_val, he, prior_at]

variable {u v K d' : ℕ} {r : Inventory H m d'} (L : Layout (append A.inventory r) u v K)

noncomputable def loc (i : E) (b : Bool) := L.portSlots (extendL A.inventory r (A.point (i, b)))

theorem col_eq (i : E) (b : Bool) : (A.loc L i b).2 = (A.loc L i (!b)).2 := by
  apply Fin.ext
  unfold loc
  rw [L.ordinal, L.ordinal, rank_extendL, rank_extendL, A.rank_eq i b, A.rank_eq i (!b)]

theorem row_eq (i j : E) (b c : Bool) :
    (A.loc L i b).1 = (A.loc L j c).1 ↔ b = c ∧
      A.host false i = A.host false j ∧ A.host true i = A.host true j ∧
      rank A.inventory (A.point (i, false)) / (2 * u) = rank A.inventory (A.point (j, false)) / (2 * u) := by
  unfold loc
  rw [L.row_eq, rank_extendL, rank_extendL, A.rank_eq i b, A.rank_eq j c]
  change (A.host b i = A.host c j ∧ (Fin.castAddEmb d') (A.lane b i) = (Fin.castAddEmb d') (A.lane c j)) ∧ _ ↔ _
  rw [(Fin.castAddEmb d').injective.eq_iff, A.lanes, and_assoc, and_assoc]

end Channels
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end

/-! # Internal channel inventories from a posted core diagram -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent

namespace BatchDescent.PackRows.Channels

variable {E : Type} [Fintype E] {H m d : ℕ} (A : Channels E H m d)

theorem total_eq : ∑ i, total (A.inventory i) = 2 * Fintype.card E := by
  have he := Fintype.card_congr A.point
  unfold Endpoints Slots Blocks at he
  simp_rw [Fintype.card_sigma, Fintype.card_fin] at he
  rw [Fintype.card_prod, Fintype.card_bool, mul_comm] at he
  exact he.symm

theorem arity_eq (i : Fin H) (j : Fin m) :
    arity (A.inventory i) j =
      ∑ e, ((if A.host false e = i ∧ A.block e = j then 1 else 0) +
            (if A.host true e = i ∧ A.block e = j then 1 else 0)) := by
  let s := Finset.univ.filter (fun t : E × Bool => A.host t.2 t.1 = i ∧ A.block t.1 = j)
  have h (k : Fin d) : A.inventory i j k = (s.filter (fun t => A.lane t.2 t.1 = k)).card := by
    simp only [inventory, pool, position, s, Finset.filter_filter, Prod.mk.injEq, and_assoc]
  unfold arity
  simp_rw [h]
  rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)]
  unfold s
  rw [Finset.card_filter, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun e _ => (Fintype.sum_bool _).trans (Nat.add_comm ..)

end BatchDescent.PackRows.Channels

namespace Assembly.Scheme.Posting
open BatchDescent.PackRows Packing Coloring
open scoped Classical

variable {F T : Type} [Field F] {x y : Wire} {L : Fringe x y T} {h z : ℕ}
    {S : Scheme F} {r : S.format.obj} {G : HostNet F L h z}
    (p : S.Posting r G) (hz : 0 < z)

include hz in
theorem neighbor (i : G.E) (b : Bool) :
    (r (p.host (side G i b))).1 (p.index (side G i b) (side G i (!b))) =
      p.host (side G i (!b)) := by
  cases b
  · exact p.target hz i
  · have he := (p.internal (G.units.bits.symm (i, ⟨0, hz⟩))).1
    change S.peer r (p.toSeating.ends (endBit G i false _)).1 =
      some (p.toSeating.ends (endBit G i true _)).1 at he
    rw [(p.ordered _ _ _).1, (p.ordered _ _ _).1] at he
    have hr := (p.proper _ _ he).1
    rw [peer, p.link] at hr
    exact congrArg (fun j : S.Span => j.1.1) (Option.some.inj hr)

def lane (b : Bool) (i : G.E) : Fin (2 * 2 ^ S.d) :=
  finProdFinEquiv (finTwoEquiv.symm b, p.index (side G i b) (side G i (!b)))

def channels (p : S.Posting r G) (hz : 0 < z) : Channels G.E (2 ^ S.m) (2 ^ S.h) (2 * 2 ^ S.d) where
  host b i := p.host (side G i b)
  block i := p.block (G.ix i)
  lane := p.lane
  key i := (p.stub i false).val
  lanes i j b c := by
    constructor
    · rintro ⟨he, hl⟩
      obtain ⟨hb, ht⟩ := Prod.mk.inj (finProdFinEquiv.injective hl)
      have eq := finTwoEquiv.symm.injective hb
      subst c
      have ho : p.host (side G i (!b)) = p.host (side G j (!b)) := by
        rw [← p.neighbor hz i b, ← p.neighbor hz j b, he, ht]
      cases b
      · exact ⟨rfl, he, ho⟩
      · exact ⟨rfl, ho, he⟩
    · rintro ⟨rfl, hl, hr⟩
      have eq (b) : side G i b = side G j b := by
        cases b
        · exact p.host.injective hl
        · exact p.host.injective hr
      simp only [lane, eq, and_self]
  unique i j hi hb he := by
    apply p.distinct hz
    unfold span spanAt
    rw [hi, hb, Fin.ext he]

theorem channels_arity (i : G.V) (j : Cell h) :
    arity ((p.channels hz).inventory (p.host i)) (p.block j) = degree G.pair (i, j) := by
  rw [Channels.arity_eq, degree_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp [channels, side, arityCost, HostNet.pair, Prod.ext_iff]

end Assembly.Scheme.Posting
end OAI.LinearAlgebra.MatrixExponent
end

/-!
# Recovering the internal channel order from local metadata

The key of a source endpoint is its own stub index. At a destination
it is the peer stub index in the local pattern. Lane sizes and copy
ordinals can thus be computed without looking at other host positions.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring BatchDescent.PackRows Packing
open scoped Classical

namespace Pattern

variable {F : Type} {d k e : ℕ} (p : Pattern F d k e)

/-- The oriented lane and source stub of a positive internal span. -/
def inner (i : B e) : Option (Fin (2 * 2 ^ d) × B e) :=
  if p.width 0 i = 0 then none else
  (p.peer 0 i).map fun a =>
    let t := p.direction 0 i
    (finProdFinEquiv (finTwoEquiv.symm t, a.1), if t then a.2.2 else i)

def innerCount (j : Fin (2 * 2 ^ d)) :=
  (Finset.univ.filter fun i => ∃ a, p.inner i = some (j, a)).card

def innerPrior (j : Fin (2 * 2 ^ d)) (z : B e) :=
  (Finset.univ.filter fun i => ∃ a, p.inner i = some (j, a) ∧ a < z).card

end Pattern

namespace Scheme.Posting

variable {F T : Type} [Field F] {x y : Wire} {L : Fringe x y T} {h z : ℕ}
    {S : Scheme F} {r : S.format.obj} {G : HostNet F L h z}
    (p : S.Posting r G) (hz : 0 < z)

include hz in
theorem inner_spec (i : G.E) (t : Bool) :
    (S.pattern r (p.span i t).1).inner (p.stub i t) = some (p.lane t i, p.stub i false) := by
  have hw := p.length i t
  have hd := p.dir i t
  have hp := p.link i t
  change (S.pattern r (p.span i t).1).width 0 (p.stub i t) = z at hw
  change (S.pattern r (p.span i t).1).direction 0 (p.stub i t) = t at hd
  change (S.pattern r (p.span i t).1).peer 0 (p.stub i t) = _ at hp
  rw [Pattern.inner, hw, ite_eq_right hz.ne', hp, hd]
  cases t <;> rfl

theorem found (a : S.Span) (hs : 0 < S.width r a) (hv : (S.peer r a).isSome) :
    ∃ i : G.E × Bool, p.span i.1 i.2 = a := by
  obtain ⟨q, hq⟩ := p.toSeating.ends.surjective ⟨a, ⟨0, hs⟩⟩
  have he : (p.toSeating.ends q).1 = a := congrArg Sigma.fst hq
  rcases q with (i|e)|(i|e)
  · rw [← he, p.input] at hv
    cases hv
  · obtain ⟨⟨i, j⟩, rfl⟩ := G.units.bits.symm.surjective e
    exact ⟨(i, false), (p.ordered i false j).1.symm.trans he⟩
  · rw [← he, p.output] at hv
    cases hv
  · obtain ⟨⟨i, j⟩, rfl⟩ := G.units.bits.symm.surjective e
    exact ⟨(i, true), (p.ordered i true j).1.symm.trans he⟩

include hz in
theorem inner_iff (i : B S.m) (j : B S.h) (s : B S.e) (l : Fin (2 * 2 ^ S.d)) (u : B S.e) :
    (S.pattern r (i, j, 0)).inner s = some (l, u) ↔
      ∃ w : G.E × Bool, (p.channels hz).position w = (i, j, l) ∧
        p.stub w.1 w.2 = s ∧ p.stub w.1 false = u := by
  constructor
  · intro he
    let a : S.Span := ((i, j, 0), s)
    have hw : 0 < S.width r a := by
      by_contra! h
      have ha : (S.pattern r (i, j, 0)).width 0 s = 0 := Nat.eq_zero_of_le_zero h
      simp [Pattern.inner, ha] at he
    have hv : (S.peer r a).isSome := by
      cases hl : (S.pattern r (i, j, 0)).peer 0 s with
      | none => simp [Pattern.inner, hl] at he
      | some v => simp [a, peer, hl]
    obtain ⟨⟨w, t⟩, eq⟩ := p.found a hw hv
    have hp := p.inner_spec hz w t
    have hs : p.stub w t = s := congrArg Prod.snd eq
    rw [hs, eq, he] at hp
    obtain ⟨hl, hu⟩ := Prod.mk.inj (Option.some.inj hp.symm)
    exact ⟨(w, t), Prod.ext (congrArg (·.1.1) eq) (Prod.ext (congrArg (·.1.2.1) eq) hl), hs, hu⟩
  · rintro ⟨⟨w, t⟩, hp, rfl, rfl⟩
    change (p.host (side G w t), p.block (G.ix w), p.lane t w) = (i, j, l) at hp
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj hp |>.imp_right Prod.mk.inj
    exact p.inner_spec hz w t

private theorem filtered (i : B S.m) (j : B S.h) (l : Fin (2 * 2 ^ S.d)) (P : B S.e → Prop)
    [DecidablePred P] :
    (((p.channels hz).pool (i, j, l)).filter (fun w => P (p.stub w.1 false))).card =
      (Finset.univ.filter fun s => ∃ u, (S.pattern r (i, j, 0)).inner s = some (l, u) ∧ P u).card := by
  let A := p.channels hz
  have get (w : G.E × Bool) (hw : w ∈ A.pool (i, j, l)) :
      (S.pattern r (i, j, 0)).inner (p.stub w.1 w.2) = some (l, p.stub w.1 false) :=
    (p.inner_iff hz _ _ _ _ _).mpr ⟨w, (Finset.mem_filter.mp hw).2, rfl, rfl⟩
  refine Finset.card_bij (fun w _ => p.stub w.1 w.2) ?_ ?_ ?_
  · intro w hw
    obtain ⟨hw, hp⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, get w hw, hp⟩
  · intro x hx y hy he
    have hx' := (Finset.mem_filter.mp hx).1
    have hy' := (Finset.mem_filter.mp hy).1
    have hh := get x hx'
    rw [he, get y hy'] at hh
    have hk : A.key x.1 = A.key y.1 := congrArg Fin.val (Prod.mk.inj (Option.some.inj hh.symm)).2
    have ht := (Finset.mem_filter.mp hx').2.trans (Finset.mem_filter.mp hy').2.symm
    obtain ⟨hb, hl, _⟩ := (A.lanes _ _ _ _).mp ⟨congrArg Prod.fst ht, congrArg (·.2.2) ht⟩
    exact Prod.ext (A.unique _ _ hl (congrArg (·.2.1) ht) hk) hb
  · intro s hs
    obtain ⟨u, hu, hp⟩ := (Finset.mem_filter.mp hs).2
    obtain ⟨w, hw, he, hf⟩ := (p.inner_iff hz _ _ _ _ _).mp hu
    refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, ?_⟩, he⟩
    rwa [hf]

theorem channels_count (i : B S.m) (j : B S.h) (l : Fin (2 * 2 ^ S.d)) :
    (p.channels hz).inventory i j l = (S.pattern r (i, j, 0)).innerCount l := by
  simpa [Channels.inventory, Pattern.innerCount] using p.filtered hz i j l (fun _ => True)

theorem channels_prior (i : G.E) (b : Bool) :
    (p.channels hz).prior (i, b) =
      (S.pattern r (p.span i b).1).innerPrior (p.lane b i) (p.stub i false) :=
  p.filtered hz _ _ _ (fun k => k < p.stub i false)

end Scheme.Posting
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # The dictionary product equals the product of occurrence tables -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Pieces
open Assembly Coloring PackRows Classical

variable {F : Type} {S : Scheme F} {r : S.format.obj} {d u v K p : ℕ}
  {l : Inventory (2 ^ S.m) (2 ^ S.h) d} (B : Pieces S r l v p)

def equiv : units S r (bundleSize v p) ≃ Endpoints l :=
  Equiv.sigmaCongrRight fun i => Equiv.sigmaCongrRight (B.locate i)

def slots : S.Pin r ≃ Endpoints l × Payload v (Fin p) :=
  (join S r _ B.uniform).symm.trans (B.equiv.prodCongr finProdFinEquiv.symm)

def inside (L : PackRows.Layout l u v K) : S.Pin r ↪ Address v K × Row (Fin (2 * v)) (Fin (2 * u)) (Fin p) :=
  B.slots.toEmbedding.trans <| (L.portSlots.prodMap (.refl _)).trans
    (Equiv.prodAssoc _ _ _).toEmbedding

theorem inside_join (L : PackRows.Layout l u v K) (x : units S r (bundleSize v p))
    (t : Fin (bundleSize v p)) :
    B.inside L (join S r _ B.uniform (x, t)) =
      ((L.portSlots (B.equiv x)).1, (L.portSlots (B.equiv x)).2, finProdFinEquiv.symm t) := by
  unfold inside slots
  simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  rfl

def Room := ∀ i j, arity (l i) j ≤ u

include B in
theorem fits (ha : Room (l := l) (u := u)) (i j) :
    Fintype.card (Parts.Unit (pattern S r i j) (bundleSize v p)) ≤ u := by
  rw [Fintype.card_congr (B.locate i j), Fintype.card_sigma]
  simpa only [Fintype.card_fin, arity] using ha i j

def index (ha : Room (l := l) (u := u)) : Index l u :=
  fun i j => (B.locate i j).symm.toEmbedding.trans (Parts.number _ _ (B.fits ha i j))

variable [Field F]

private theorem eval_entry (ha : Room (l := l) (u := u))
    (y : Endpoints l → Payload v (Fin p) → Bool) (i j) :
    entry S u v p (labels S r i j) (padded (B.index ha) y i j) =
      ∏ k : Coloring.B S.k, S.table r (i, j, k) (Function.uncurry y ∘ B.slots ∘ S.port r (i, j, k)) := by
  unfold entry labels
  rw [Equiv.symm_apply_apply]
  unfold entryAt
  dsimp only
  rw [dite_eq_left ⟨B.uniform i j, B.fits ha i j⟩]
  unfold Parts.value
  apply Finset.prod_congr rfl
  intro k _
  unfold Scheme.table
  apply congrArg
  funext s t
  let a := (Parts.join _ _ (B.uniform i j)).symm ⟨(k, s), t⟩
  have he : B.index ha i j (B.locate i j a.1) = Parts.number _ _ (B.fits ha i j) a.1 := by
    simp [index]
  change padded (B.index ha) y i j (Parts.number _ _ (B.fits ha i j) a.1, finProdFinEquiv.symm a.2) =
    y ⟨i, j, B.locate i j a.1⟩ (finProdFinEquiv.symm a.2)
  rw [← he, padded_at]

theorem product (ha : Room (l := l) (u := u)) (L : PackRows.Layout l u v K)
    (y : Address v K × Row (Fin (2 * v)) (Fin (2 * u)) (Fin p) → Bool) :
    (∏ i, ∏ j, entry S u v p (labels S r i j)
      (padded (B.index ha) (fun z t => y ((L.portSlots z).1, (L.portSlots z).2, t)) i j)) =
    ∏ v, S.table r v (y ∘ B.inside L ∘ S.port r v) := by
  simp only [Fintype.prod_prod_type, eval_entry]
  rfl

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Pieces
end

/-!
# Padded port slots

Check one row at a time by table lookup. The routing description names
the port sockets actually consumed. Every other socket must be zero
to avoid introducing multiplicities when summing over private wires.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
open Classical Transcript

variable {H m d u v K : ℕ} {l : Inventory H m d} {P X : Type}

def Layout.Padded (L : Layout l u v K) (x : Address v K × Fin (2 * u) → Payload v P → Bool) : Prop :=
  ∀ i ∉ Set.range L.portSlots, ∀ t, x i t = false

private theorem used (L : Layout l u v K) (r : Address v K) (s : Fin (2 * u)) :
    (∃ j, L.moves r.1 (j, r.2, s) = true) ↔ (r, s) ∈ Set.range L.portSlots := by
  simp only [Layout.moves, decide_eq_true_eq]
  constructor
  · rintro ⟨_, i, _, hi⟩
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨((L.tableSlots i).1.2, (L.tableSlots i).2), i, ?_, hi⟩
    exact Prod.ext (Prod.ext ((L.bin_eq i).trans (congrArg (·.1.1) hi)) rfl) rfl

private abbrev Pins (v u : ℕ) (P : Type) := Route v u ⊕ (Fin (2 * u) × Payload v P)

private def ok (x : Pins v u P → Bool) : Prop :=
  ∀ s, (¬∃ j : Socket v u, x (.inl (j, j.1, s)) = true) → ∀ t, x (.inr (s, t)) = false

variable (F : Type) [Field F] (control : Fin K → Route v u → X ⊕ Bool)
    (port : Fin K → Socket v u → Payload v P → X ⊕ Bool)

private def tap (r : Address v K) : Pins v u P → X ⊕ Bool
  | .inl j => control r.1 (j.1, r.2, j.2.2)
  | .inr t => port r.1 (r.2, t.1) t.2

def zeroTest (x : X → Bool) : F :=
  ∏ r, if ok (Sum.elim x id ∘ tap control port r) then 1 else 0

variable {F}

theorem packed_zero [Fintype P] [Fintype X] {w j a : ℕ}
    (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w) (ha : 3 ≤ a) (hb : 2 * 2 ^ (j + 1) * (2 * j + 2) ≤ a)
    (hwidth : Fintype.card (Route v u) + Fintype.card (Fin (2 * u) × Payload v P) < j)
    (hrows : Fintype.card (Address v K) ≤ 2 ^ j) :
    WideWeight F a (SortTables F w) (zeroTest F control port) (4 * Fintype.card X + 11000 * 2 ^ j * (1 + j)) :=
  dictionary hj hj' ha hb (by rw [Fintype.card_sum]; exact hwidth) hrows
    (fun x => if ok x then 1 else 0) (tap control port)

variable {control port}

theorem zeroTest_eq (L : Layout l u v K) (x : X → Bool) (hm : ∀ g, Sum.elim x id ∘ control g = L.moves g) :
    zeroTest F control port x = if L.Padded (readPort port x) then 1 else 0 := by
  have eq (r : Address v K) : ok (Sum.elim x id ∘ tap control port r) ↔
      ∀ s, (r, s) ∉ Set.range L.portSlots → ∀ t, readPort port x (r, s) t = false := by
    change (∀ s, (¬∃ j, (Sum.elim x id ∘ control r.1) (j, r.2, s) = true) →
      ∀ t, readPort port x (r, s) t = false) ↔ _
    simp only [hm, used]
  simp only [zeroTest, Finset.prod_boole, Finset.mem_univ, forall_const, eq]
  congr 1
  exact propext ⟨fun h i => h i.1 i.2, fun h r s => h (r, s)⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end

/-!
# Uniform scale choices for the exact batch descent

The number of terminal blocks and the maximum number of rows in a
bin have independent polynomial bounds in the desired width saving.
Only after fixing these bounds do we choose the fraction of the
address length available for a bundle.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Packing Filter

variable (F : Type) [Field F]

structure Recipe where
  b : ℕ
  n : ℕ
  e : ℕ
  H : ℕ
  C : ℝ
  beats : ∀ j : ℕ, 0 < j → Reduction F 8 3 (b ^ j) (n * j) (e ^ j) (H ^ j) ((1 / 2) ^ j) C

theorem recipe (h : ¬Tagged.Hard F) : Nonempty (Recipe F) := by
  obtain ⟨b, n, e, H, C, _, _, beat⟩ := Packing.beats (.inr h) 8 (by decide)
  exact ⟨⟨b, n, e, H, C, fun j hj => beat j hj F⟩⟩

namespace Recipe
variable {F} (P : Recipe F)

theorem b_pos : 0 < P.b := by simpa using (P.beats 1 Nat.one_pos).unit
theorem H_pos : 0 < P.H := by simpa using (P.beats 1 Nat.one_pos).overhead

def group (j : ℕ) := (P.H + 5) * j
def blocks (R j : ℕ) := R * j + (P.n * j) * P.group j
def batch (R j z : ℕ) := 2 ^ (P.blocks R j) * (P.b ^ j * z)

theorem group_room (j : ℕ) (hj : 1 ≤ j) :
    12 * (P.H ^ j : ℕ) ≤ (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ (P.group j) := by
  have hp : (P.H : ℝ) ≤ (2 : ℝ) ^ P.H := by exact_mod_cast (Nat.lt_two_pow_self (n := P.H)).le
  rw [group, pow_mul, ← mul_pow, pow_add, Nat.cast_pow]
  calc
    _ ≤ (12 : ℝ) ^ j * ((2 : ℝ) ^ P.H) ^ j := by
      gcongr
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 12) hj
    _ = (12 * (2 : ℝ) ^ P.H) ^ j := (mul_pow _ _ _).symm
    _ ≤ _ := by apply pow_le_pow_left₀ (by positivity); linarith [pow_pos (by norm_num : (0 : ℝ) < 2) P.H]

theorem expand {a b : Wire} (G : Diagram F a b) (hg : G.Trivalent)
    {M j z : ℕ} (hsize : Fintype.card G.V + wd a + wd b ≤ M)
    (hj : 1 ≤ j) (hz : 0 < z) (R : ℕ) :
    let h := P.blocks R j
    let u := P.b ^ j * z
    (Stack.start G h u).Expands (P.H ^ j * (5 * 2 ^ h * M * P.b ^ j)) (fun Q : HostNet F _ (R * j) z =>
      Q.seats ≤ P.H ^ j * (2 * M * 2 ^ h) ∧ Q.Bounded 3 (8 ^ (P.e ^ j)) ((P.H ^ j : ℕ) * (6 * (u : ℝ))) ∧
      Q.X ≤ (P.batch R j z : ℝ) * ((3 + P.C) * (1 / 2 : ℝ) ^ j * M + P.C * (wd a + wd b : ℕ)) ∧
      Q.seats ≤ P.H ^ j * (Stack.start G h u).seats ∧ Q.mass ≤ 10 * (P.H ^ j) * (P.batch R j z) * M ∧
      (∀ p, Q.past p ≤ 6 * u * (P.H ^ j) * 2 ^ (P.group j)) ∧ (Stack.start G h u).Tracks Q (P.H ^ j)) :=
  Stack.reduce (P.beats j hj) (pow_le_one₀ (by norm_num) (by norm_num)) G hg M (P.group j)
    (R * j) z hsize hz rfl le_rfl (P.group_room j hj)

private theorem power_le (b j : ℕ) : b ^ j ≤ 2 ^ (b * j) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := b)).le j

theorem parameters (R Q W B J : ℕ) (hB : 5 + Q + P.b + W ≤ B)
    {κ : ℝ} (hk : 0 < κ) :
    ∀ᶠ w : ℕ in atTop, ∃ j z : ℕ, J ≤ j ∧ 1 ≤ j ∧ 2 ^ (B * j) ≤ w ∧ w ≤ 2 ^ (2 * B * j) ∧
      0 < z ∧ 2 ^ (W * j) ∣ z ∧
      16 * (2 ^ (Q * j) * P.b ^ j) * z ≤ w ∧ w ≤ 32 * (2 ^ (Q * j) * P.b ^ j) * z ∧
      0 < P.batch R j z ∧ (P.batch R j z : ℝ) ≤ ((2 : ℝ) ^ w : ℝ) ^ κ := by
  let v := R + 2 * B + P.n * (P.H + 5)
  obtain ⟨j₀, h₀⟩ := eventually_atTop.mp (replication hk v)
  filter_upwards [scales B (max j₀ J) (by omega)] with w hw
  obtain ⟨j, hj, hj', hl, hu⟩ := hw
  have hr : 32 * (2 ^ (Q * j) * P.b ^ j) * 2 ^ (W * j) ≤ w := calc
    _ ≤ 2 ^ 5 * (2 ^ (Q * j) * 2 ^ (P.b * j)) * 2 ^ (W * j) := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 32 (Nat.mul_le_mul_left _ (power_le P.b j)))
    _ = 2 ^ (5 + (Q * j + P.b * j) + W * j) := by simp only [pow_add]
    _ ≤ 2 ^ (B * j) := Nat.pow_le_pow_right (by decide) (by nlinarith)
    _ ≤ _ := hl
  have hb := P.b_pos
  obtain ⟨z, hz, hdz, hlo, hup⟩ := fill (by positivity) (by positivity) hr
  have hd : 0 < P.batch R j z := by unfold batch; positivity
  refine ⟨j, z, (le_max_right _ _).trans hj, hj', hl, hu, hz, hdz, hlo, hup, hd, ?_⟩
  have hjw : 2 ^ j ≤ w := (Nat.pow_le_pow_right (by decide) (by nlinarith : j ≤ B * j)).trans hl
  have hwidth : P.b ^ j * z ≤ w := calc
    _ ≤ (16 * 2 ^ (Q * j)) * (P.b ^ j * z) := Nat.le_mul_of_pos_left _ (by positivity)
    _ ≤ _ := by simpa [mul_assoc] using hlo
  have hlayers : P.blocks R j + 2 * B * j ≤ v * j ^ 2 := by
    unfold blocks group v
    nlinarith only [Nat.mul_le_mul_left (R + 2 * B) (show j ≤ j ^ 2 by nlinarith)]
  have hbatch : P.batch R j z ≤ 2 ^ (v * j ^ 2) := calc
    _ ≤ 2 ^ (P.blocks R j) * 2 ^ (2 * B * j) := Nat.mul_le_mul_left _ (hwidth.trans hu)
    _ ≤ _ := by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) hlayers
  exact (show (P.batch R j z : ℝ) ≤ (2 : ℝ) ^ (v * j ^ 2) by exact_mod_cast hbatch).trans
    (h₀ j ((le_max_left _ _).trans hj) w hjw)

end Recipe
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end
