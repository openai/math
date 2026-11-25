import OAI.LinearAlgebra.MatrixExponent.Diagonal.Cuts
import OAI.LinearAlgebra.MatrixExponent.Spectral.Packets
import Mathlib.Data.Sigma.Order

section
/-! # Uniformity of the two group names of a packet -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

variable {A B Z : Type} [Fintype A] [Fintype B] [Fintype Z] [DecidableEq Z]

/-- A product parametrization makes the number of points per label exact. -/
private theorem uniform (e : A ≃ Z × B) (z : Z) :
    multiplicity (fun a => (e a).1) z * Fintype.card Z = Fintype.card A := by
  have ht : multiplicity (fun a => (e a).1) z = Fintype.card B := by
    apply Fintype.card_congr
    exact {
      toFun := fun a => (e a.val).2
      invFun := fun b => ⟨e.symm (z, b), congrArg Prod.fst (e.apply_symm_apply (z, b))⟩
      left_inv := fun a => Subtype.ext (e.symm_apply_eq.mpr (Prod.ext a.2.symm rfl))
      right_inv := by intro b; simp }
  rw [ht, Fintype.card_congr e, Fintype.card_prod, mul_comm]

variable {n r d : ℕ}


theorem label_uniform (i : Fin n) (g : Fin r) :
    multiplicity (fun a : Label n r => a i) g * r = r ^ n := by
  have H := uniform (Equiv.funSplitAt i (Fin r)) g
  change multiplicity (fun a : Label n r => a i) g * _ = _ at H
  simpa using H

/-- Each of the two labels has one independently variable symbol per coordinate. -/
abbrev Key (n : ℕ) := Fin n × Bool

def symbols (n r : ℕ) : Template n r ≃ (Key n → Fin r) where
  toFun p i := group p i.1 i.2
  invFun f := (fun i => f (i, false), fun i => f (i, true))
  left_inv _ := rfl
  right_inv _ := by funext ⟨i, b⟩; cases b <;> rfl

theorem group_uniform (i : Fin n) (b : Bool) (g : Fin r) :
    multiplicity (fun p : Packet n r d => group p.1 i b) g * r =
      Fintype.card (Packet n r d) := by
  let e := (symbols n r).trans (Equiv.funSplitAt (i, b) (Fin r))
  let t := (e.prodCongr (Equiv.refl (Fin d))).trans (Equiv.prodAssoc _ _ _)
  have H := uniform t g
  change multiplicity (fun p : Packet n r d => group p.1 i b) g * _ = _ at H
  simpa only [Fintype.card_fin] using H

theorem pair_uniform (i j : Key n) (hne : j ≠ i) (g g' : Fin r) :
    multiplicity (fun p : Packet n r d => (symbols n r p.1 i, symbols n r p.1 j)) (g, g') * r ^ 2 =
      Fintype.card (Packet n r d) := by
  let e := (symbols n r).trans (Equiv.funSplitAt i (Fin r))
  let a := Equiv.funSplitAt (⟨j, hne⟩ : {u : Key n // u ≠ i}) (Fin r)
  let f := (e.trans ((Equiv.refl _).prodCongr a)).trans (Equiv.prodAssoc _ _ _).symm
  let t := (f.prodCongr (Equiv.refl (Fin d))).trans (Equiv.prodAssoc _ _ _)
  have H := uniform t (g, g')
  change multiplicity (fun p : Packet n r d => (symbols n r p.1 i, symbols n r p.1 j))
    (g, g') * _ = _ at H
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using H

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# Two coordinate assignments for overloaded groups

Keep light work at its group. Assign heavy work by a different
coordinate of its label. The bound below applies both to the reassigned
work and to each light group's contacts with heavy groups.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal
open Finset

variable {n r d : ℕ}

/-- The packet touches a heavy group at the cut and a given group
at the worker coordinate. -/
def contact (i j : Fin n) (H : Finset (Fin r)) (g : Fin r) : Finset (Packet n r d) :=
  univ.filter (fun p => (∃ s, group p.1 i s ∈ H) ∧ (∃ s, group p.1 j s = g))

private theorem contact_pair (i j : Fin n) (g e : Fin r) (b c : Bool)
    (hne : i ≠ j ∨ g ≠ e) :
    (univ.filter (fun p : Packet n r d => group p.1 i b = g ∧ group p.1 j c = e)).card * r ^ 2 ≤
      Fintype.card (Packet n r d) := by
  by_cases hpair : (j, c) = (i, b)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    have hne' := hne.resolve_left (not_ne_iff.mpr rfl)
    have he (p : Packet n r d) : ¬ (group p.1 j c = g ∧ group p.1 j c = e) :=
      fun h => hne' (h.1.symm.trans h.2)
    simp [he]
  · have he := pair_uniform (d := d) (i, b) (j, c) hpair g e
    change multiplicity (fun p : Packet n r d => (group p.1 i b, group p.1 j c)) (g, e) * r ^ 2 = _ at he
    simpa [multiplicity, Fintype.card_subtype] using he.le

theorem contact_bound (i j : Fin n) (H : Finset (Fin r)) (g : Fin r) (h : i ≠ j ∨ g ∉ H) :
    (contact (d := d) i j H g).card * r ^ 2 ≤ 4 * H.card * Fintype.card (Packet n r d) := by
  let S := H ×ˢ (univ : Finset (Bool × Bool))
  let T (a : Fin r × Bool × Bool) := univ.filter (fun p : Packet n r d =>
    group p.1 i a.2.1 = a.1 ∧ group p.1 j a.2.2 = g)
  have sub : contact (d := d) i j H g ⊆ S.biUnion T := by
    intro p hp
    obtain ⟨_, ⟨b, hb⟩, ⟨c, hc⟩⟩ := mem_filter.mp hp
    exact mem_biUnion.mpr ⟨(group p.1 i b, b, c), mem_product.mpr ⟨hb, mem_univ _⟩,
      mem_filter.mpr ⟨mem_univ _, rfl, hc⟩⟩
  calc
    _ ≤ (∑ i ∈ S, (T i).card) * r ^ 2 :=
      Nat.mul_le_mul_right _ ((card_le_card sub).trans card_biUnion_le)
    _ = ∑ i ∈ S, (T i).card * r ^ 2 := sum_mul ..
    _ ≤ ∑ _ ∈ S, Fintype.card (Packet n r d) := sum_le_sum (fun u hu => by
      apply contact_pair
      rcases h with h | h
      · exact .inl h
      · exact .inr (fun he => h (he ▸ (mem_product.mp hu).1)))
    _ = _ := by simp [S, mul_comm]

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# Bounding communication with two fixed pools of workers

A light home can afford the crossing bits of its light pairs. Packets
touching a heavy group are evaluated whole, assigning workers by a
second coordinate. Each such packet costs at most two full blocks of
slots at any one worker.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal
open Finset

variable {n r d : ℕ}

/-- Count both incidences, even if they belong to the same group. -/
def charge (i : Fin n) (q : Packet n r d → ℕ) (g : Fin r) :=
  ∑ p, ((if group p.1 i false = g then q p else 0) + (if group p.1 i true = g then q p else 0))

theorem charge_total (i : Fin n) (q : Packet n r d → ℕ) :
    ∑ g, charge i q g = 2 * ∑ p, q p := by
  unfold charge
  rw [sum_comm]
  simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true, two_mul]

def heavy (T N : ℕ) (i : Fin n) (q : Packet n r d → ℕ) :=
  univ.filter (fun g => N < T * charge i q g)

private theorem heavy_bound {C L W T N : ℕ} (hN : 0 < N)
    (hw : Fintype.card (Packet n r d) * W ≤ C * r * N) (i : Fin n) (q : Packet n r d → ℕ)
    (hs : L * ∑ p, q p ≤ 2 * Fintype.card (Packet n r d) * W) :
    (heavy T N i q).card * L ≤ 4 * T * C * r := by
  let H := heavy T N i q
  have hb : H.card * N ≤ T * ∑ g, charge i q g := by
    calc
      _ = ∑ _ ∈ H, N := by simp
      _ ≤ ∑ g ∈ H, T * charge i q g := sum_le_sum (fun g hg => (mem_filter.mp hg).2.le)
      _ ≤ ∑ g, T * charge i q g := sum_le_sum_of_subset (subset_univ _)
      _ = _ := (mul_sum ..).symm
  rw [charge_total] at hb
  apply (Nat.mul_le_mul_right_iff hN).mp
  calc
    _ = (H.card * N) * L := by unfold H; ring
    _ ≤ (T * (2*∑ p, q p)) * L := Nat.mul_le_mul_right _ hb
    _ = (2 * T) * (L * ∑ p, q p) := by ring
    _ ≤ (2 * T) * (2 * Fintype.card (Packet n r d) * W) := Nat.mul_le_mul_left _ hs
    _ = 4 * T * (Fintype.card (Packet n r d) * W) := by ring
    _ ≤ 4 * T * (C * r * N) := Nat.mul_le_mul_left _ hw
    _ = _ := by ring

/-- Bound the entire workload of each reassigned worker (`i ≠ j`)
or the work sent to heavy partners by any light home (`g ∉ H`). -/
theorem workload {C L W T N : ℕ} (hN : 0 < N) (hL : 0 < L)
    (hsave : 32 * T ^ 2 * C ^ 2 ≤ L) (hw : Fintype.card (Packet n r d) * W ≤ C * r * N)
    (i j : Fin n) (q : Packet n r d → ℕ) (hs : L * ∑ p, q p ≤ 2 * Fintype.card (Packet n r d) * W)
    (g : Fin r) (hg : i ≠ j ∨ g ∉ heavy T N i q) :
    T * (2 * W * (contact (d := d) i j (heavy T N i q) g).card) ≤ N := by
  let H := heavy T N i q
  let K := (contact (d := d) i j H g).card
  have hH : H.card * L ≤ 4 * T * C * r := heavy_bound hN hw i q hs
  have hK : K * r ^ 2 ≤ 4 * H.card * Fintype.card (Packet n r d) := contact_bound i j H g hg
  have hr : 0 < r := g.isLt |> Nat.zero_lt_of_lt
  apply (Nat.mul_le_mul_right_iff (by positivity : 0 < L * r ^ 2)).mp
  change (T * (2 * W * K)) * (L * r ^ 2) ≤ N * (L * r ^ 2)
  calc
    _ = (2 * T * W * L) * (K * r ^ 2) := by ring
    _ ≤ (2 * T * W * L) * (4 * H.card * Fintype.card (Packet n r d)) := Nat.mul_le_mul_left _ hK
    _ = 8 * T * (H.card * L) * (Fintype.card (Packet n r d) * W) := by ring
    _ ≤ 8 * T * (4 * T * C * r) * (C * r * N) := by gcongr
    _ = 32 * T ^ 2 * C ^ 2 * (N * r ^ 2) := by ring
    _ ≤ L * (N * r ^ 2) := Nat.mul_le_mul_right _ hsave
    _ = _ := by ring

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# Assigning each virtual bit to two processors

Two pools indexed by the auxiliary coordinate handle the heavy groups.
This makes the locations of the workers independent of the internal
wiring of the batch. Self-links may remain private.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Spectral
variable {n r d h : ℕ}

inductive Worker (r : ℕ) where
  | home (g : Fin r)
  | station (g : Fin r)
  | packet (g : Fin r)
  deriving DecidableEq, Fintype

structure Plan (n r d : ℕ) where
  cut : Fin n
  aux : Fin n
  groups : Finset (Fin r)
  q : Packet n r d → ℕ

namespace Plan
variable (π : Plan n r d)

def base (x : Label n r) : Worker r :=
  if x π.cut ∈ π.groups then .station (x π.aux) else .home (x π.cut)

def marked (p : Packet n r d) : Prop := ∃ s, group p.1 π.cut s ∈ π.groups
  deriving Decidable

/-- Heavy packets share both blocks of slots. Light packets share
the selector and the wire bits at the chosen cut. -/
abbrev Message (h : ℕ) (p : Packet n r d) :=
  { _m : Bool × Cube n × Fin h // π.marked p } ⊕ { _m : Fin (π.q p) // ¬π.marked p }

def sender (p : Packet n r d) : π.Message h p → Worker r
  | .inl m => π.base (corner p.1 (if m.1.1 then Cube.flip Finset.univ m.1.2.1 else m.1.2.1))
  | .inr _ => .home (group p.1 π.cut false)

def receiver (p : Packet n r d) : π.Message h p → Worker r
  | .inl _ => .packet (group p.1 π.aux false)
  | .inr _ => .home (group p.1 π.cut true)

def slotsAt (h : ℕ) (u : Worker r) (p : Packet n r d) :=
  Fintype.card {m : π.Message h p // π.sender p m = u ∨ π.receiver p m = u}

def eligible (u : Worker r) : Finset (Packet n r d) :=
  match u with
  | .home g => if g ∈ π.groups then ∅ else contact π.cut π.cut π.groups g
  | .station g | .packet g => contact π.cut π.aux π.groups g

private theorem base_mem (p : Packet n r d) (hm : π.marked p) (x : Cube n) :
    p ∈ π.eligible (π.base (corner p.1 x)) := by
  unfold base
  split_ifs with h
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm, ⟨x π.aux, rfl⟩⟩
  · simp only [eligible, h, ite_false]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm, ⟨x π.cut, rfl⟩⟩

private theorem receiver_mem (p : Packet n r d) (hm : π.marked p) :
    p ∈ π.eligible (.packet (group p.1 π.aux false)) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm, ⟨false, rfl⟩⟩

private def light (p : Packet n r d) : Worker r → ℕ
  | .home g => if g ∈ π.groups then 0 else
      (if group p.1 π.cut false = g then π.q p else 0) +
      (if group p.1 π.cut true = g then π.q p else 0)
  | _ => 0

private theorem light_le (p : Packet n r d) (hm : ¬π.marked p) (b : Bool) :
    π.q p ≤ π.light p (.home (group p.1 π.cut b)) := by
  have he : group p.1 π.cut b ∉ π.groups := fun h => hm ⟨b, h⟩
  simp only [light, he, ite_false]
  cases b <;> simp

private theorem slotsAt_le (u : Worker r) (p : Packet n r d) :
    π.slotsAt h u p ≤ π.light p u +
      if p ∈ π.eligible u then 2 * (Fintype.card (Cube n) * h) else 0 := by
  classical
  by_cases hz : π.slotsAt h u p = 0
  · rw [hz]; exact Nat.zero_le _
  have hc : π.slotsAt h u p ≤ Fintype.card (π.Message h p) := Fintype.card_subtype_le _
  obtain ⟨⟨m, hs⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hz)
  rcases m with m|m
  · have he : p ∈ π.eligible u := by
      rcases hs with rfl | rfl
      · exact π.base_mem p m.2 _
      · exact π.receiver_mem p m.2
    rw [ite_eq_left he]
    refine hc.trans (le_trans ?_ (Nat.le_add_left _ _))
    simp [Message, m.2]
  · have he : π.q p ≤ π.light p u := by
      rcases hs with rfl | rfl
      · exact π.light_le p m.2 false
      · exact π.light_le p m.2 true
    refine hc.trans (le_trans ?_ (he.trans (Nat.le_add_right _ _)))
    simp [Message, m.2]

/-- The endpoint budget for all packets, including every padded position. -/
theorem capacity {C L T N : ℕ} (hN : 0 < N) (hL : 0 < L) (hsave : 32 * T ^ 2 * C ^ 2 ≤ L)
    (hw : Fintype.card (Position n r d h) ≤ C * r * N) (hne : π.cut ≠ π.aux)
    (hH : π.groups = heavy T N π.cut π.q)
    (hs : L * ∑ p, π.q p ≤ 2 * Fintype.card (Position n r d h)) (u : Worker r) :
    T * ∑ p, π.slotsAt h u p ≤ 2 * N := by
  let W := Fintype.card (Cube n) * h
  have size : Fintype.card (Position n r d h) = Fintype.card (Packet n r d) * W := by
    simp only [Position, Fintype.card_prod, Fintype.card_fin, W]
  rw [size] at hw
  rw [size, ← mul_assoc] at hs
  have hl : T * ∑ p, π.light p u ≤ N := by
    cases u with
    | station g | packet g => simp [light]
    | home g =>
      by_cases hg : g ∈ π.groups
      · simp [light, hg]
      · simp only [light, hg, ite_false]
        change T * charge π.cut π.q g ≤ N
        simpa only [hH, heavy, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hg
  have he : T * (2 * W * (π.eligible u).card) ≤ N := by
    cases u with
    | station g | packet g =>
      simp only [eligible, hH]
      exact workload hN hL hsave hw _ _ _ hs _ (.inl hne)
    | home g =>
      simp only [eligible, hH]
      split_ifs with hg
      · simp
      · exact workload hN hL hsave hw _ _ _ hs _ (.inr hg)
  calc
    _ ≤ T * ∑ p, (π.light p u + if p ∈ π.eligible u then 2 * W else 0) :=
      Nat.mul_le_mul_left T (Finset.sum_le_sum (fun p _ => π.slotsAt_le u p))
    _ = T * (∑ p, π.light p u) + T * (2 * W * (π.eligible u).card) := by
      simp [Finset.sum_add_distrib, mul_add, mul_comm]
    _ ≤ _ := by omega

end Plan
end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-! # Adaptive packet expansion for independent copies of a diagram -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout

open Classical

variable {F : Type} [Field F] {a b : Wire} {G : Diagram F a b} {n r h B : ℕ}
variable (L : Layout G n r h)

/-- Keep the cube template and combine the batch and repetition indices. -/
def batchLoad (x : Fin B → G.End → Bool) (p : Packet n r (B * L.d)) : Block n h :=
  L.load (x (finProdFinEquiv.symm p.2).1) (p.1, (finProdFinEquiv.symm p.2).2)

theorem batchLoad_injective : Function.Injective (L.batchLoad (B := B)) := by
  intro x y he
  funext j
  apply L.load_injective
  funext p
  simpa only [batchLoad, Equiv.symm_apply_apply] using
    congrFun he (p.1, finProdFinEquiv (j, p.2))

/-- All copies may share a single coordinate choice based on all selectors.
Station and junction bits remain separate until the packet sum restores their
equality. -/
theorem eval_batch (A : Expansion F n h) (x : Fin B → Val a) (y : Fin B → Val b)
    (cut : (Packet n r (B * L.d) → A.I) → Fin n)
    (split : (Packet n r (B * L.d) → A.I) → Packet n r (B * L.d) → Bool) :
    ∏ j, G.eval (x j) (y j) =
      ∑ u : Fin B → G.End → Bool, ∑ v : Fin B → G.End → Bool,
        (∏ j, ∏ i : G.V, G.normalized.vertex (x j) (y j) (u j) (.inl i)) *
        (∏ j, ∏ i : G.Joint, G.normalized.vertex (x j) (y j) (v j) (.inr i)) *
        ∑ s, ∑ z : A.Wires s (cut s) (split s), ∏ p,
          A.value (s p) (cut s) (L.batchLoad u p) (L.batchLoad v p) (split s p) (z p) := by
  simp only [A.adaptive, L.batchLoad_injective.eq_iff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.prod_mul_distrib]
  simp_rw [L.eval A, A.full_product, L.load_injective.eq_iff, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Fintype.prod_sum _

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout
end

/-!
# Cutting a packet across one cube coordinate

Partition the supply edges into crossing edges and two sets of internal
edges. Fixing the crossing bits leaves independent contractions on the
two sides. Each supply edge is charged at exactly one coordinate.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Classical Spectral
variable {F J : Type} [Field F] [Fintype J]

namespace Cut

private abbrev Shared (κ : J → Option Bool) := {e // κ e = none}
private abbrev Own (κ : J → Option Bool) (b : Bool) := {e // κ e = some b}

private def combine (κ : J → Option Bool) :
    (Shared κ → Bool) × (Own κ false → Bool) × (Own κ true → Bool) ≃ (J → Bool) where
  toFun u e := if h : κ e = none then u.1 ⟨e, h⟩ else
    if g : κ e = some false then u.2.1 ⟨e, g⟩ else u.2.2 ⟨e, by
      cases he : κ e with
      | none => contradiction
      | some b => cases b <;> simp_all⟩
  invFun p := (fun e => p e, fun e => p e, fun e => p e)
  left_inv u := by
    ext ⟨e, he⟩ <;> simp [he]
  right_inv p := by funext e; simp

private def patch (κ : J → Option Bool) (b : Bool) (u : Shared κ → Bool)
    (v : Own κ b → Bool) (e : J) : Bool :=
  if h : κ e = none then u ⟨e, h⟩ else if h : κ e = some b then v ⟨e, h⟩ else false

def part (κ : J → Option Bool) (φ : Bool → (J → Bool) → F) (b : Bool)
    (u : Fin (Fintype.card (Shared κ)) → Bool) : F :=
  ∑ v, φ b (patch κ b (u ∘ Fintype.equivFin (Shared κ)) v)

theorem split (κ : J → Option Bool) (φ : Bool → (J → Bool) → F)
    (h : ∀ b u v, (∀ e, κ e = none ∨ κ e = some b → u e = v e) → φ b u = φ b v) :
    (∑ u, φ false u * φ true u) = ∑ z, part κ φ false z * part κ φ true z := by
  have hf (u v w) : φ false (combine κ (u, v, w)) = φ false (patch κ false u v) :=
    h _ _ _ (fun e he => by rcases he with he | he <;> simp [combine, patch, he])
  have ht (u v w) : φ true (combine κ (u, v, w)) = φ true (patch κ true u w) :=
    h _ _ _ (fun e he => by rcases he with he | he <;> simp [combine, patch, he])
  rw [← (combine κ).sum_comp, Fintype.sum_prod_type]
  let E := Equiv.arrowCongr (Fintype.equivFin (Shared κ)).symm (Equiv.refl Bool)
  rw [← E.sum_comp]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.sum_prod_type]
  simp only [hf, ht, ← Finset.mul_sum, ← Finset.sum_mul]
  rfl

end Cut

variable {n h : ℕ}

/-- Charge each supply bit to the unique coordinate changed by its edge. -/
private def region (p : Cube n × Fin n) (i : Fin n) : Option Bool :=
  if p.2 = i then none else some (p.1 i)

private theorem region_card (t : J → Cube n × Fin n) :
    ∑ i, Fintype.card {e // region (t e) i = none} = Fintype.card J := by
  simp [region, Fintype.card_subtype, Finset.sum_card_fiberwise_eq_card_filter]

private def half (i : Fin n) (g : Cube n → F) (b : Bool) : F :=
  ∏ v, if v i = b then g v else 1

private theorem prod_half (i : Fin n) (g : Cube n → F) :
    (∏ v, g v) = half i g false * half i g true := by
  rw [half, half, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  cases v i <;> simp

private theorem half_congr {i : Fin n} {g g' : Cube n → F} {b : Bool}
    (he : ∀ v, v i = b → g v = g' v) : half i g b = half i g' b := by
  apply Finset.prod_congr rfl
  intro v _
  split
  · apply he; assumption
  · rfl

theorem expand_packet {I : Type} {A : I → Type} [Fintype I] [∀ s, Fintype (A s)]
    (edges : (s : I) → A s → Cube n × Fin n)
    (packet : Spectral.Packet F (fun p : Cube n × Fin h => (p.1, Cube.flip Finset.univ p.1))
      (fun s e => ((edges s e).1, Cube.flip {(edges s e).2} (edges s e).1))) :
    ∃ E : Expansion F n h, Fintype.card E.I = Fintype.card I ∧
      ∀ s, ∃ t : I, ∑ i, E.cross s i = Fintype.card (A t) := by
  obtain ⟨f, hf, full⟩ := packet
  let κ (s : I) (i : Fin n) (e : A s) := region (edges s e) i
  let φ (s : I) (i : Fin n) (x y : Block n h) (b : Bool) (u : A s → Bool) :=
    half i (fun v => f s v x y u) b
  let E : Expansion F n h := {
    I := I
    weight := fun s x y => ∑ u, ∏ v, f s v x y u
    cross := fun s i => Fintype.card {e // κ s i e = none}
    side := fun s i b x y z => Cut.part (κ s i) (φ s i x y) b z
    full := fun x y => (full x y).symm
    split := by
      intro s i x y
      simp_rw [prod_half i]
      apply Cut.split (κ s i) (φ s i x y)
      intro b u u' he
      apply half_congr
      intro v hv
      refine hf _ _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun e hh => he e ?_)
      by_cases hc : (edges s e).2 = i
      · exact .inl (by simp [κ, region, hc])
      · right
        rcases hh with h₁ | h₂
        · change (edges s e).1 = v at h₁
          simp [κ, region, hc, h₁, hv]
        · have h₃ := (congrFun h₂ i).trans hv
          simpa [κ, region, Cube.flip, hc, Ne.symm hc] using h₃
    depends := by
      intro s i b x x' y y' z hx hy
      apply Finset.sum_congr rfl
      intro u _
      apply half_congr
      intro v hv
      apply hf
      · intro e he
        exact hx e ((congrFun he i).trans hv)
      · intro e he
        apply hy
        have h₁ := (congrFun he i).trans hv
        simp [Cube.flip] at h₁
        grind
      · intro e _; rfl
  }
  exact ⟨E, rfl, fun s => ⟨s, region_card (edges s)⟩⟩

/-- A cube of arbitrarily large dimension with a packet expansion.
The average crossing cost and the selector length can both be made
arbitrarily small compared with the number of demanded bits. -/
theorem expansion (F : Type) [Field F] (L n₀ : ℕ) (hL : 0 < L) :
    ∃ n ≥ n₀, ∃ h : ℕ, ∃ E : Expansion F n h, 0 < h ∧
      L * Nat.clog 2 (Fintype.card E.I) ≤ h ∧
      ∀ s, L * ∑ i, E.cross s i < n * Fintype.card (Cube n) * h := by
  obtain ⟨n, hn, b, C, H, hb, hc, hp⟩ := Spectral.Tensor.cube_packets F L n₀ hL
  let z := L * Nat.clog 2 (Fintype.card (Fin C × ↥H)) + 1
  have hz : 0 < z := Nat.zero_lt_succ _
  let edges (s : Fin C × ↥H) (e : Σ j : Cube n × Fin n, Fin (s.2.val j * z)) := e.1
  obtain ⟨E, he, hcost⟩ := expand_packet edges (hp z hz)
  refine ⟨n, hn, b * z, E, Nat.mul_pos hb hz, ?_, ?_⟩
  · rw [he]
    exact (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_left z hb)
  · intro s
    obtain ⟨t, ht⟩ := hcost s
    rw [ht, Fintype.card_sigma]
    simp only [Fintype.card_fin, ← Finset.sum_mul, ← mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right (hc t.2.val t.2.property) hz

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-! # Uniform communication plans for exact packet expansions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Spectral
variable {F : Type} [Field F] {n h d r : ℕ}

private theorem exists_first (hn : 2 ≤ n) (c : Fin n → ℕ) :
    ∃ i, ∀ j, c i < c j ∨ c i = c j ∧ i ≤ j := by
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun j => toLex (c j, j))
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  exact ⟨i, fun j => Prod.Lex.toLex_le_toLex.mp (hi j (Finset.mem_univ _))⟩

def first (hn : 2 ≤ n) (c : Fin n → ℕ) : Fin n := (exists_first hn c).choose

theorem first_spec (hn : 2 ≤ n) (c : Fin n → ℕ) (j : Fin n) :
    c (first hn c) < c j ∨ c (first hn c) = c j ∧ first hn c ≤ j :=
  (exists_first hn c).choose_spec j

def other (hn : 2 ≤ n) (i : Fin n) : Fin n :=
  if i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

theorem other_ne (hn : 2 ≤ n) (i : Fin n) : i ≠ other hn i := by
  unfold other
  split_ifs <;> intro h <;> have := congrArg Fin.val h <;> simp_all

namespace Expansion

variable (A : Expansion F n h)

def plan (hn : 2 ≤ n) (N : ℕ) (s : Packet n r d → A.I) : Plan n r d :=
  let i := first hn (fun j => ∑ p, A.cross (s p) j)
  let q := fun p => A.cross (s p) i + Nat.clog 2 (Fintype.card A.I)
  ⟨i, other hn i, heavy 256 N i q, q⟩

def splitPacket (hn : 2 ≤ n) (N : ℕ) (s : Packet n r d → A.I) (p : Packet n r d) : Bool :=
  decide (¬(A.plan hn N s).marked p)

private theorem plan_bound (hn : 2 ≤ n) (N C L : ℕ) (s : Packet n r d → A.I)
    (hN : 0 < N) (hL : 0 < L) (hsave : 32 * 256 ^ 2 * C ^ 2 ≤ L)
    (hw : Fintype.card (Position n r d h) ≤ C * r * N)
    (hc : ∀ s, L * ∑ i, A.cross s i ≤ n * Fintype.card (Cube n) * h)
    (hl : L * Nat.clog 2 (Fintype.card A.I) ≤ h) (u : Worker r) :
    128 * ∑ p, (A.plan hn N s).slotsAt h u p ≤ N := by
  let π := A.plan hn N s
  obtain ⟨i, hi, hm⟩ := A.coordinate (by omega) L hc hl s
  have he : ∑ p, A.cross (s p) π.cut = ∑ p, A.cross (s p) i := by
    refine le_antisymm ?_ (hi _)
    exact (first_spec hn (fun j => ∑ p, A.cross (s p) j) i).elim
      (fun h => h.le) (fun h => h.1.le)
  have hb : L * ∑ p, π.q p ≤ 2 * Fintype.card (Position n r d h) := by
    change L * (∑ p, (A.cross (s p) π.cut + Nat.clog 2 (Fintype.card A.I))) ≤ _
    rw [Finset.sum_add_distrib, he, ← Finset.sum_add_distrib]
    simpa only [Position, Fintype.card_prod, Fintype.card_fin, mul_assoc] using hm
  have := π.capacity hN hL hsave hw (other_ne hn π.cut) rfl hb u
  change 128 * ∑ p, π.slotsAt h u p ≤ N
  omega

end Expansion

/-- One exact cube identity works for every problem size and every tuple
of selectors. The packet links consume at most half of each worker's
virtual bit budget, leaving room for the literal pins. -/
theorem bounded_expansion (F : Type) [Field F] (C : ℕ) :
    ∃ n, ∃ hn : 2 ≤ n, ∃ h, ∃ A : Expansion F n h, 0 < h ∧
      ∀ (r d N : ℕ), 0 < N → Fintype.card (Position n r d h) ≤ C * r * N →
        ∀ (s : Packet n r d → A.I) (u : Worker r),
          128 * ∑ p, (A.plan hn N s).slotsAt h u p ≤ N := by
  let L := 32 * 256 ^ 2 * C ^ 2 + 1
  have hl : 0 < L := Nat.zero_lt_succ _
  obtain ⟨n, hn, h, A, hh, hs, hc⟩ := expansion F L 2 hl
  exact ⟨n, hn, h, A, hh, fun _ _ N hN hw s u =>
    A.plan_bound hn N C L s hN hl (Nat.le_succ _) hw (fun t => (hc t).le) hs u⟩

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-!
# A public report for the adaptive plan

Packets in one class have the same pair of homes and the same packet
worker. Report selector counts by class. A report gives the costs at
all candidate cuts, so one can check the minimizing rule even though
the partition into classes itself depends on the proposed cut.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Finset Classical
variable {F : Type} [Field F] {n h d r : ℕ}

abbrev Class (r : ℕ) := Fin r × Fin r × Fin r

def packetClass (hn : 2 ≤ n) (i : Fin n) (p : Packet n r d) : Class r :=
  (group p.1 i false, group p.1 i true, group p.1 (other hn i) false)

namespace Expansion

variable (A : Expansion F n h) (hn : 2 ≤ n)

/-- A class can report at most the total number of packets. -/
abbrev Report (r d : ℕ) :=
  Fin n × (Class r × A.I → Fin (Fintype.card (Packet n r d) + 1))

def counts (s : Packet n r d → A.I) (i : Fin n)
    (z : Class r × A.I) : Fin (Fintype.card (Packet n r d) + 1) :=
  ⟨multiplicity (fun p => (packetClass hn i p, s p)) z,
    Nat.lt_succ_of_le (Fintype.card_subtype_le _)⟩

def total (R : A.Report r d) (f : Class r → A.I → ℕ) :=
  ∑ z, (R.2 z).val * f z.1 z.2

theorem total_counts (s : Packet n r d → A.I) (i : Fin n) (f : Class r → A.I → ℕ) :
    A.total (i, A.counts hn s i) f = ∑ p, f (packetClass hn i p) (s p) := by
  simp only [total, counts, multiplicity, Fintype.card_subtype]
  have he (p : Packet n r d → Prop) [DecidablePred p] : (univ.filter p).card = ∑ i, if p i then 1 else 0 := by
    simp

  simp_rw [he, sum_mul, ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true]

def report (s : Packet n r d → A.I) : A.Report r d :=
  let i := first hn (fun j => ∑ p, A.cross (s p) j)
  (i, A.counts hn s i)

def checks (R : A.Report r d) (s : Packet n r d → A.I) : Prop :=
  R.1 = first hn (fun j => A.total R (fun _ t => A.cross t j)) ∧
    ∀ c, R.2 c = A.counts hn s R.1 c

/-- Every selector assignment has exactly one valid report. -/
theorem checks_iff (R : A.Report r d) (s : Packet n r d → A.I) :
    A.checks hn R s ↔ R = A.report hn s := by
  constructor
  · rcases R with ⟨i, N⟩
    rintro ⟨hi, hs⟩
    have he : N = A.counts hn s i := funext hs
    subst N
    simp only [total_counts] at hi
    exact congrArg (fun i => (i, A.counts hn s i)) hi
  · rintro rfl
    unfold checks report
    simp only [total_counts, implies_true, and_self]

def reportGroups (N : ℕ) (R : A.Report r d) : Finset (Fin r) :=
  univ.filter (fun g => N < 256 * A.total R (fun c t =>
    let w := A.cross t R.1 + Nat.clog 2 (Fintype.card A.I)
    (if c.1 = g then w else 0) + (if c.2.1 = g then w else 0)))

theorem report_groups (N : ℕ) (s : Packet n r d → A.I) :
    A.reportGroups N (A.report hn s) = (A.plan hn N s).groups := by
  simp only [reportGroups, report, total_counts, packetClass, plan, heavy, charge]
  rfl

/-- The public report has polynomially many count fields, each of
logarithmic bit length, at fixed cube and coefficient field. -/
theorem report_size :
    Fintype.card (A.Report r d) ≤
      2 ^ (Nat.clog 2 n + r ^ 3 * Fintype.card A.I * Nat.clog 2 (Fintype.card (Packet n r d) + 1)) := by
  change Fintype.card (Fin n × (Class r × A.I → Fin (Fintype.card (Packet n r d) + 1))) ≤ _
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Fintype.card_prod (Class r) A.I]
  have he : Fintype.card (Class r) = r ^ 3 := by simp [Class]; ring
  rw [he, pow_add, mul_comm (r ^ 3 * Fintype.card A.I), pow_mul (2 : ℕ)]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by decide : 1 < 2) n)
    (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) _) _)

end Expansion
end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-!
# Encoding the choices of one packet class

Once the report is fixed the total crossing width is independent of the
assignment of selectors in a class. The selectors and their crossing
bits therefore fit in a single bit string of the reported length.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

open Finset Classical
variable {F : Type} [Field F] {n h d r : ℕ} (A : Expansion F n h)

abbrev Members (hn : 2 ≤ n) (R : A.Report r d) (c : Class r) :=
  {p : Packet n r d // packetClass hn R.1 p = c}

abbrev Selectors (hn : 2 ≤ n) (R : A.Report r d) (c : Class r) :=
  {s : A.Members hn R c → A.I // ∀ z, multiplicity s z = (R.2 (c, z)).val}

def shared (N : ℕ) (R : A.Report r d) (c : Class r) : Bool :=
  decide (c.1 ∉ A.reportGroups N R ∧ c.2.1 ∉ A.reportGroups N R)

abbrev Alphabet (hn : 2 ≤ n) (N : ℕ) (R : A.Report r d) (c : Class r) :=
  Σ s : A.Selectors hn R c, A.Wires s.val R.1 (fun _ => A.shared N R c)

def classWidth (R : A.Report r d) (c : Class r) :=
  ∑ z, (R.2 (c, z)).val * (A.cross z R.1 + Nat.clog 2 (Fintype.card A.I))

variable {hn : 2 ≤ n} {R : A.Report r d} {c : Class r}

instance selectorFintype : Fintype (A.Selectors hn R c) := by
  unfold Selectors
  infer_instance

instance wiresFintype {N : ℕ} (s : A.Selectors hn R c) :
    Fintype (A.Wires s.val R.1 (fun _ => A.shared N R c)) := by
  unfold Wires
  infer_instance

instance alphabetFintype {N : ℕ} : Fintype (A.Alphabet hn N R c) := by
  unfold Alphabet
  infer_instance

theorem classWidth_spec (s : A.Selectors hn R c) :
    A.classWidth R c = ∑ p, (A.cross (s.val p) R.1 + Nat.clog 2 (Fintype.card A.I)) := by
  unfold classWidth
  simp_rw [← s.property, multiplicity, Fintype.card_subtype]
  have he (p : A.Members hn R c → Prop) [DecidablePred p] :
      (univ.filter p).card = ∑ i, if p i then 1 else 0 := by
    simp
  simp_rw [he, sum_mul, ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true]

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end

/-! # Packing one selector class in packet order -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
open Finset Classical

section Pack
variable {P : Type} [LinearOrder P] [Fintype P] (f : P → ℕ)

def packOrder : Fin (∑ p, f p) ≃o Lex (Σ p, Fin (f p)) :=
  Fintype.orderIsoFinOfCardEq _ (by simp)

variable {l : ℕ} (hl : ∑ p, f p ≤ l)

/-- Concatenate blocks in packet order, padding with zero when necessary. -/
def pack : ((p : P) → Fin (f p) → Bool) ↪ (Fin l → Bool) := by
  let e := (packOrder f).symm.toEquiv.toEmbedding.trans (Fin.castLEEmb hl)
  refine ⟨fun x => Function.extend e (fun z => x z.1 z.2) (fun _ => false), ?_⟩
  intro x y he
  funext p i
  have hh := congrFun he (e ⟨p, i⟩)
  exact ((e.injective.extend_apply (fun z => x z.1 z.2) _ ⟨p, i⟩).symm.trans hh).trans
    (e.injective.extend_apply (fun z => y z.1 z.2) _ ⟨p, i⟩)

theorem pack_at (x : (p : P) → Fin (f p) → Bool) (z : Lex (Σ p, Fin (f p))) :
    pack f hl x (Fin.castLE hl ((packOrder f).symm z)) = x z.1 z.2 := by
  let e := (packOrder f).symm.toEquiv.toEmbedding.trans (Fin.castLEEmb hl)
  exact e.injective.extend_apply (fun y => x y.1 y.2) (fun _ => false) z

end Pack

variable {F : Type} [Field F] {n h d r : ℕ} (A : Expansion F n h)

def selectorCode : A.I ↪ (Fin (Nat.clog 2 (Fintype.card A.I)) → Bool) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa using Nat.le_pow_clog (by decide : 1 < 2) (Fintype.card A.I)))

variable (hn : 2 ≤ n) (N : ℕ) (R : A.Report r d) (c : Class r)

@[instance_reducible] def memberOrder : LinearOrder (A.Members hn R c) := by
  letI : LinearOrder (Packet n r d) :=
    inferInstanceAs (LinearOrder (Lex (Lex (Lex (Label n r) × Lex (Label n r)) × Fin d)))
  exact LinearOrder.lift' Subtype.val Subtype.val_injective

attribute [local instance] memberOrder

def selectorWidth := ∑ _ : A.Members hn R c, Nat.clog 2 (Fintype.card A.I)

variable {hn R c}

theorem classWidth_split (s : A.Selectors hn R c) :
    A.classWidth R c = A.selectorWidth hn R c + ∑ p, A.cross (s.val p) R.1 := by
  rw [A.classWidth_spec s, sum_add_distrib, add_comm]
  rfl

theorem tail_bound (s : A.Selectors hn R c) :
    ∑ p, A.width (s.val p) R.1 (A.shared N R c) ≤ A.classWidth R c - A.selectorWidth hn R c := by
  rw [A.classWidth_split s, Nat.add_sub_cancel_left]
  apply sum_le_sum
  intro p _
  unfold width
  split_ifs <;> omega

def selectorPrefix (s : A.Selectors hn R c) : Fin (A.selectorWidth hn R c) → Bool :=
  pack (fun _ : A.Members hn R c => Nat.clog 2 (Fintype.card A.I)) le_rfl
    (fun p => A.selectorCode (s.val p))

def crossingSuffix (z : A.Alphabet hn N R c) : Fin (A.classWidth R c - A.selectorWidth hn R c) → Bool :=
  pack _ (A.tail_bound N z.1) z.2

def codeSplit (s : A.Selectors hn R c) :
    Fin (A.classWidth R c) ≃ Fin (A.selectorWidth hn R c + (A.classWidth R c - A.selectorWidth hn R c)) :=
  finCongr (by have := A.classWidth_split s; omega)

/-- The fixed prefix determines the lengths of the crossing blocks. -/
def alphabetCode (hn : 2 ≤ n) (N : ℕ) (R : A.Report r d) (c : Class r) :
    A.Alphabet hn N R c ↪ (Fin (A.classWidth R c) → Bool) where
  toFun z i := Fin.append (A.selectorPrefix z.1) (A.crossingSuffix N z) (A.codeSplit z.1 i)
  inj' := by
    rintro ⟨s, x⟩ ⟨s', y⟩ he
    have he' (i) :
        Fin.append (A.selectorPrefix s) (A.crossingSuffix N ⟨s, x⟩) i =
        Fin.append (A.selectorPrefix s') (A.crossingSuffix N ⟨s', y⟩) i := by
      have hi : A.codeSplit s' = A.codeSplit s := rfl
      simpa only [hi, Equiv.apply_symm_apply] using congrFun he ((A.codeSplit s).symm i)
    have hs : A.selectorPrefix s = A.selectorPrefix s' := funext fun i => by
      simpa only [Fin.append_left] using he' (Fin.castAdd _ i)
    unfold selectorPrefix at hs
    have hs' := (pack _ le_rfl).injective hs
    have : s = s' := Subtype.ext (funext fun p => A.selectorCode.injective (congrFun hs' p))
    subst s'
    have ht : A.crossingSuffix N ⟨s, x⟩ = A.crossingSuffix N ⟨s, y⟩ := funext fun i => by
      simpa only [Fin.append_right] using he' (Fin.natAdd _ i)
    have : x = y := (pack _ (A.tail_bound N s)).injective ht
    rw [this]

theorem alphabetCode_eq (z : A.Alphabet hn N R c) :
    A.alphabetCode hn N R c z =
      Fin.append (A.selectorPrefix z.1) (A.crossingSuffix N z) ∘ A.codeSplit z.1 := rfl

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end
