import OAI.LinearAlgebra.MatrixExponent.Packing.TetherHost
import OAI.LinearAlgebra.MatrixExponent.Packing.Occupancy
import OAI.LinearAlgebra.MatrixExponent.Spectral.Path
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import Mathlib.Tactic.Linarith

/-!
# Routing exceptional units through their two contact trees

Descend to the tip assigned to the destination, cross its unique link,
then climb to the receiving terminal. The group label stays fixed.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Detour

variable {w : ℕ} {X : Type}
local notation "L" => Nat.clog 2 w

def steps (w : ℕ) := 2 * Nat.clog 2 w + 3

private def arm (x : X) (pin : Fin w) (k : ℕ) : Hub X w :=
  if k ≤ L then .inr (x, Tree.climb pin k) else .inl x

private theorem owner_arm (x : X) (pin : Fin w) (k : ℕ) : owner (arm x pin k) = x := by
  unfold arm
  split_ifs <;> rfl

private theorem arm_inj (x : X) (pin : Fin w) {i j : ℕ} (hi : i ≤ L + 1) (hj : j ≤ L + 1)
    (he : arm x pin i = arm x pin j) : i = j := by
  unfold arm at he
  split_ifs at he with h h'
  · have eq := (Prod.mk.inj (Sum.inr.inj he)).2
    exact congrArg Fin.val (Tree.climb_injective pin (a₁ := ⟨i, by omega⟩)
      (a₂ := ⟨j, by omega⟩) eq)
  · omega

namespace Switch
variable (sw : Switch X w) {x y : X}

private theorem arm_adj [Fintype X] (x : X) (pin : Fin w) {i : ℕ} (hi : i ≤ L) :
    arm x pin (i + 1) ∈ sw.adj (arm x pin i) := by
  rcases hi.eq_or_lt with rfl | hi
  · apply sw.adj_symm
    simp [arm]
  · rw [arm, arm, ite_eq_left hi.le, ite_eq_left (by omega)]
    exact sw.adj_inner _ (Tree.climb_adj _ hi)

def path (hx : y ∈ sw.near x) (i : ℕ) : Hub X w :=
  if i ≤ L + 1 then arm x (sw.pin x ⟨y, hx⟩) (L + 1 - i)
  else arm y (sw.pin y ⟨x, sw.sym _ _ hx⟩) (i - (L + 2))

@[simp] theorem path_zero (hx : y ∈ sw.near x) : sw.path hx 0 = .inl x := by simp [path, arm]

@[simp] theorem path_last (hx : y ∈ sw.near x) : sw.path hx (steps w) = .inl y := by
  unfold path steps arm
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem path_adj [Fintype X] (hx : y ∈ sw.near x) {i : ℕ} (hi : i < steps w) :
    sw.path hx (i + 1) ∈ sw.adj (sw.path hx i) := by
  unfold steps at hi
  simp only [path]
  rcases lt_trichotomy i (L + 1) with h | rfl | h
  · rw [ite_eq_left h.le, ite_eq_left (by omega), show L + 1 - i = L + 1 - (i + 1) + 1 by omega]
    exact sw.adj_symm _ _ (sw.arm_adj _ _ (by omega))
  · simpa [arm] using sw.adj_bridge x y hx
  · rw [ite_eq_right h.not_ge, ite_eq_right (by omega), show i + 1 - (L + 2) = i - (L + 2) + 1 by omega]
    exact sw.arm_adj _ _ (by omega)

/-- The endpoint owning an intermediate station. -/
def side (w i : ℕ) := decide (Nat.clog 2 w + 1 < i)

theorem path_owner (hx : y ∈ sw.near x) (i : ℕ) :
    owner (sw.path hx i) = if side w i then y else x := by
  by_cases h : i ≤ L + 1
  · simp [path, owner_arm, side, h, not_lt.mpr h]
  · simp [path, owner_arm, side, h, lt_of_not_ge h]

theorem path_inj (hx : y ∈ sw.near x) {i j : ℕ} (hi : i ≤ steps w) (hj : j ≤ steps w)
    (hs : side w i = side w j) (he : sw.path hx i = sw.path hx j) : i = j := by
  unfold steps at hi hj
  have iff : i ≤ L + 1 ↔ j ≤ L + 1 := by
    have : L + 1 < i ↔ L + 1 < j := by simpa [side] using hs
    omega
  unfold path at he
  by_cases h : i ≤ L + 1
  · rw [ite_eq_left h, ite_eq_left (iff.mp h)] at he
    have := arm_inj _ _ (by omega) (by omega) he
    omega
  · rw [ite_eq_right h, ite_eq_right (mt iff.mpr h)] at he
    have := arm_inj _ _ (by omega) (by omega) he
    omega

variable {U G : Type} (group : U → G) (ends : U → Bool → X)
  (h : ∀ u, ends u true ∈ sw.near (ends u false))

def route (p : Fin (steps w) × U) : (G × Hub X w) × (G × Hub X w) :=
  ((group p.2, sw.path (h p.2) p.1.val), (group p.2, sw.path (h p.2) (p.1.val + 1)))

theorem route_adj [Fintype X] (p : Fin (steps w) × U) :
    (sw.route group ends h p).1.1 = (sw.route group ends h p).2.1 ∧
    (sw.route group ends h p).2.2 ∈ sw.adj (sw.route group ends h p).1.2 :=
  ⟨rfl, sw.path_adj (h p.2) p.1.isLt⟩

def rule [Fintype X] [Fintype U] [Fintype G] (K : Type) [Field K] :
    Spectral.Packet.Rule K (fun u => ((group u, Sum.inl (ends u false)), (group u, Sum.inl (ends u true))))
      (fun _ : Unit => sw.route group ends h) :=
  (Spectral.Packet.Rule.path K (fun i u => (group u, sw.path (h u) i)) (steps w)).congr
    (by simp only [path_zero, path_last]) rfl

theorem packet [Fintype X] [Fintype U] [Fintype G] (K : Type) [Field K] :
    Spectral.Packet K (fun u => ((group u, Sum.inl (ends u false)), (group u, Sum.inl (ends u true))))
      (fun _ : Unit => sw.route group ends h) :=
  (sw.rule group ends h K).packet

open scoped Classical

/-- Each station on an arm is visited at most once. Count both wire
incidences at a visit, even when both ends have the same owner. -/
theorem route_degree [Fintype U] (z : G × Hub X w) :
    degree (sw.route group ends h) z ≤ 2 *
      degree (fun u => ((group u, ends u false), (group u, ends u true))) (z.1, owner z.2) := by
  let v := (z.1, owner z.2)
  let f (u : U) (s : Bool) := (group u, ends u s)
  let k := degree (fun u => (f u false, f u true)) v
  have each (n : ℕ) (hn : n ≤ 1) :
      Fintype.card {p : Fin (steps w) × U //
        (group p.2, sw.path (h p.2) (p.1.val + n)) = z} ≤ k := by
    let S := {p : Fin (steps w) × U // (group p.2, sw.path (h p.2) (p.1.val + n)) = z}
    let T := {s : U × Bool // f s.1 s.2 = v}
    have hv (p : S) : f p.val.2 (side w (p.val.1.val + n)) = v := by
      unfold v
      refine Eq.trans ?_ (congrArg (fun a => (a.1, owner a.2)) p.property)
      simp only [path_owner]
      cases side w (p.val.1.val + n) <;> rfl
    let index (p : S) : T := ⟨(p.val.2, side w (p.val.1.val + n)), hv p⟩
    have hi : Function.Injective index := by
      rintro ⟨⟨i, u⟩, hu⟩ ⟨⟨j, u'⟩, hu'⟩ e
      obtain ⟨he, hs⟩ := Prod.mk.inj (congrArg Subtype.val e)
      change u = u' at he
      subst u'
      have t := congrArg Prod.snd (hu.trans hu'.symm)
      have ht : i.val + n = j.val + n := sw.path_inj (h u) (by omega) (by omega) hs t
      have : i = j := Fin.ext (by omega)
      subst j
      rfl
    have hk : Fintype.card T = k := by
      simp only [T, k, degree, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
        Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib]
      exact add_comm _ _
    exact (Fintype.card_le_of_injective index hi).trans_eq hk
  rw [two_mul]
  unfold degree
  convert! Nat.add_le_add (each 0 (by decide)) (each 1 (by decide)) using 1
  congr! 3

end Switch
end OAI.LinearAlgebra.MatrixExponent.Packing.Detour
end

/-!
# Routing tethers between frozen members and the core

A short splitting tree may carry the whole frozen charge. The long
addressing trees carry only the load of a single outlet or core endpoint.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Tether
open scoped Classical
open Finset

variable {V G I : Type} {r s w : ℕ} (sw : Detour.Switch (End V r s) w)

/-- Each tether bit has its own index, even when many bits take one route. -/
structure Plan (G I : Type) where
  group : I → G
  dst : I → V
  src : I → V × Fin r
  pin : I → Fin s
  ok : ∀ i, Sum.inr (src i, Tree.tip (pin i)) ∈ sw.near (.inl (dst i))

namespace Plan
variable {sw} (P : Plan sw G I)

abbrev Wire (s w : ℕ) (I : Type) := (Fin (Detour.steps w) × I) ⊕ (Fin (Nat.clog 2 s) × I)

def ends (i : I) (t : Bool) : End V r s :=
  if t then .inr (P.src i, Tree.tip (P.pin i)) else .inl (P.dst i)

def terminal (i : I) : G × Host V r s w := (P.group i, core (P.dst i))
def frozen (i : I) : G × Host V r s w := (P.group i, member (P.src i))
def climb (k : ℕ) (i : I) : G × Host V r s w :=
  (P.group i, .inl (.inr (P.src i, Tree.climb (P.pin i) k)))

def cold := sw.route P.group P.ends P.ok
def hot (q : Fin (Nat.clog 2 s) × I) := (P.climb q.1.val q.2, P.climb (q.1.val + 1) q.2)
def supply := Sum.elim P.cold P.hot

variable [Fintype V]

theorem support (C : V → Finset V) (e : Wire s w I) :
    (P.supply e).1.1 = (P.supply e).2.1 ∧ (P.supply e).2.2 ∈ adj sw C (P.supply e).1.2 := by
  cases e with
  | inl e => exact ⟨rfl, mem_union_left _ (sw.route_adj P.group P.ends P.ok e).2⟩
  | inr e => exact ⟨rfl, branch_adj sw C (P.src e.2) (Tree.climb_adj (P.pin e.2) e.1.isLt)⟩

variable [Fintype I] [Fintype G]

theorem packet (F : Type) [Field F] :
    Spectral.Packet F (fun i => (P.terminal i, P.frozen i)) (fun _ : Unit => P.supply) := by
  have hc := sw.packet P.group P.ends P.ok F
  have hh := Spectral.Packet.path F P.climb (Nat.clog 2 s)
  have h : Spectral.Packet F (fun i => ((P.group i, Sum.inl (P.ends i true)), P.frozen i))
      (fun _ : Unit => P.hot) := by
    unfold frozen member hot
    simpa only [climb, ends, ite_true, Tree.climb_zero, Tree.climb_top] using hh
  exact hc.series h

theorem cardinality : Fintype.card (Wire s w I) =
    (Detour.steps w + Nat.clog 2 s) * Fintype.card I := by simp [Wire, add_mul]

end Plan
end OAI.LinearAlgebra.MatrixExponent.Packing.Tether
end

/-! # Squared arity on the short splitting trees -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V G I T : Type} [Fintype I]

private theorem sum_fiber_card [Fintype T] (f : I → T) :
    ∑ i, Fintype.card {j // f j = f i} = ∑ t, (Fintype.card {j // f j = t}) ^ 2 := by
  let n t := Fintype.card {j // f j = t}
  change ∑ i, n (f i) = ∑ t, n t ^ 2
  rw [← Fintype.sum_fiberwise f]
  apply sum_congr rfl
  intro t _
  have he (i : {i // f i = t}) : n (f i.val) = n t := congrArg n i.property
  simp only [he, sum_const, card_univ, Nat.nsmul_eq_mul, pow_two]
  rfl

namespace Tether.Plan
variable {r s w : ℕ} {sw : Detour.Switch (End V r s) w}
  (P : Plan sw G I) (f : I → T)
  (sep : ∀ i j, P.group i = P.group j → P.src i = P.src j → f i = f j)

include sep

/-- All paths visiting a vertex of a splitting tree come from one
frozen tensor. Each contributes at most two incidences there. -/
theorem hot_at (i : I) (k : ℕ) :
    degree P.hot (P.climb k i) ≤ 2 * Fintype.card {j // f j = f i} := by
  have once (n : ℕ) (hn : n ≤ 1) :
      Fintype.card {e : Fin (Nat.clog 2 s) × I // P.climb (e.1.val + n) e.2 = P.climb k i}
        ≤ Fintype.card {j // f j = f i} := by
    let A := {e : Fin (Nat.clog 2 s) × I // P.climb (e.1.val + n) e.2 = P.climb k i}
    have hlabel (a : A) : f a.val.2 = f i := by
      have he := a.property
      simp only [climb, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at he
      exact sep _ _ he.1 he.2.1
    let send (a : A) : {j // f j = f i} := ⟨a.val.2, hlabel a⟩
    apply Fintype.card_le_of_injective send
    rintro ⟨⟨a, j⟩, ha⟩ ⟨⟨b, l⟩, hb⟩ he
    have eq : j = l := congrArg Subtype.val he
    subst l
    have hc := ha.trans hb.symm
    simp only [climb, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, true_and] at hc
    have e := Tree.climb_injective (P.pin j) (a₁ := ⟨a.val + n, by omega⟩)
      (a₂ := ⟨b.val + n, by omega⟩) hc
    have : a = b := Fin.ext (Nat.add_right_cancel (congrArg Fin.val e))
    subst b
    rfl
  rw [two_mul]
  unfold degree
  convert! Nat.add_le_add (once 0 (by decide)) (once 1 le_rfl) using 1

variable [Fintype V] [Fintype G] [Fintype T]

/-- Only the short splitting-tree depth multiplies the frozen square
budget. It is independent of the full host degree. -/
theorem hot_squares :
    ∑ z, (degree P.hot z) ^ 2 ≤ 4 * Nat.clog 2 s * ∑ t, (Fintype.card {i // f i = t}) ^ 2 := by
  simp_rw [pow_two (degree P.hot _)]
  rw [weighted_degree, Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _k : Fin (Nat.clog 2 s), ∑ i, 4 * Fintype.card {j // f j = f i} := by
      refine sum_le_sum fun k _ => sum_le_sum fun i _ => ?_
      have := P.hot_at f sep i k.val
      have := P.hot_at f sep i (k.val + 1)
      change degree P.hot (P.climb k.val i) + degree P.hot (P.climb (k.val + 1) i) ≤ _
      omega
    _ = _ := by rw [← mul_sum, sum_fiber_card]; simp [mul_assoc, mul_left_comm]

omit [Fintype V] [Fintype G] [Fintype T] in
theorem hot_max (B : ℝ) (hb : 0 ≤ B) (hB : ∀ t, Fintype.card {j // f j = t} ≤ B)
    (z : G × Host V r s w) : degree P.hot z ≤ 2 * B := by
  by_cases hz : ∃ i k, P.climb k i = z
  · obtain ⟨i, k, rfl⟩ := hz
    have hd : (degree P.hot (P.climb k i) : ℝ) ≤ 2 * Fintype.card {j // f j = f i} := by
      exact_mod_cast P.hot_at f sep i k
    exact hd.trans (mul_le_mul_of_nonneg_left (hB _) (by norm_num))
  · push Not at hz
    simp [degree_sum, arityCost, hot, hz, hb]

omit sep [Fintype V] [Fintype G] [Fintype T] in
/-- A single outlet serves a single core destination. Thus both sides
of any cold route satisfy the same core load bound. -/
theorem cold_max (B : ℝ) (hb : 0 ≤ B)
    (dst : ∀ g v, Fintype.card {i // P.group i = g ∧ P.dst i = v} ≤ B)
    (dest : ∀ i j, P.group i = P.group j → P.src i = P.src j → P.pin i = P.pin j → P.dst i = P.dst j)
    (z : G × Host V r s w) : degree P.cold z ≤ 2 * B := by
  let a i := ((P.group i, P.ends i false), (P.group i, P.ends i true))
  have bound (g : G) (v : End V r s) : degree a (g, v) ≤ B := by
    cases v with
    | inl v =>
      simpa [degree_sum, arityCost, a, ends, sum_boole, Fintype.card_subtype] using dst g v
    | inr v =>
      by_cases he : ∃ i, P.group i = g ∧ (P.src i, Tree.tip (P.pin i)) = v
      · obtain ⟨i, hi, hv⟩ := he
        have hd : degree a (g, .inr v) ≤ Fintype.card {j // P.group j = g ∧ P.dst j = P.dst i} := by
          rw [degree_sum, Fintype.card_subtype, card_eq_sum_ones, sum_filter]
          refine sum_le_sum fun j _ => ?_
          by_cases hj : P.group j = g ∧ (P.src j, Tree.tip (P.pin j)) = v
          · obtain ⟨e, p⟩ := Prod.mk.inj (hj.2.trans hv.symm)
            have := dest j i (hj.1.trans hi.symm) e (Tree.tip_injective p)
            simp [arityCost, a, ends, hj.1, hj.2, this]
          · simp [arityCost, a, ends, hj]
        exact (Nat.cast_le.mpr hd).trans (dst _ _)
      · have hn (i : I) : ¬(P.group i = g ∧ (P.src i, Tree.tip (P.pin i)) = v) :=
          fun h => he ⟨i, h⟩
        simp [degree_sum, arityCost, a, ends, hn, hb]
  have h : (degree P.cold z : ℝ) ≤ 2 * degree a (z.1, Detour.owner z.2) := by
    exact_mod_cast sw.route_degree P.group P.ends P.ok z
  exact h.trans (mul_le_mul_of_nonneg_left (bound _ _) (by norm_num))

end Tether.Plan
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Indexing frozen members and tether outlets

A positive load floor and a bound on the total load at a site give a
bound on the required slots. One outlet per distinct core destination
suffices. Thus a group of parallel bits is never split.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Tether
open Finset
open scoped Classical

variable {I T V : Type} [Fintype I]

/-- Number the occupants of each location without conflicts. -/
theorem number (loc : I → V) (l : I → ℝ) (b : ℝ) (hb : 0 < b)
    (lo : ∀ i, b ≤ l i) (r : ℕ) (hi : ∀ v, push loc l v ≤ r * b) :
    ∃ t : I → Fin r, Function.Injective (fun i => (loc i, t i)) := by
  have slots (v : V) : Nonempty ({i // loc i = v} ↪ Fin r) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin, ← Nat.cast_le (α := ℝ)]
    apply le_of_mul_le_mul_right _ hb
    calc
      _ = push loc (fun _ => b) v := by
        rw [push, ← sum_filter, sum_const, nsmul_eq_mul, Fintype.card_subtype]
      _ ≤ push loc l v := push_le_push loc lo v
      _ ≤ _ := hi v
  let p := fun v => Classical.choice (slots v)
  let t i := p (loc i) ⟨i, rfl⟩
  have aux i v (he : loc i = v) : t i = p v ⟨i, he⟩ := by subst v; rfl
  refine ⟨t, fun i j h => ?_⟩
  obtain ⟨e, h⟩ := Prod.mk.inj h
  rw [aux i _ e, aux j _ rfl] at h
  exact congrArg Subtype.val ((p _).injective h)

/-- Bits of a frozen member have the same outlet exactly when they
have the same core destination. -/
theorem outlets (f : I → T) (v : I → V) (b : ℝ) (hb : 0 < b)
    (lo : ∀ i, b ≤ Fintype.card {j // f j = f i ∧ v j = v i})
    (s : ℕ) (hi : ∀ t, Fintype.card {i // f i = t} ≤ s * b) :
    ∃ pin : I → Fin s, ∀ i j, f i = f j → (pin i = pin j ↔ v i = v j) := by
  let A := Set.range (fun i => (f i, v i))
  let e (i : I) : A := ⟨(f i, v i), i, rfl⟩
  let wt := push e (fun _ => 1)
  let owner (p : A) := p.val.1
  have hw (p : A) : b ≤ wt p := by
    obtain ⟨i, hi⟩ := p.property
    have he : e i = p := Subtype.ext hi
    rw [← he]
    have eq (j : I) : e j = e i ↔ f j = f i ∧ v j = v i := by
      rw [Subtype.ext_iff]
      simp only [e, Prod.mk.injEq]
    simpa only [wt, push, eq, sum_boole, Fintype.card_subtype] using lo i
  have cap t : push owner wt t ≤ s * b := by
    unfold wt
    rw [push_comp]
    change push f (fun _ => 1) t ≤ _
    simpa only [push, sum_boole, Fintype.card_subtype] using hi t
  obtain ⟨p, hp⟩ := number owner wt b hb hw s cap
  refine ⟨p ∘ e, fun i j he => ⟨fun h => ?_, fun h => congrArg p (Subtype.ext (Prod.ext he h))⟩⟩
  exact congrArg (fun z : A => z.val.2) (hp (show (owner (e i), p (e i)) = _ from Prod.ext he h))

end OAI.LinearAlgebra.MatrixExponent.Packing.Tether
end

/-! # Restoring individual frozen members on the common host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
open Finset
open scoped Classical

variable {F T : Type} {x y : Wire} {h u : ℕ} {L : Fringe x y T} (G : HostNet F L h u)

def far (i : slots x ⊕ slots y) := G.units.place (portEnd G.diagram i)

/-- Parallel tether bits from one frozen tensor to a core occurrence. -/
def parallelBits (i : slots x ⊕ slots y) :=
  letI : DecidableEq (G.V × Cell h) := Classical.typeDecidableEq _
  Fintype.card {j // L.tensor j = L.tensor i ∧ G.far j = G.far i}

theorem Preserves.parallelBits {h' u' : ℕ} {Q : HostNet F L h' u'} (hq : G.Preserves Q)
    (i : slots x ⊕ slots y) : G.parallelBits i ≤ Q.parallelBits i := by
  obtain ⟨o, _, ho, _⟩ := hq
  simp only [HostNet.parallelBits, Fintype.card_subtype]
  apply card_le_card
  intro j hj
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  exact ⟨hj.1, (ho j).trans ((congrArg o hj.2).trans (ho i).symm)⟩

structure Restore (D r s : ℕ) where
  degree : ∀ v, (G.N v).card ≤ D
  slot : T → Fin r
  unique : Function.Injective (fun t => (G.park t, slot t))
  pin : slots x ⊕ slots y → Fin s
  outlet : ∀ i j, L.tensor i = L.tensor j → (pin i = pin j ↔ G.far i = G.far j)
  pins : ∀ x, ↥(Tether.near G.N r s x) ↪ Fin (Tether.width D r s) :=
    (Detour.switch (Tether.near G.N r s) (Tether.near_symm G.N G.ns)
      (Tether.near_card G.N D degree)).pin

theorem restore [Fintype T] (D r s : ℕ) (B b : ℝ) (hb : 0 < b)
    (host : G.Bounded 3 D B) (member_cap : B ≤ L.scale * (r * b))
    (charges : ∀ t, b ≤ L.charge t ∧ L.charge t ≤ s * b)
    (contacts : ∀ i, b ≤ G.parallelBits i) : Nonempty (G.Restore D r s) := by
  have upper (v : G.V × Cell h) : push G.park L.charge v ≤ r * b := by
    apply le_of_mul_le_mul_left _ L.pos
    refine le_trans ?_ ((host.2.2 v.1 v.2).trans member_cap)
    change _ ≤ (G.tetherLoad v : ℝ) + degree G.pair v * (u : ℝ) +
      L.scale * push G.park L.charge v + G.rate * G.past v
    refine le_trans ?_ (le_add_of_nonneg_right (mul_nonneg G.rate_nonneg (Nat.cast_nonneg _)))
    exact le_add_of_nonneg_left (by positivity)
  obtain ⟨p, hp⟩ := Tether.number G.park L.charge b hb (fun t => (charges t).1) r upper
  obtain ⟨pin, hit⟩ := Tether.outlets L.tensor G.far b hb contacts s
    (fun t => (L.cover t).trans (charges t).2)
  exact ⟨{ degree := host.2.1, slot := p, unique := hp, pin := pin, outlet := hit }⟩

namespace Restore
variable {G} {D r s : ℕ} (A : G.Restore D r s)
local notation "W" => Tether.width D r s

abbrev Space (_ : G.Restore D r s) := Tether.Host G.V r s W

def sw : Detour.Switch (Tether.End G.V r s) W :=
  ⟨Tether.near G.N r s, Tether.near_symm G.N G.ns, A.pins⟩

def plan : Tether.Plan A.sw (Cell h) (slots x ⊕ slots y) where
  group i := (G.far i).2
  dst i := (G.far i).1
  src i := ((G.park (L.tensor i)).1, A.slot (L.tensor i))
  pin := A.pin
  ok i := mem_image_of_mem _ (mem_product.mpr
    ⟨mem_product.mpr ⟨(G.tether i).2.2, mem_univ _⟩, mem_univ _⟩)

def toCore (z : G.V × Cell h) : Cell h × A.Space := (z.2, Tether.core z.1)

theorem core_injective : Function.Injective A.toCore := by
  intro p q he
  simp only [toCore, Tether.core, Prod.mk.injEq, Sum.inl.injEq] at he
  exact Prod.ext he.2 he.1

def toFrozen (t : T) : Cell h × A.Space :=
  ((G.park t).2, Tether.member ((G.park t).1, A.slot t))

theorem frozen_injective : Function.Injective A.toFrozen := by
  intro p q he
  simp only [toFrozen, Tether.member, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, and_true] at he
  exact A.unique (Prod.ext (Prod.ext he.2.1 he.1) he.2.2)

theorem frozen_eq (i : slots x ⊕ slots y) : A.plan.frozen i = A.toFrozen (L.tensor i) :=
  Prod.ext (G.tether i).2.1 rfl

theorem sep (i j : slots x ⊕ slots y) (hg : A.plan.group i = A.plan.group j)
    (hs : A.plan.src i = A.plan.src j) : L.tensor i = L.tensor j := by
  apply A.frozen_injective
  rw [← frozen_eq, ← frozen_eq, Tether.Plan.frozen, Tether.Plan.frozen, hg, hs]

variable [Fintype T]

omit [Fintype T] in
theorem hot_max (B : ℝ) (hB : 0 ≤ B) (hc : ∀ t, L.charge t ≤ B) (z : Cell h × A.Space) :
    Packing.degree A.plan.hot z ≤ 2 * B :=
  A.plan.hot_max L.tensor A.sep B hB (fun t => (L.cover t).trans (hc t)) z

theorem hot_squares : (∑ z, (Packing.degree A.plan.hot z : ℝ) ^ 2) ≤
    4 * Nat.clog 2 s * ∑ t, (L.charge t) ^ 2 := by
  have h := A.plan.hot_squares L.tensor A.sep
  have h' : (∑ z, (Packing.degree A.plan.hot z : ℝ) ^ 2) ≤
      4 * Nat.clog 2 s * ∑ t, (Fintype.card {i // L.tensor i = t} : ℝ) ^ 2 := by
    exact_mod_cast h
  exact h'.trans (mul_le_mul_of_nonneg_left (sum_le_sum fun t _ =>
    pow_le_pow_left₀ (Nat.cast_nonneg _) (L.cover t) 2) (by positivity))

theorem cold_max (B : ℝ) (hb : 0 ≤ B) (host : G.Bounded 3 D B) (z : Cell h × A.Space) :
    Packing.degree A.plan.cold z ≤ 2 * B := by
  apply A.plan.cold_max B hb _ _ z
  · intro i v
    have ht : (G.tetherLoad (v, i) : ℝ) ≤ B := le_trans (le_add_of_nonneg_right (by positivity))
      ((G.core_le_load v i).trans (host.2.2 v i))
    rw [tetherLoad, port_load] at ht
    simpa [plan, far, push, Prod.ext_iff, and_comm, sum_boole, Fintype.card_subtype] using ht
  · intro i j hg hs hp
    exact congrArg Prod.fst ((A.outlet i j (A.sep i j hg hs)).mp hp)

end Restore
end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
end

/-!
# Restoring the frozen border and the degree-four support

Keep the core wires and realize the tethers by one exact packet.
The orientation of each old incidence is retained. Exterior bits
are never identified, even when frozen members share a parking site.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet.Restore
open scoped Classical
open Spectral

variable {F T : Type} {a b x y : Wire} {h u D r s : ℕ}
  {L : Fringe x y T} {G : HostNet F L h u} (A : G.Restore D r s)

abbrev Wires (_ : G.Restore D r s) :=
  Tether.Plan.Wire s (Tether.width D r s) (slots x ⊕ slots y) ⊕ G.diagram.E

def owner : G.diagram.V ⊕ T → Cell h × A.Space :=
  Sum.elim (A.toCore ∘ G.units.place) A.toFrozen

def oldCore (e : G.diagram.E) :=
  (A.toCore (G.units.place (G.diagram.source e)), A.toCore (G.units.place (G.diagram.target e)))

def supply : A.Wires → (Cell h × A.Space) × (Cell h × A.Space) :=
  Sum.elim A.plan.supply A.oldCore

def adj : A.Space → Finset A.Space := Tether.adj A.sw G.C

theorem support (e : A.Wires) :
    (A.supply e).1.1 = (A.supply e).2.1 ∧ (A.supply e).2.2 ∈ A.adj (A.supply e).1.2 := by
  cases e with
  | inl e => exact A.plan.support G.C e
  | inr e =>
    simp only [supply, Sum.elim_inr, oldCore, G.units.left, G.units.right, toCore, true_and]
    exact Tether.core_adj _ _ (G.edge _)

variable [Fintype T] [Field F] (B : Border F T a b x y) (hB : L.tensor = B.tensor)

def demands (e : (B.attach G.diagram).E) :=
  (A.owner ((B.attach G.diagram).source e), A.owner ((B.attach G.diagram).target e))

include hB in
theorem packet : Packet F (A.demands B) (fun _ : Unit => A.supply) := by
  let flip : slots x ⊕ slots y → Bool := Sum.elim (fun _ => false) (fun _ => true)
  have ht := (A.plan.packet F).orient flip
  have hp := ((ht.keep A.oldCore).place (Sum.elim id id)).reindex
    (Equiv.sumComm G.diagram.E (slots x ⊕ slots y))
  convert hp using 1
  · funext e
    rcases e with e | i | j
    · rfl
    · change (A.plan.terminal (.inl i), A.toFrozen (B.tensor (.inl i))) =
        (A.plan.terminal (.inl i), A.plan.frozen (.inl i))
      rw [A.frozen_eq, hB]
    · change (A.toFrozen (B.tensor (.inr j)), A.plan.terminal (.inr j)) =
        (A.plan.frozen (.inr j), A.plan.terminal (.inr j))
      rw [A.frozen_eq, hB]
  · funext _ e
    cases e <;> rfl

omit [Field F] in
private theorem aligned :
    (B.attach G.diagram).Aligned (fun _ : Unit => A.owner) (fun _ => id) (A.demands B) :=
  fun _ _ => ⟨rfl, rfl⟩

abbrev graph : Diagram F a b :=
  (B.attach G.diagram).replaced (A.packet B hB).rule (fun _ => A.owner) (fun _ => id) ()

theorem eval : (A.graph B hB).eval = (B.attach G.diagram).eval := by
  funext x y
  simpa only [Fintype.sum_unique] using
    (B.attach G.diagram).eval_replaced (A.packet B hB).rule (fun _ => A.owner) (fun _ => id) x y

theorem supported (e : (A.graph B hB).E) :
    let p := (A.graph B hB).source e
    let q := (A.graph B hB).target e
    p.1 = q.1 ∧ q.2 ∈ A.adj p.2 := by
  obtain ⟨i, rfl⟩ := ((B.attach G.diagram).cutEdges (A.packet B hB).rule
    (fun _ => A.owner) (fun _ => id) (A.aligned B) ()).surjective e
  exact A.support i.val

theorem arity (p : Cell h × A.Space) :
    (A.graph B hB).arity p ≤ exterior (B.attach G.diagram) A.owner p + Packing.degree A.supply p :=
  (B.attach G.diagram).arity_replaced (A.packet B hB).rule (fun _ => A.owner) (fun _ => id)
    (A.aligned B) () p

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet.Restore
end

/-! # Total load and squared load after restoring bounded degree -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V W : Type} [Fintype V] {f : V → W}

private theorem push_inj (hf : Function.Injective f) (l : V → ℝ) (v : V) :
    push f l (f v) = l v := by simp [push, hf.eq_iff]

private theorem push_zero (l : V → ℝ) {w : W} (hw : w ∉ Set.range f) :
    push f l w = 0 := by
  have hn v : f v ≠ w := fun h => hw ⟨v, h⟩
  simp [push, hn]

private theorem push_sq (hf : Function.Injective f) (l : V → ℝ) (w : W) :
    (push f l w) ^ 2 = push f (fun v => (l v) ^ 2) w := by
  by_cases h : w ∈ Set.range f
  · obtain ⟨v, rfl⟩ := h
    rw [push_inj hf, push_inj hf]
  · rw [push_zero _ h, push_zero _ h]; norm_num

namespace HostNet.Restore

variable {F T : Type} [Fintype T] {a b x y : Wire} {h u D r s : ℕ}
  {L : Fringe x y T} {G : HostNet F L h u} (A : G.Restore D r s)

/-- Charge every parked member and all incident supply bits, also when
coarsening makes some of those bits internal to a site. -/
def charge (p : Cell h × A.Space) := push A.toFrozen L.charge p + Packing.degree A.supply p

theorem charge_nonneg (p : Cell h × A.Space) : 0 ≤ A.charge p :=
  add_nonneg (push_nonneg _ _ L.nonneg _) (Nat.cast_nonneg _)

theorem exterior_covers (B : Border F T a b x y)
    (cap : ∀ t, ((B.attach G.diagram).arity (.inr t) : ℝ) ≤ L.charge t)
    (p : Cell h × A.Space) : exterior (B.attach G.diagram) A.owner p ≤ push A.toFrozen L.charge p := by
  let H := B.attach G.diagram
  let f : slots a ⊕ slots b → T :=
    Sum.elim (fun i => (B.src.symm (.inl i)).1) (fun j => (B.dst.symm (.inl j)).1)
  have hf : portEnd H = Sum.inr ∘ f := by funext q; cases q <;> rfl
  have bound (t : T) : push f (fun _ => 1) t ≤ L.charge t := by
    have hi := site_arity H id (.inr t)
    rw [port_load, hf] at hi
    have bit : push f (fun _ => 1) t ≤ (H.arity (.inr t) : ℝ) := by
      rw [show (H.arity (.inr t) : ℝ) = push id (fun i => (H.arity i : ℝ)) (.inr t)
        by exact (push_inj Function.injective_id (fun i => (H.arity i : ℝ)) (.inr t)).symm, hi]
      have eq : push (id ∘ Sum.inr ∘ f) (fun _ => 1) (Sum.inr t : H.V) =
          push f (fun _ => 1) t := by simp only [push, Function.comp_apply, id_eq, Sum.inr.injEq]
      rw [eq]
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    exact bit.trans (cap t)
  change (exterior H A.owner p : ℝ) ≤ _
  rw [port_load, hf]
  change push (A.toFrozen ∘ f) (fun _ => 1) p ≤ _
  rw [← push_comp]
  exact push_le_push A.toFrozen bound p

theorem charge_covers [Field F] (B : Border F T a b x y) (he : L.tensor = B.tensor)
    (cap : ∀ t, ((B.attach G.diagram).arity (.inr t) : ℝ) ≤ L.charge t)
    (p : Cell h × A.Space) : (A.graph B he).arity p ≤ A.charge p := by
  have outside := A.exterior_covers B cap p
  have := Nat.cast_le (α := ℝ) |>.mpr (A.arity B he p)
  rw [Nat.cast_add] at this
  exact this.trans (add_le_add_left outside _)

theorem mass :
    ∑ p, A.charge p ≤ 2 * G.X +
      (1 + 2 * (Detour.steps (Tether.width D r s) + Nat.clog 2 s)) * L.Z := by
  have hc : Fintype.card G.diagram.E = G.X := by
    simp [X, Fintype.card_congr G.units.bits]
  rw [show (∑ p, A.charge p) = ∑ t, L.charge t + 2 * Fintype.card A.Wires by
    simp only [charge, sum_add_distrib, sum_push, ← Nat.cast_sum, sum_degree, Nat.cast_mul, Nat.cast_ofNat]]
  unfold Wires
  rw [Fintype.card_sum, Tether.Plan.cardinality, hc, Nat.cast_add, Nat.cast_mul, Nat.cast_add]
  have ht := mul_le_mul_of_nonneg_left L.tethers
    (show (0 : ℝ) ≤ Detour.steps (Tether.width D r s) + Nat.clog 2 s by positivity)
  have hp := L.reserve_nonneg
  unfold Fringe.Z at *
  linarith [L.reserve_nonneg]

omit [Fintype T] in
theorem core_degree (p : Cell h × A.Space) :
    (Packing.degree A.oldCore p : ℝ) = push A.toCore (fun v => (Packing.degree G.pair v : ℝ) * u) p := by
  let pair (e : G.diagram.E) := (G.units.place (G.diagram.source e), G.units.place (G.diagram.target e))
  have hh (z : G.V × Cell h) : Packing.degree pair z = Packing.degree G.pair z * u := by
    rw [← degree_bundle G.pair u z, degree_sum, degree_sum]
    exact Fintype.sum_equiv G.units.bits _ _ (fun e =>
      congrArg (arityCost z) (Prod.ext (G.units.left e) (G.units.right e)))
  change (Packing.degree (fun e => Prod.map A.toCore A.toCore (pair e)) p : ℝ) = _
  simp only [degree_map, hh, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_mul, push]

private def light (p : Cell h × A.Space) :=
  (Packing.degree A.oldCore p : ℝ) + Packing.degree A.plan.cold p

private theorem light_bound (B : ℝ) (hb : 0 ≤ B) (host : G.Bounded 3 D B)
    (p : Cell h × A.Space) : A.light p ≤ 3 * B := by
  have hc : (Packing.degree A.oldCore p : ℝ) ≤ B := by
    rw [core_degree]
    by_cases hx : p ∈ Set.range A.toCore
    · obtain ⟨⟨v, i⟩, rfl⟩ := hx
      rw [push_inj A.core_injective]
      exact le_trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
        ((G.core_le_load v i).trans (host.2.2 v i))
    · rw [push_zero _ hx]; exact hb
  unfold light
  linarith [A.cold_max B hb host p]

private theorem parts (p : Cell h × A.Space) :
    A.charge p = push A.toFrozen L.charge p + Packing.degree A.plan.hot p + A.light p := by
  simp only [charge, light, supply, Tether.Plan.supply, degree_partition, Nat.cast_add]
  ring

theorem maximum (B Q : ℝ) (hb : 0 ≤ B) (hq : 0 ≤ Q)
    (host : G.Bounded 3 D B) (hQ : ∀ t, L.charge t ≤ Q) (p : Cell h × A.Space) :
    A.charge p ≤ 3 * (B + Q) := by
  have hf : push A.toFrozen L.charge p ≤ Q := by
    by_cases h : p ∈ Set.range A.toFrozen
    · obtain ⟨t, rfl⟩ := h
      rw [push_inj A.frozen_injective]
      exact hQ _
    · rw [push_zero _ h]; exact hq
  rw [parts]
  linarith [A.hot_max Q hq hQ p, A.light_bound B hb host p]

/-- Full-degree routing contributes only a light-arity term. The large
frozen square budget is multiplied only by the short outlet depth. -/
theorem squares (B : ℝ) (hb : 0 ≤ B) (host : G.Bounded 3 D B) :
    ∑ p, (A.charge p) ^ 2 ≤ 3 * (1 + 4 * Nat.clog 2 s) * (∑ t, (L.charge t) ^ 2) +
      9 * B * ∑ p, A.charge p := by
  have point (p : Cell h × A.Space) : (A.charge p) ^ 2 ≤
      3 * ((push A.toFrozen L.charge p) ^ 2 + (Packing.degree A.plan.hot p : ℝ) ^ 2) + 9 * B * A.charge p := by
    let x := push A.toFrozen L.charge p
    let y : ℝ := Packing.degree A.plan.hot p
    let z := A.light p
    have hx : 0 ≤ x := push_nonneg _ _ L.nonneg _
    have hy : 0 ≤ y := Nat.cast_nonneg _
    have hz : 0 ≤ z := by unfold z light; positivity
    have he : A.charge p = x + y + z := A.parts p
    have ht : z ≤ 3 * B := A.light_bound B hb host p
    change (A.charge p) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2) + 9 * B * A.charge p
    rw [he]
    nlinarith only [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
      mul_nonneg hb hx, mul_nonneg hb hy, mul_le_mul_of_nonneg_right ht hz]
  have := sum_le_sum (fun p (_ : p ∈ univ) => point p)
  simp only [sum_add_distrib, ← mul_sum, push_sq A.frozen_injective, sum_push] at this
  linarith [A.hot_squares]

omit [Fintype T] in
private theorem repeated (b : ℝ) (units : b ≤ u) (contacts : ∀ i, b ≤ G.parallelBits i)
    (e : A.Wires) : b ≤ Fintype.card {i // A.supply i = A.supply e} := by
  let : DecidableEq (G.V × Cell h) := Classical.typeDecidableEq _
  rcases e with (⟨k, i⟩ | ⟨k, i⟩) | e
  · refine (contacts i).trans (Nat.cast_le.mpr ?_)
    unfold parallelBits
    let t (j : {j // L.tensor j = L.tensor i ∧ G.far j = G.far i}) :
        {e // A.supply e = A.supply (.inl (.inl (k, i)))} := ⟨.inl (.inl (k, j.val)), by
      have hh := (A.outlet _ _ j.property.1).mpr j.property.2
      simp only [supply, Tether.Plan.supply, Sum.elim_inl, Tether.Plan.cold, Detour.Switch.route,
        Tether.Plan.ends, plan, j.property.1, j.property.2, hh]⟩
    exact Fintype.card_le_of_injective t (by intro j l h; simpa [t, Subtype.ext_iff] using h)
  · refine (contacts i).trans (Nat.cast_le.mpr ?_)
    unfold parallelBits
    let t (j : {j // L.tensor j = L.tensor i ∧ G.far j = G.far i}) :
        {e // A.supply e = A.supply (.inl (.inr (k, i)))} := ⟨.inl (.inr (k, j.val)), by
      have hh := (A.outlet _ _ j.property.1).mpr j.property.2
      simp only [supply, Tether.Plan.supply, Sum.elim_inl, Sum.elim_inr, Tether.Plan.hot,
        Tether.Plan.climb, plan, j.property.1, j.property.2, hh]⟩
    exact Fintype.card_le_of_injective t (by intro j l h; simpa [t, Subtype.ext_iff] using h)
  · let t (j : Fin u) : {i // A.supply i = A.supply (.inr e)} :=
      ⟨.inr (G.units.bits.symm ((G.units.bits e).1, j)), by
        simp only [supply, Sum.elim_inr, oldCore, G.units.left, G.units.right, Equiv.apply_symm_apply]⟩
    have hi : Function.Injective t := by intro j l he; simpa [t, Subtype.ext_iff] using he
    refine units.trans (Nat.cast_le.mpr ?_)
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective t hi

/-- Unoccupied sites have zero charge. Every other site carries at
least one whole original bundle or one surviving frozen member. -/
theorem floor (b : ℝ) (units : b ≤ u) (contacts : ∀ i, b ≤ G.parallelBits i)
    (frozen : ∀ t, b ≤ L.charge t) (p : Cell h × A.Space) :
    A.charge p = 0 ∨ b ≤ A.charge p := by
  unfold charge
  by_cases hf : p ∈ Set.range A.toFrozen
  · obtain ⟨t, rfl⟩ := hf
    rw [push_inj A.frozen_injective]
    exact .inr ((frozen t).trans (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  rw [push_zero _ hf, zero_add]
  by_cases ha : ∃ e, (A.supply e).1 = p ∨ (A.supply e).2 = p
  · obtain ⟨e, he⟩ := ha
    refine .inr ((A.repeated b units contacts e).trans (Nat.cast_le.mpr ?_))
    rw [Fintype.card_subtype, card_eq_sum_ones, sum_filter, degree_sum]
    refine sum_le_sum fun i _ => ?_
    by_cases h : A.supply i = A.supply e
    · rcases he with he|he <;> simp [h, arityCost, he]
    · simp [h]
  · push Not at ha
    left
    simp [degree_sum, arityCost, (ha _).1, (ha _).2]

end HostNet.Restore
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-! # Original tether multiplicities are lower bounds after cutting -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Freeze
open scoped Classical

variable {F : Type} {a b : Wire} {G : Diagram F a b} (Z : Freeze G)

private theorem parallel_tether (i : slots Z.x ⊕ slots Z.y) (e : G.E)
    (hs : G.source e = G.source (Z.tether i)) (ht : G.target e = G.target (Z.tether i)) :
    ∃ j, Z.tether j = e ∧ Z.border.tensor j = Z.border.tensor i ∧
      portEnd Z.core j = portEnd Z.core i := by
  cases i with
  | inl i =>
    have h : Z.frozen (G.target e) := ht.symm ▸ (Z.input i).property
    obtain ⟨j, hj⟩ := Z.input.surjective ⟨e, h⟩
    have eq : Z.tether (.inl j) = e := congrArg Subtype.val hj
    exact ⟨.inl j, eq, Subtype.ext ((congrArg G.target eq).trans ht),
      Subtype.ext ((congrArg G.source eq).trans hs)⟩
  | inr i =>
    have h : Z.frozen (G.source e) := hs.symm ▸ (Z.output i).property
    obtain ⟨j, hj⟩ := Z.output.surjective ⟨e, h⟩
    have eq : Z.tether (.inr j) = e := congrArg Subtype.val hj
    exact ⟨.inr j, eq, Subtype.ext ((congrArg G.source eq).trans hs),
      Subtype.ext ((congrArg G.target eq).trans ht)⟩

namespace Frame
variable {V : Type} [Fintype V] {h u : ℕ} {Z}
    (H : Z.Frame V h) (hu : 0 < u) (hd : Z.Divisible u)
    (L : Fringe Z.x Z.y Z.Fixed) (hL : L.tensor = Z.border.tensor)

theorem host_parallel
    (hw : ∀ v w, u ∣ Fintype.card {e // G.source e = v ∧ G.target e = w})
    (i : slots Z.x ⊕ slots Z.y) : u ≤ (H.host hu hd L hL).parallelBits i := by
  let Q := H.host hu hd L hL
  let W := {e // G.source e = G.source (Z.tether i) ∧ G.target e = G.target (Z.tether i)}
  have : Nonempty W := ⟨⟨Z.tether i, rfl, rfl⟩⟩
  have lower : u ≤ Fintype.card W := Nat.le_of_dvd Fintype.card_pos (hw _ _)
  refine lower.trans ?_
  choose j he ht hc using fun e : W => Z.parallel_tether i e.val e.property.1 e.property.2
  have far (e : W) : Q.far (j e) = Q.far i :=
    congrArg (fun v : Z.Core => H.place v.val) (hc e)
  let f (e : W) : {p // L.tensor p = L.tensor i ∧ Q.far p = Q.far i} :=
    ⟨j e, by rw [hL]; exact ht e, far e⟩
  have inj : Function.Injective f := by
    intro e e' eq
    exact Subtype.ext ((he e).symm.trans
      ((congrArg (fun p => Z.tether p.val) eq).trans (he e')))
  unfold HostNet.parallelBits
  convert! Fintype.card_le_of_injective f inj using 2

end Frame
end OAI.LinearAlgebra.MatrixExponent.Packing.Freeze
end
