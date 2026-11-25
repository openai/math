import Mathlib.FieldTheory.Finiteness
import OAI.LinearAlgebra.MatrixExponent.Routing.Fixed
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryControl
import Mathlib.Logic.Equiv.Fintype

section
/-!
# Independent samples for affine partitions

A dependent tuple and one extra vector fit injectively into a coefficient
tuple and a vector tuple. Store a nonzero relation, then shift the tuple so
that evaluating this relation recovers the extra vector.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped Classical

theorem half_independent (k V I : Type) [Field k] [Fintype k]
    [AddCommGroup V] [Module k V] [Fintype V] [Fintype I] [DecidableEq I]
    (h : Fintype.card I < Module.finrank k V) :
    Fintype.card (I → V) ≤
      2 * (Finset.univ.filter (fun x : I → V => LinearIndependent k x)).card := by
  let D := {x : I → V // ¬ LinearIndependent k x}
  choose c hc hn using fun x : D => Fintype.not_linearIndependent_iff.mp x.2
  have correction (a : I → k) (ha : ∃ i, a i ≠ 0) (v : V) :
      ∃ y : I → V, ∑ i, a i • y i = v := by
    obtain ⟨j, hj⟩ := ha
    refine ⟨fun i => if i = j then (a j)⁻¹ • v else 0, ?_⟩
    simp [smul_ite, hj]
  choose! t ht using correction
  let f (p : D × V) : (I → k) × (I → V) :=
    (c p.1, p.1.val + t (c p.1) p.2)
  have recover (p : D × V) : ∑ i, (f p).1 i • (f p).2 i = p.2 := by
    simp only [f, Pi.add_apply, smul_add, Finset.sum_add_distrib, hc, ht _ (hn p.1), zero_add]
  have hinj : Function.Injective f := by
    rintro ⟨x, u⟩ ⟨y, v⟩ he
    have huv : u = v := by
      have hu := recover (x, u)
      rw [he, recover] at hu
      exact hu.symm
    subst v
    have hxy : c x = c y := congrArg Prod.fst he
    have hs := congrArg Prod.snd he
    simp only [f, hxy] at hs
    exact Prod.ext (Subtype.ext (add_right_cancel hs)) rfl
  have hb := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_prod, Fintype.card_prod] at hb
  have hd : 2 * Fintype.card (I → k) ≤ Fintype.card V := by
    rw [Fintype.card_fun, Module.card_eq_pow_finrank (K := k) (V := V)]
    calc
      _ ≤ Fintype.card k * Fintype.card k ^ Fintype.card I :=
        Nat.mul_le_mul_right _ Fintype.one_lt_card
      _ = Fintype.card k ^ (Fintype.card I + 1) := (pow_succ' _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right Fintype.card_pos h
  have hbad : 2 * Fintype.card D ≤ Fintype.card (I → V) := by
    apply Nat.le_of_mul_le_mul_right (c := Fintype.card (I → k)) _ Fintype.card_pos
    calc
      _ = Fintype.card D * (2 * Fintype.card (I → k)) := by ac_rfl
      _ ≤ Fintype.card D * Fintype.card V := Nat.mul_le_mul_left _ hd
      _ ≤ _ := hb.trans_eq (Nat.mul_comm _ _)
  rw [show Fintype.card D = _ from Fintype.card_subtype_compl _, Fintype.card_subtype] at hbad
  omega

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Replicating each request at the centers that can use it
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral Finset
open scoped Classical

variable {K S I : Type} [Field K] [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]
  {N : ℕ} (b : Market I N) (A : Finset (Tensor K S))

namespace Shape

abbrev Req (s : Shape N) := BallShape.Requests (Fin s.1.val) A

def prices (s : Shape N) (μ d M : ℕ) (x : s.Req A → ℕ) : s.2.Goods A → ℝ
  | .inl none => price μ d (x none)
  | .inl (some a) => price μ M (x (some a))
  | .inr _ => 1

end Shape

namespace Market

def localStock (z : b.Request A → ℕ) (i : I) : (b.code i).Req A → ℕ := z ∘ b.request A i

def neighbors (i : I) := (b.support i).biUnion fun x => univ.filter fun j => x ∈ b.support j

theorem count_neighbors (i : I) : (b.neighbors i).card ≤ N * N := by
  refine card_biUnion_le.trans ?_
  calc
    _ ≤ ∑ _ ∈ b.support i, N := sum_le_sum fun x _ => b.count_support x
    _ ≤ N * N := by simpa using Nat.mul_le_mul_right N (b.card_support i)

omit [Fintype I] [DecidableEq I] [DecidableEq S] in
theorem request_surj (x : b.Request A) : ∃ i t, b.request A i t = x := by
  rcases x with i | ⟨⟨_, ⟨i, v⟩, rfl⟩, j⟩
  · exact ⟨i, none, rfl⟩
  · exact ⟨i, some (v, j), rfl⟩

omit [Fintype I] [DecidableEq I] [DecidableEq S] in
theorem localStock_injective : Function.Injective (b.localStock A) := by
  intro z w h
  funext x
  obtain ⟨i, t, rfl⟩ := b.request_surj A x
  exact congrFun (congrFun h i) t

omit [Fintype I] [DecidableEq I] [DecidableEq S] in
theorem localStock_rates (z : b.Request A → ℕ) (μ d M : ℕ) (i : I) :
    b.rates A (fun x => price μ (b.cap A d M x) (z x)) ∘ b.assign A i =
      (b.code i).prices A μ d M (b.localStock A z i) := by
  funext x
  rcases x with (_ | ⟨v, j⟩) | e <;> rfl

omit [DecidableEq S] in
theorem overlap_neighbor [Nonempty S] (i j : I) (x : (b.code i).Req A) (y : (b.code j).Req A)
    (he : b.request A i x = b.request A j y) : j ∈ b.neighbors i :=
  mem_biUnion.mpr ⟨b.home A (b.request A i x), b.home_mem A i (.inl x) _ rfl,
    mem_filter.mpr ⟨mem_univ _, he.symm ▸ b.home_mem A j (.inl y) _ rfl⟩⟩

omit [Fintype I] [DecidableEq I] [DecidableEq S] in
theorem request_eq (i j : I) (x : (b.code i).Req A) (y : (b.code j).Req A) :
    b.request A i x = b.request A j y ↔
      match x, y with
      | none, none => i = j
      | some (a, k), some (c, l) => k = l ∧ ∀ s, b.name i (a s) = b.name j (c s)
      | _, _ => False := by
  cases x <;> cases y <;> simp [request, Prod.ext_iff, Subtype.ext_iff, funext_iff, and_comm]

end Market
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Unique finite descriptions of the outcomes of a policy round

Only active centers have an outcome. At each center the local prices
determine the active menu entry. Its histogram, or a unique inactive
marker, records the branch without adding multiplicity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral Finset
open scoped Classical

variable {K S I : Type} [Field K] [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]
  {N M : ℕ} {ρ : ℝ} {A : Finset (Tensor K S)} (a : Atlas N A M ρ)

namespace Atlas

abbrev Branch (s : Shape N) (m : ℕ) (q : a.menu s) :=
  ↥(histograms q.val.move.letter (m + Fintype.card q.val.move.letter))

abbrev Record (s : Shape N) (m : ℕ) := Option (Σ q : a.menu s, a.Branch s m q)

def entry (s : Shape N) (p : s.2.Goods A → ℝ) (h : a.Enabled s p) : a.menu s :=
  ⟨a.select s p h, (a.selected s p h).1⟩

def Valid (s : Shape N) (m : ℕ) (p : s.2.Goods A → ℝ) (r : a.Record s m) : Prop :=
  if h : a.Enabled s p then ∃ j, r = some ⟨a.entry s p h, j⟩ else r = none

def changeAt (s : Shape N) (m : ℕ) (r : a.Record s m) (put : Bool) (j : s.2.Goods A) : ℕ :=
  match r with
  | none => 0
  | some ⟨q, h⟩ =>
    if put then q.val.output (s.2.links A) (m + Fintype.card q.val.move.letter) h.val j
    else Stock.copies q.val.demand (q.val.move.block * m) j

end Atlas

namespace Market
variable (b : Market I N) (p : b.Request A → ℝ) (m : ℕ)

def live (i : b.active a p) : a.menu (b.code i) :=
  a.entry _ (b.rates A p ∘ b.assign A i) (mem_filter.mp i.property).2

def record (j : (b.policy a p m).choice) (i : I) : a.Record (b.code i) m :=
  if h : i ∈ b.active a p then some ⟨b.live a p ⟨i, h⟩, j ⟨i, h⟩⟩ else none

theorem record_active (j : (b.policy a p m).choice) (i : b.active a p) :
    b.record a p m j i = some ⟨b.live a p i, j i⟩ := dite_eq_left i.property

theorem record_valid (j : (b.policy a p m).choice) (i : I) :
    a.Valid (b.code i) m (b.rates A p ∘ b.assign A i) (b.record a p m j i) := by
  by_cases he : a.Enabled (b.code i) (b.rates A p ∘ b.assign A i)
  · let u : b.active a p := ⟨i, mem_filter.mpr ⟨mem_univ _, he⟩⟩
    rw [Atlas.Valid, dite_eq_left he]
    exact ⟨j u, b.record_active a p m j u⟩
  · rw [Atlas.Valid, dite_eq_right he]
    have hi : i ∉ b.active a p := fun h => he (mem_filter.mp h).2
    exact dite_eq_right hi

theorem record_injective : Function.Injective (b.record a p m) := by
  intro u v h
  funext i
  have he := congrFun h i.val
  rw [record_active, record_active] at he
  exact eq_of_heq (Sigma.mk.inj (Option.some.inj he)).2

theorem exists_record (r : ∀ i, a.Record (b.code i) m)
    (h : ∀ i, a.Valid (b.code i) m (b.rates A p ∘ b.assign A i) (r i)) :
    ∃! j, b.record a p m j = r := by
  have each (i : b.active a p) : ∃ j : (b.localMove a p m i).choice, r i = some ⟨b.live a p i, j⟩ := by
    have he := h i.val
    rw [Atlas.Valid, dite_eq_left (mem_filter.mp i.property).2] at he
    exact he
  choose j hj using each
  have he : b.record a p m j = r := by
    funext i
    by_cases hi : i ∈ b.active a p
    · exact (b.record_active a p m j ⟨i, hi⟩).trans (hj ⟨i, hi⟩).symm
    · have hv := h i
      have hn : ¬ a.Enabled (b.code i) (b.rates A p ∘ b.assign A i) :=
        fun hh => hi (mem_filter.mpr ⟨mem_univ _, hh⟩)
      rw [Atlas.Valid, dite_eq_right hn] at hv
      exact (dite_eq_right hi).trans hv.symm
  exact ⟨j, he, fun _ h => b.record_injective a p m (h.trans he.symm)⟩

end Market
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Updating a replicated stock from local records

Only the request coincidences between neighboring centers are used.
The order or naming of the global requests is immaterial.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Market
open Spectral Finset
open scoped Classical

variable {K S I : Type} [Field K] [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]
  {N M : ℕ} {ρ : ℝ} {A : Finset (Tensor K S)}
  (b : Market I N) (a : Atlas N A M ρ) (p : b.Request A → ℝ) (m : ℕ)

def sent (j : I) (r : a.Record (b.code j) m) (put : Bool) (x : b.Request A) :=
  ∑ y ∈ univ.filter (fun y => b.request A j y = x), a.changeAt (b.code j) m r put (.inl y)

omit [Fintype I] in
private theorem sent_collect (j : I) (r : a.Record (b.code j) m) (put : Bool) (x : b.Request A) :
    b.sent a m j r put x =
      Stock.collect (b.assign A j) (a.changeAt (b.code j) m r put) (.inl x) := by
  simp only [sent, Stock.collect, sum_filter]
  rw [Fintype.sum_sum_type]
  simp [assign]

theorem sent_active (j : b.active a p) (u : (b.policy a p m).choice) (put : Bool) (x : b.Request A) :
    b.sent a m j (b.record a p m u j) put x =
      if put then (b.localMove a p m j).put (u j) x else (b.localMove a p m j).take x := by
  rw [sent_collect, record_active]
  cases put <;> simp only [Bool.false_eq_true, ↓reduceIte, localMove,
    Proposal.flex, Proposal.trade, Function.comp_apply] <;> congr

theorem sent_inactive (j : I) (u : (b.policy a p m).choice) (put : Bool) (x : b.Request A)
    (hj : j ∉ b.active a p) : b.sent a m j (b.record a p m u j) put x = 0 := by
  rw [show b.record a p m u j = none from dite_eq_right hj]
  exact sum_eq_zero fun _ _ => rfl

variable [Nonempty S]

def incoming (r : ∀ i, a.Record (b.code i) m) (put : Bool) (i : I) (x : (b.code i).Req A) :=
  ∑ j ∈ b.neighbors i, b.sent a m j (r j) put (b.request A i x)

theorem incoming_eq (u : (b.policy a p m).choice) (put : Bool) (i : I) (x : (b.code i).Req A) :
    b.incoming a m (b.record a p m u) put i x =
      if put then (b.policy a p m).put u (b.request A i x)
      else (b.policy a p m).take (b.request A i x) := by
  let f j := b.sent a m j (b.record a p m u j) put (b.request A i x)
  change (∑ j ∈ b.neighbors i, f j) = _
  calc
    _ = ∑ j, f j := sum_subset (subset_univ _) fun j _ hj =>
      sum_eq_zero fun y hy => (hj (b.overlap_neighbor A i j x y (mem_filter.mp hy).2.symm)).elim
    _ = ∑ j ∈ b.active a p, f j :=
      (sum_subset (subset_univ _) fun j _ hj => b.sent_inactive a p m j u put _ hj).symm
    _ = ∑ j : b.active a p, f j := (sum_coe_sort _ _).symm
    _ = _ := by
      simp only [f, sent_active]
      cases put <;> rfl

def localNext (r : ∀ i, a.Record (b.code i) m) (i : I)
    (v : (b.code i).Req A → ℕ) (x : (b.code i).Req A) : ℕ :=
  v x - b.incoming a m r false i x + b.incoming a m r true i x + if x = none then 1 else 0

theorem localNext_eq (u : (b.policy a p m).choice) (z : b.Request A → ℕ) (i : I) :
    b.localNext a m (b.record a p m u) i (b.localStock A z i) =
      b.localStock A ((b.policy a p m).next z u + Stock.copies (b.payload A) 1) i := by
  funext x
  simp only [localNext, incoming_eq, Bool.false_eq_true, ↓reduceIte,
    localStock, Function.comp_apply, Pi.add_apply, Intervention.next]
  congr 1
  rcases x with _ | ⟨v, j⟩ <;> simp [Stock.copies, payload, request]

end OAI.LinearAlgebra.MatrixExponent.Routing.Market
end

/-!
# Checking one policy round with no spurious outcomes
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Market
open Spectral
open scoped Classical

variable {K S I : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype I] [DecidableEq I] {N M : ℕ} {ρ : ℝ} {A : Finset (Tensor K S)}
  (b : Market I N) (a : Atlas N A M ρ) (μ d m : ℕ)

abbrev stockPrice (z : b.Request A → ℕ) (x : b.Request A) := price μ (b.cap A d M x) (z x)

def Checks (v : (i : I) → (b.code i).Req A → ℕ)
    (r : ∀ i, a.Record (b.code i) m) (w : (i : I) → (b.code i).Req A → ℕ) : Prop :=
  ∀ i, a.Valid (b.code i) m ((b.code i).prices A μ d M (v i)) (r i) ∧
    w i = b.localNext a m r i (v i)

def after (z : b.Request A → ℕ) (u : (b.decision a μ d m z).choice) : b.Request A → ℕ :=
  (b.decision a μ d m z).next z u + Stock.copies (b.payload A) 1

theorem checks_iff (z : b.Request A → ℕ) (r : ∀ i, a.Record (b.code i) m)
    (w : (i : I) → (b.code i).Req A → ℕ) :
    b.Checks a μ d m (b.localStock A z) r w ↔
      ∃! u : (b.decision a μ d m z).choice,
        b.record a (b.stockPrice (M := M) μ d z) m u = r ∧ w = b.localStock A (b.after a μ d m z u) := by
  let p := b.stockPrice (M := M) μ d z
  have he (i) : b.rates A p ∘ b.assign A i =
      (b.code i).prices A μ d M (b.localStock A z i) := b.localStock_rates A z μ d M i
  constructor
  · intro h
    have hv (i) : a.Valid (b.code i) m (b.rates A p ∘ b.assign A i) (r i) := by
      rw [he]
      exact (h i).1
    obtain ⟨u, hu, hh⟩ := b.exists_record a p m r hv
    refine ⟨u, ⟨hu, funext fun i => ?_⟩, fun j hj => hh j hj.1⟩
    rw [(h i).2, ← hu]
    exact b.localNext_eq a p m u z i
  · rintro ⟨u, ⟨rfl, rfl⟩, _⟩ i
    rw [← he]
    exact ⟨b.record_valid a p m u i, (b.localNext_eq a p m u z i).symm⟩

/-- Each update introduces only boundedly many units of each type,
including the one newly injected payload bit. -/
theorem after_bound (room : a.Room m) (hm : 1 ≤ M) (hd : d ≤ M)
    (z : b.Request A → ℕ) (u : (b.decision a μ d m z).choice) (i : b.Request A) :
    b.after a μ d m z u i ≤ z i + N * (2 * a.capacity * m) + 1 := by
  let p := b.stockPrice (M := M) μ d z
  have hp (i) : p i ≤ M := by
    refine price_le.trans ?_
    cases i with
    | inl x => exact Nat.cast_le.mpr hd
    | inr x => exact le_rfl
  have he := b.local_efficient a p m room hm hp
  have h := (Intervention.parallel_bounds _ (b.local_overlap a p m) he i).2.2 u
  have hb : Stock.copies (b.payload A) 1 i ≤ 1 := by unfold Stock.copies; split <;> simp
  exact Nat.add_le_add (Nat.add_le_add (Nat.sub_le _ _) h) hb

end OAI.LinearAlgebra.MatrixExponent.Routing.Market
end

/-!
# An action-independent alphabet for one round

Only neighbor addresses and coincidence masks depend on the number
of centers. The local trade and its replay use a fixed finite table.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral Finset
open scoped Classical

variable {K S I : Type} [Field K] [Fintype S] [DecidableEq S]
  [Fintype I] [DecidableEq I] {N M : ℕ} {ρ : ℝ} {A : Finset (Tensor K S)}

abbrev Key (N : ℕ) (A : Finset (Tensor K S)) := Σ s : Shape N, s.Req A

namespace Market

variable (b : Market I N) (A : Finset (Tensor K S))

structure Ports (t : ℕ) where
  addr : Fin (2 ^ t) → I → I
  use : I → Finset (Fin (2 ^ t))
  image : ∀ i, (use i).image (fun j => addr j i) = b.neighbors i
  distinct : ∀ i, Set.InjOn (fun j => addr j i) (use i)

def mask {t : ℕ} (g : b.Ports t) (i : I) (j : Fin (2 ^ t))
    (x y : Key N A) : Bool :=
  decide (j ∈ g.use i ∧ ∃ u v, x = ⟨b.code i, u⟩ ∧ y = ⟨b.code (g.addr j i), v⟩ ∧
    b.request A i u = b.request A (g.addr j i) v)

theorem mask_test {t : ℕ} (g : b.Ports t) (i : I) (j : Fin (2 ^ t))
    (x : (b.code i).Req A) (y : (b.code (g.addr j i)).Req A) :
    b.mask A g i j ⟨_, x⟩ ⟨_, y⟩ = true ↔
      j ∈ g.use i ∧ b.request A i x = b.request A (g.addr j i) y := by
  rw [mask, decide_eq_true_eq]
  constructor
  · rintro ⟨hu, x', y', hx, hy, he⟩
    rw [eq_of_heq (Sigma.mk.inj hx).2, eq_of_heq (Sigma.mk.inj hy).2]
    exact ⟨hu, he⟩
  · exact fun h => ⟨h.1, x, y, rfl, rfl, h.2⟩

end Market

namespace Atlas
variable (a : Atlas N A M ρ) (m t R : ℕ)

abbrev Cell (s : Shape N) :=
  (s.Req A → Fin (R + 1)) × a.Record s m × (s.Req A → Fin (R + 1))

abbrev Packet := (Σ s : Shape N, a.Cell m R s) × (Fin (2 ^ t) → Key N A → Key N A → Bool)

instance : Fintype (a.Packet m t R) := by
  let _ : Fintype (Shape N) := Fintype.ofFinite _
  have _ (s : Shape N) : Finite (a.Record s m) := inferInstance
  have _ (s : Shape N) : Finite (a.Cell m R s) := inferInstance
  have _ : Finite (Key N A) := inferInstance
  exact Fintype.ofFinite _

def received (x : a.Packet m t R) (y : Fin (2 ^ t) → a.Packet m t R)
    (put : Bool) (u : x.1.1.Req A) : ℕ :=
  ∑ j, ∑ v ∈ univ.filter (fun v => x.2 j ⟨_, u⟩ ⟨(y j).1.1, v⟩ = true),
    a.changeAt (y j).1.1 m (y j).1.2.2.1 put (.inl v)

def test (μ d : ℕ) (x : a.Packet m t R) (y : Fin (2 ^ t) → a.Packet m t R) : Prop :=
  a.Valid x.1.1 m (x.1.1.prices A μ d M fun u => (x.1.2.1 u).val) x.1.2.2.1 ∧
    ∀ u, (x.1.2.2.2 u).val =
      (x.1.2.1 u).val - a.received m t R x y false u + a.received m t R x y true u +
        if u = none then 1 else 0

end Atlas
namespace Market

variable (b : Market I N) (a : Atlas N A M ρ) {m t R : ℕ} (g : b.Ports t)
  (c : (i : I) → a.Cell m R (b.code i))

def packet (i : I) : a.Packet m t R := (⟨b.code i, c i⟩, b.mask A g i)

theorem received_eq (put : Bool) (i : I) (u : (b.code i).Req A) :
    a.received m t R (b.packet a g c i) (fun j => b.packet a g c (g.addr j i)) put u =
      b.incoming a m (fun j => (c j).2.1) put i u := by
  rw [incoming, ← g.image i, sum_image (g.distinct i)]
  change (∑ j, ∑ v ∈ univ.filter (fun v => b.mask A g i j ⟨_, u⟩ ⟨b.code (g.addr j i), v⟩ = true),
    a.changeAt (b.code (g.addr j i)) m (c (g.addr j i)).2.1 put (.inl v)) = _
  simp only [mask_test]
  rw [← sum_subset (subset_univ (g.use i)) (fun j _ hj => by simp [hj])]
  refine sum_congr rfl fun j hj => ?_
  simp only [hj, true_and, sent, eq_comm]

theorem checked (μ d : ℕ) :
    (∀ i, a.test m t R μ d (b.packet a g c i) (fun j => b.packet a g c (g.addr j i))) ↔
    b.Checks a μ d m (fun i x => ((c i).1 x).val) (fun i => (c i).2.1)
      (fun i x => ((c i).2.2 x).val) := by
  simp only [Atlas.test, Checks, funext_iff, localNext]
  refine forall_congr' fun i => and_congr Iff.rfl (forall_congr' fun u => ?_)
  erw [received_eq, received_eq]
  rfl

end Market
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Packing the fixed groups for a hop

Round the common group size up to a power of two. This wastes at
most a factor of two, and allows the smaller groups to be packed
whole into dyadic groups of the prescribed capacity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Coloring
open scoped Classical

private theorem dyadic_round (n : ℕ) (hn : 0 < n) : 2 ^ (Nat.clog 2 n) ≤ n * 2 := by
  cases he : Nat.clog 2 n with
  | zero => simp; omega
  | succ k =>
    rw [pow_succ]
    exact Nat.mul_le_mul_right 2 (Nat.pow_lt_of_lt_clog (show k < Nat.clog 2 n by omega)).le

private theorem group_chart (A D : Type) [Fintype A] [Fintype D] [Nonempty D] (h b : ℕ)
    (hb : b ≤ h) (hd : Fintype.card D ≤ 2 ^ b) (ha : Fintype.card A * Fintype.card D ≤ 2 ^ (h + 1)) :
    ∃ f : A × D ↪ B (h + 2 - b) × B b, ∀ i j : A × D, i.1 = j.1 → (f i).1 = (f j).1 := by
  let t := Nat.clog 2 (Fintype.card D)
  have ht : t ≤ b := Nat.clog_le_of_le_pow hd
  have hd' : Fintype.card A * 2 ^ t ≤ 2 ^ (h + 2) := calc
    _ ≤ Fintype.card A * (Fintype.card D * 2) :=
      Nat.mul_le_mul_left _ (dyadic_round _ Fintype.card_pos)
    _ ≤ 2 ^ (h + 1) * 2 := by rw [← mul_assoc]; exact Nat.mul_le_mul_right _ ha
    _ = _ := (pow_succ _ _).symm
  obtain ⟨a⟩ : Nonempty (A ↪ B (h + 2 - b) × B (b - t)) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_prod, Fintype.card_fin, ← pow_add]
    apply Nat.le_of_mul_le_mul_right _ (Nat.two_pow_pos t)
    rwa [← pow_add, show h + 2 - b + (b - t) + t = h + 2 by omega]
  obtain ⟨d⟩ : Nonempty (D ↪ B t) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin]
    exact Nat.le_pow_clog (by decide) _
  let f : B (b - t) × B t ≃ B b := Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_fin, ← pow_add, Nat.sub_add_cancel ht])
  let g := (a.prodMap d).trans ((Equiv.prodAssoc _ _ _).toEmbedding.trans
    ((Equiv.refl _).prodCongr f).toEmbedding)
  exact ⟨g, fun _ _ he => congrArg (fun i => (a i).1) he⟩

/-- One packing works at the given height for all input permutations.
The group index is unchanged by the selected controller. -/
theorem Routes.grouping {F : Type} [Field F] {m : ℕ} (T : Routes F m)
    {g : controllers F T.embed} (hg : g ∈ T.params.core) (h b : ℕ)
    (hb : h / m + T.overhead ≤ b) (hb' : b ≤ h) :
    ∃ f : B (h + 1) ↪ B (h + 2 - b) × B b, ∀ σ i, (f ((T.action h σ).smul g i)).1 = (f i).1 := by
  obtain ⟨A, D, _, _, s, hd, hs⟩ := T.groups g hg h
  have : Nonempty D := ⟨(s (Classical.arbitrary _)).2⟩
  have ha : Fintype.card A * Fintype.card D ≤ 2 ^ (h + 1) := by
    rw [← Fintype.card_prod, ← Fintype.card_congr s]
    exact (T.size h).2.le
  obtain ⟨u, hu⟩ := group_chart A D h b hb' (hd.trans (Nat.pow_le_pow_right (by decide) hb)) ha
  obtain ⟨v⟩ : Nonempty (B (h + 1) ↪ B (h + 2 - b) × B b) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_prod, Fintype.card_fin, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair ((T.embed h).trans v) (s.toEmbedding.trans u)
    ((T.embed h).trans v).injective (s.toEmbedding.trans u).injective
  let f := v.trans p.toEmbedding
  have he (i : T.labels h) : f (T.embed h i) = u (s i) := hp i
  refine ⟨f, fun σ i => ?_⟩
  let q := g.val h (σ.viaEmbedding (T.base h))
  change (f (q.viaEmbedding (T.embed h) i)).1 = _
  by_cases hi : i ∈ Set.range (T.embed h)
  · obtain ⟨j, rfl⟩ := hi
    rw [Equiv.Perm.viaEmbedding_apply, he, he]
    exact hu _ _ (hs _ _)
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hi]

/-- Ports using the same generator retain a common group across each
hop. A group has at most the slot multiplicity times the site capacity. -/
theorem Routes.portGroup {F : Type} [Field F] {m : ℕ} (T : Routes F m)
    (h b p : ℕ) (hb : h / m + T.overhead ≤ b) (hb' : b ≤ h) (f : B p → T.params.core) :
    ∃ group : B (h + 1) × B p → ℕ,
      (∀ i, (Finset.univ.filter (fun k => group k = i)).card ≤ 2 ^ (b + p)) ∧
      ∀ σ x y i j, f i = f j → (T.action h σ).smul (f i).val x = y →
        group (x, i) = group (y, j) := by
  choose d hd using fun g : T.params.core => T.grouping g.property h b hb hb'
  let group := fun k : B (h + 1) × B p => (d (f k.2) k.1).1.val
  refine ⟨group, ?_, ?_⟩
  · intro i
    let g := fun k : B (h + 1) × B p => ((d (f k.2) k.1).2, k.2)
    have he : (Finset.univ.filter (fun k => group k = i)).card ≤
        (Finset.univ : Finset (B b × B p)).card := by
      refine Finset.card_le_card_of_injOn g (fun _ _ => Finset.mem_univ _) ?_
      rintro ⟨x, j⟩ hx ⟨y, l⟩ hy hxy
      obtain ⟨he, rfl⟩ := Prod.mk.inj hxy
      have hh := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      exact Prod.ext ((d (f j)).injective (Prod.ext (Fin.ext hh) he)) rfl
    simpa [pow_add] using he
  · intro σ x y i j he hh
    subst y
    change (d (f i) x).1.val = (d (f j) ((T.action h σ).smul (f i).val x)).1.val
    rw [← he, hd]

end OAI.LinearAlgebra.MatrixExponent.Routing
end
