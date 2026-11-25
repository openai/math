import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Fintype.Pi
import OAI.LinearAlgebra.MatrixExponent.Routing.Round
import OAI.LinearAlgebra.MatrixExponent.Spectral.Place
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryPrices

/-!
# Finite observations of a pointed group action

A query compares the labels obtained by two fixed actions on the
center. A function of finitely many such comparisons is local. This
property is preserved by finite tuples and by moving the center.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open scoped Classical

structure Root (G : Type) [Group G] where
  site : Type
  [act : MulAction G site]
  center : site

attribute [instance] Root.act

namespace Root

variable {G : Type} [Group G] {X Y : Type*}

def label (r : Root G) (a : G) : r.site := a • r.center

def shift (a : G) (r : Root G) : Root G := ⟨r.site, r.label a⟩

def see (r : Root G) (a b : G) : Bool := decide (r.label a = r.label b)

def Agree (E : Finset G) (r s : Root G) : Prop :=
  ∀ a ∈ E, ∀ b ∈ E, r.see a b = s.see a b

def Local (f : Root G → X) : Prop :=
  ∃ E : Finset G, ∀ r s, Agree E r s → f r = f s

theorem Agree.mono {E D : Finset G} {r s : Root G} (h : Agree E r s) (hd : D ⊆ E) :
    Agree D r s := fun _ ha _ hb => h _ (hd ha) _ (hd hb)

theorem local_see (a b : G) : Local (fun r : Root G => r.see a b) :=
  ⟨{a, b}, fun _ _ h => h a (by simp) b (by simp)⟩

theorem Local.map {f : Root G → X} (h : Local f) (g : X → Y) : Local (g ∘ f) := by
  obtain ⟨E, hE⟩ := h
  exact ⟨E, fun r s he => congrArg g (hE r s he)⟩

theorem Local.pair {f : Root G → X} {g : Root G → Y} (h : Local f) (k : Local g) :
    Local (fun r => (f r, g r)) := by
  obtain ⟨E, hE⟩ := h
  obtain ⟨D, hD⟩ := k
  exact ⟨E ∪ D, fun r s he => Prod.ext (hE r s (he.mono Finset.subset_union_left))
    (hD r s (he.mono Finset.subset_union_right))⟩

theorem local_pi {J : Type*} [Finite J] {V : J → Type*} {f : Root G → ∀ j, V j}
    (h : ∀ j, Local (fun r => f r j)) : Local f := by
  let _ := Fintype.ofFinite J
  choose E hE using h
  exact ⟨Finset.univ.biUnion E, fun r s he => funext fun j =>
    hE j r s (he.mono (Finset.subset_biUnion_of_mem _ (Finset.mem_univ j)))⟩

theorem Local.shift {f : Root G → X} (h : Local f) (a : G) : Local (f ∘ Root.shift a) := by
  obtain ⟨E, hE⟩ := h
  refine ⟨E.image (· * a), fun r s he => hE _ _ ?_⟩
  intro x hx y hy
  have hh := he _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy)
  simp only [see, label, Root.shift, mul_smul] at hh ⊢
  exact hh

theorem Local.of_eq {f : Root G → X} {g : Root G → Y}
    (h : Local f) (hg : ∀ r s, f r = f s → g r = g s) : Local g := by
  obtain ⟨E, hE⟩ := h
  exact ⟨E, fun r s he => hg r s (hE r s he)⟩

end Root
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Local observations with an input record at each site
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open scoped Classical

structure Decor (G : Type) [Group G] (q : ℕ) extends Root G where
  mark : site → Fin (2 ^ q)

namespace Decor

variable {G : Type} [Group G] {q : ℕ} {X Y : Type*}

def Local (f : Decor G q → X) : Prop :=
  ∃ E : Finset G, ∀ x y, Root.Agree E x.toRoot y.toRoot →
    (∀ a ∈ E, x.mark (x.label a) = y.mark (y.label a)) → f x = f y

theorem local_root {f : Root G → X} (h : Root.Local f) :
    Local (fun x : Decor G q => f x.toRoot) := by
  obtain ⟨E, hE⟩ := h
  exact ⟨E, fun x y he _ => hE x.toRoot y.toRoot he⟩

theorem local_mark (a : G) : Local (fun x : Decor G q => x.mark (x.label a)) :=
  ⟨{a}, fun _ _ _ h => h a (Finset.mem_singleton_self _)⟩

theorem Local.map {f : Decor G q → X} (h : Local f) (g : X → Y) : Local (g ∘ f) := by
  obtain ⟨E, hE⟩ := h
  exact ⟨E, fun x y he hv => congrArg g (hE x y he hv)⟩

theorem Local.pair {f : Decor G q → X} {g : Decor G q → Y} (h : Local f) (k : Local g) :
    Local (fun r => (f r, g r)) := by
  obtain ⟨E, hE⟩ := h
  obtain ⟨D, hD⟩ := k
  exact ⟨E ∪ D, fun r s he hv =>
    Prod.ext (hE _ _ (he.mono Finset.subset_union_left) fun a ha => hv a (Finset.mem_union_left _ ha))
      (hD _ _ (he.mono Finset.subset_union_right) fun a ha => hv a (Finset.mem_union_right _ ha))⟩

theorem local_pi {J : Type*} [Finite J] {V : J → Type*} {f : Decor G q → ∀ j, V j}
    (h : ∀ j, Local (fun r => f r j)) : Local f := by
  let _ := Fintype.ofFinite J
  choose E hE using h
  refine ⟨Finset.univ.biUnion E, fun r s he hv => funext fun j => ?_⟩
  have hj := Finset.subset_biUnion_of_mem E (Finset.mem_univ j)
  exact hE j r s (he.mono hj) (fun a ha => hv a (hj ha))

end Decor
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Commodities local to a single ball

A shape records the endpoints of a payload and the available core
links. Extra commodities range over all placements of finitely many
tensor types. The core links are supplies only.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral
open scoped Classical

structure BallShape (B : Type) where
  src : B
  dst : B
  edges : Finset (B × B)
  flip : ∀ a b, (a, b) ∈ edges → (b, a) ∈ edges
  connected : ∀ a b, Relation.EqvGen (fun x y => (x, y) ∈ edges) a b

namespace BallShape

variable {B S K : Type} [Fintype B] [Fintype S] [Field K]

instance : Finite (BallShape B) :=
  Finite.of_injective (fun b => (b.src, b.dst, b.edges)) (by
    rintro ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ h
    cases h
    rfl)

variable [DecidableEq B] [DecidableEq S] (b : BallShape B) (A : Finset (Tensor K S))

abbrev Requests (B : Type) (A : Finset (Tensor K S)) := Option ((S → B) × Fin A.card)
abbrev Goods := Requests B A ⊕ b.edges

def tensor : b.Goods A → Tensor K B
  | .inl none => Tensor.wire K b.src b.dst 2
  | .inl (some (z, i)) => Tensor.place z (A.equivFin.symm i).val
  | .inr e => Tensor.wire K e.val.1 e.val.2 2

def rates (v : ℝ) (x : (S → B) → Tensor K S → ℝ) : b.Goods A → ℝ
  | .inl none => v
  | .inl (some (z, i)) => x z (A.equivFin.symm i).val
  | .inr _ => 1

def demands : Finset (b.Goods A) := Finset.univ.map Function.Embedding.inl
def links : Finset (b.Goods A) := Finset.univ.map Function.Embedding.inr

/-- One binary broadcast uses at most one bit on every core link. -/
theorem broadcast : (2 : Tensor K B) ≤ ∏ i ∈ b.links A, b.tensor A i := by
  let _ : Nonempty B := ⟨b.src⟩
  simp only [links, Finset.prod_map]
  apply Tensor.connected K (fun e : b.edges => e.val.1) (fun e => e.val.2)
  intro U hn hu
  by_contra! hh
  have stable (x y : B) (h : (x, y) ∈ b.edges) : x ∈ U → y ∈ U := hh ⟨(x, y), h⟩
  have eqv {x y : B} (h : Relation.EqvGen (fun x y => (x, y) ∈ b.edges) x y) :
      x ∈ U ↔ y ∈ U := by
    induction h with
    | rel x y h => exact ⟨stable x y h, stable y x (b.flip x y h)⟩
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
  obtain ⟨x, hx⟩ := hn
  exact hu (Finset.eq_univ_of_forall fun y => (eqv (b.connected x y)).mp hx)

theorem nonzero [Nonempty S] (ha : 0 ∉ A) (i : b.Goods A) : b.tensor A i ≠ 0 := by
  let _ : Nonempty B := ⟨b.src⟩
  suffices 1 ≤ b.tensor A i from fun he =>
    one_ne_zero (le_antisymm (he ▸ this) (Tensor.zero_le _))
  rcases i with (_ | ⟨z, j⟩) | e
  · exact Tensor.one_le_wire K _ _ (by decide)
  · have h : (A.equivFin.symm j).val ≠ 0 := ne_of_mem_of_not_mem (A.equivFin.symm j).property ha
    exact (Tensor.place_one z).symm.le.trans (Tensor.place_mono z (Tensor.one_le _ h))
  · exact Tensor.one_le_wire K _ _ (by decide)

theorem menu [Nonempty S] (ha : 0 ∉ A) (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ m : Finset (Proposal (b.tensor A) b.edges.card), ∃ δ : ℝ, 0 < δ ∧
      ∀ p ∈ Set.Icc 0 (fun _ => M), NearPrices (b.tensor A) (b.demands A) ρ p ∨
        ∃ q ∈ m, q.demand ⊆ b.demands A ∧ q.demand.Nonempty ∧ q.Works δ p := by
  let _ : Nonempty B := ⟨b.src⟩
  apply menu_dichotomy (b.tensor A) (b.nonzero A ha) (b.demands A) _ _ _ hρ
  intro v hv
  obtain ⟨i, j, h, h'⟩ := positive_link _ b.connected v hv
  exact ⟨.inr ⟨(i, j), h⟩, h'⟩

end BallShape
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# One finite menu for all shapes of bounded order
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral
open scoped Classical

variable {K S : Type} [Field K] [Fintype S] [DecidableEq S]

abbrev Shape (N : ℕ) := Σ n : Fin (N + 1), BallShape (Fin n.val)

namespace Shape
variable {N : ℕ} (b : Shape N) (A : Finset (Tensor K S))

abbrev Move := Proposal (b.2.tensor A) b.2.edges.card

def small (C : ℕ) (q : b.Move A) : Prop :=
  q.move.block ≤ C ∧ ∀ j, ∑ i, q.move.count j i ≤ C

end Shape

structure Atlas (N : ℕ) (A : Finset (Tensor K S)) (M ρ : ℝ) where
  menu : (b : Shape N) → Finset (b.Move A)
  margin : ℝ
  positive : 0 < margin
  capacity : ℕ
  small : ∀ b, ∀ q ∈ menu b, b.small A capacity q
  detect : ∀ b, ∀ p ∈ Set.Icc 0 (fun _ => M), NearPrices (b.2.tensor A) (b.2.demands A) ρ p ∨
    ∃ q ∈ menu b, q.demand ⊆ b.2.demands A ∧ q.demand.Nonempty ∧ q.Works margin p

theorem atlas [Nonempty S] (N : ℕ) (A : Finset (Tensor K S)) (hA : 0 ∉ A) (M : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) : Nonempty (Atlas N A M ρ) := by
  let _ : Fintype (Shape N) := Fintype.ofFinite _
  choose m d hd hm using fun b : Shape N => b.2.menu A hA M hρ
  choose c hc using fun b : Shape N => uniform_move_bound (m b)
  let s := insert 1 (Finset.univ.image d)
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨⟨m, s.min' hs, ?_, ∑ b, c b, ?_, ?_⟩⟩
  · rcases Finset.mem_insert.mp (s.min'_mem hs) with h | h
    · rw [h]; exact zero_lt_one
    · obtain ⟨b, _, e⟩ := Finset.mem_image.mp h
      exact e ▸ hd b
  · intro b q hq
    have h := Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) (Finset.mem_univ b)
    exact ⟨(hc b q hq).1.trans h, fun j => ((hc b q hq).2 j).trans h⟩
  · intro b p hp
    rcases hm b p hp with h | ⟨q, hq, h₁, h₂, h₃⟩
    · exact .inl h
    have h : d b ∈ s := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ b))
    exact .inr ⟨q, hq, h₁, h₂, h₃.mono (s.min'_le _ h)⟩

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! # Placing local trades across a larger set of sites -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Proposal

open Spectral Stock Finset

variable {K S B I E J : Type} [Field K] [Fintype S] [Fintype B] [DecidableEq S]
  [DecidableEq B] [Nonempty S] [Fintype I] [Fintype E] [Fintype J]
  [DecidableEq I] [DecidableEq E] [DecidableEq J] {T : J → Tensor K S} {H : ℝ}

/-- Demand and supply can use different numbers of blocks, provided
there is a local comparison with the corresponding inventories. -/
theorem place_trade (q : Proposal T H) (g : J → I ⊕ E) (u : Finset J) (m l : ℕ)
    (hd : ∀ j ∈ q.demand, ∃ i, g j = .inl i)
    (T' : J → Tensor K S) (n : S → B) (U : I ⊕ E → Tensor K B)
    (he : ∀ j, Tensor.place n (T' j) = U (g j))
    (cmp : bundle T' (copies q.demand (q.move.block * m)) ≤
      ∑ h ∈ histograms q.move.letter l, bundle T' (q.output u l h)) :
    ({ q.trade g u l with take := (q.trade g u m).take } : Intervention I E).Covers
      (U ∘ Sum.inl) (U ∘ Sum.inr) := by
  classical
  let F : Tensor K S →* Tensor K B :=
    { toFun := Tensor.place n
      map_one' := Tensor.place_one n
      map_mul' := Tensor.place_mul n }
  have hs (v : Finset (q.move.letter → ℕ)) (z : (q.move.letter → ℕ) → Tensor K S) :
      F (∑ i ∈ v, z i) ≤ ∑ i ∈ v, F (z i) := by
    induction v using Finset.induction_on with
    | empty => rw [sum_empty, sum_empty]; exact (Tensor.place_zero n).le
    | insert i v hi ih =>
      rw [sum_insert hi, sum_insert hi, add_comm (z i), add_comm (F (z i))]
      exact (Tensor.place_add_le n _ _).trans (Tensor.add_le_add_right _ _ _ ih)
  have hb (z : J → ℕ) :
      F (bundle T' z) = bundle (U ∘ Sum.inl) (collect g z ∘ Sum.inl) *
        bundle (U ∘ Sum.inr) (collect g z ∘ Sum.inr) := by
    rw [← bundle_split, bundle_collect, bundle, map_prod]
    apply prod_congr rfl
    intro j _
    rw [map_pow]
    exact congrArg (· ^ z j) (he j)
  have ht : bundle (U ∘ Sum.inl) (q.trade g u m).take =
      F (bundle T' (copies q.demand (q.move.block * m))) := by
    rw [hb, show bundle (U ∘ Sum.inr) (collect g (copies q.demand (q.move.block * m)) ∘ Sum.inr)
      = 1 by simp [bundle, q.take_core g m hd], mul_one]
    rfl
  unfold Intervention.Covers
  rw [ht]
  refine ((Tensor.place_mono n cmp).trans (hs _ _)).trans_eq ?_
  rw [← sum_coe_sort]
  exact sum_congr rfl fun h _ => hb _

theorem trade_covers (q : Proposal T H) (g : J → I ⊕ E) (u : Finset J) (m : ℕ)
    (hd : ∀ j ∈ q.demand, ∃ i, g j = .inl i) (hu : (2 : Tensor K S) ≤ ∏ j ∈ u, T j)
    (n : S → B) (U : I ⊕ E → Tensor K B) (he : ∀ j, Tensor.place n (T j) = U (g j)) :
    (q.trade g u m).Covers (U ∘ Sum.inl) (U ∘ Sum.inr) := by
  exact q.place_trade g u m m hd T n U he (q.batch u hu m)

end OAI.LinearAlgebra.MatrixExponent.Routing.Proposal
end

/-!
# Reindexing a local price test on the coordinates of a ball
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.BallShape

open Spectral
open scoped Classical

variable {K S I B : Type} [Field K] [Fintype S] [DecidableEq S] [DecidableEq I]
  [Fintype B] [DecidableEq B] {V : Finset I}

/-- A coordinate chart carries both orientations of each core link. -/
def chart (e : V ≃ B) (a b : V) (c : I → I → Prop)
    (h : ∀ x y : V, Relation.EqvGen (fun u v : V => c u.val v.val) x y) : BallShape B where
  src := e a
  dst := e b
  edges := Finset.univ.filter fun xy =>
    c (e.symm xy.1) (e.symm xy.2) ∨ c (e.symm xy.2) (e.symm xy.1)
  flip := by simp [or_comm]
  connected x y := by
    have hp (u v : V) (huv : Relation.EqvGen (fun z w : V => c z.val w.val) u v) :
        Relation.EqvGen (fun z w => c (e.symm z) (e.symm w) ∨ c (e.symm w) (e.symm z))
          (e u) (e v) := by
      induction huv with
      | rel u v h => exact .rel _ _ (by simp [h])
      | refl => exact .refl _
      | symm _ _ _ ih => exact .symm _ _ ih
      | trans _ _ _ _ _ ih ih' => exact .trans _ _ _ ih ih'
    simpa using hp _ _ (h (e.symm x) (e.symm y))

variable (A : Finset (Tensor K S)) (b : BallShape B) (e : V ≃ B)

def localRates (v : ℝ) (x : (S → I) → Tensor K S → ℝ) : b.Goods A → ℝ :=
  b.rates A v (fun z => x (Subtype.val ∘ e.symm ∘ z))

omit [DecidableEq S] [DecidableEq I] [Fintype B] [DecidableEq B] in
theorem localRates_mem {v M : ℝ} (hM : 1 ≤ M) (hv : v ∈ Set.Icc 0 M)
    (x : (S → I) → Tensor K S → ℝ) (hx : ∀ z a, a ∈ A → x z a ∈ Set.Icc 0 M) :
    localRates A b e v x ∈ Set.Icc 0 (fun _ => M) := by
  have h (i : b.Goods A) : localRates A b e v x i ∈ Set.Icc 0 M := by
    rcases i with (_ | ⟨z, j⟩) | k
    · exact hv
    · exact hx _ _ (A.equivFin.symm j).property
    · exact ⟨zero_le_one, hM⟩
  exact ⟨fun i => (h i).1, fun i => (h i).2⟩

theorem near_passes (c : I → I → Prop)
    (hc : ∀ i j : V, c i.val j.val → (e i, e j) ∈ b.edges)
    (v : ℝ) (x : (S → I) → Tensor K S → ℝ) (ρ : ℝ)
    (hp : NearPrices (b.tensor A) (b.demands A) ρ (localRates A b e v x)) :
    ∃ P, (P = 0 ∨ ∃ D, P ∈ Tensor.ordinary K V D) ∧
      Passes A V c (e.symm b.src) (e.symm b.dst) v x ρ P := by
  obtain ⟨P, hP, hs, hd⟩ := hp
  have price : P ∘ Tensor.place e = 0 ∨ ∃ D, P ∘ Tensor.place e ∈ Tensor.ordinary K V D := by
    rcases hP with rfl | ⟨D, d, h, f, hf, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨D, d, h, f.comp (Tensor.group _ e.surjective),
        hf.comp (Tensor.group_mono _ e.surjective), rfl⟩
  have hd' (i : Requests B A) := hd (.inl i) (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  refine ⟨P ∘ Tensor.place e, price, ?_, ?_, ?_⟩
  · intro i j hi hj
    rw [Subtype.ext hi, Subtype.ext hj]
    simp only [Function.comp_apply, Tensor.place_wire, Equiv.apply_symm_apply]
    exact (hd' none).le
  · intro i j h
    rw [Function.comp_apply, Tensor.place_wire]
    exact (hs (.inr ⟨(e i, e j), hc i j h⟩)).le
  · intro z u hu
    rw [Function.comp_apply, ← Tensor.place_comp]
    have h := hd' (some (e ∘ z, A.equivFin ⟨u, hu⟩))
    have he : e.symm ∘ (e ∘ z) = z := funext fun s => e.symm_apply_apply _
    simpa only [localRates, rates, tensor, Equiv.symm_apply_apply, he] using h.le

end OAI.LinearAlgebra.MatrixExponent.Routing.BallShape
end

/-!
# Requests across a family of overlapping balls

A tuple occurring at two centers names the same request. Core links
may be counted separately for each center. A site of a tuple gives
an anchor bounding the number of centers that can alter its stock.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral
open scoped Classical

structure Market (I : Type) (N : ℕ) where
  size : I → Fin (N + 1)
  shape : (i : I) → BallShape (Fin (size i).val)
  name : (i : I) → Fin (size i).val ↪ I
  origin : ∀ i, name i (shape i).src = i
  overlap : ∀ x, ∃ U : Finset I, U.card ≤ N ∧ ∀ i t, name i t = x → i ∈ U

namespace Market

variable {K I S : Type} [Field K] [Fintype I] [DecidableEq I]
  [Fintype S] [DecidableEq S] {N : ℕ}

variable (b : Market I N) (A : Finset (Tensor K S))

abbrev Site (i : I) := Fin (b.size i).val

def tuple (w : Σ i, S → b.Site i) : S → I := b.name w.1 ∘ w.2

abbrev Request := I ⊕ (Set.range (b.tuple (S := S)) × Fin A.card)
abbrev Edge := Σ i, (b.shape i).edges
abbrev Good := b.Request A ⊕ b.Edge

def request (i : I) : BallShape.Requests (b.Site i) A → b.Request A
  | none => .inl i
  | some (z, j) => .inr (⟨b.name i ∘ z, ⟨⟨i, z⟩, rfl⟩⟩, j)

def assign (i : I) : (b.shape i).Goods A → b.Good A :=
  Sum.map (b.request A i) (fun e => ⟨i, e⟩)

def tensor : b.Good A → Tensor K I
  | .inl (.inl i) => Tensor.wire K i (b.name i (b.shape i).dst) 2
  | .inl (.inr (z, j)) => Tensor.place z.val (A.equivFin.symm j).val
  | .inr ⟨i, e⟩ => Tensor.wire K (b.name i e.val.1) (b.name i e.val.2) 2

theorem place_tensor (i : I) (a : (b.shape i).Goods A) :
    Tensor.place (b.name i) ((b.shape i).tensor A a) = b.tensor A (b.assign A i a) := by
  rcases a with (_ | ⟨z, j⟩) | e
  · simp only [BallShape.tensor, Tensor.place_wire, b.origin]
    rfl
  · exact (Tensor.place_comp _ _ _).symm
  · exact Tensor.place_wire _ _ _ _

omit [Fintype I] [DecidableEq I] [DecidableEq S] in
theorem assign_injective (i : I) : Function.Injective (b.assign A i) := by
  unfold assign
  apply Sum.map_injective.mpr
  constructor
  · rintro (_ | ⟨z, j⟩) (_ | ⟨w, k⟩) h
    · rfl
    · contradiction
    · contradiction
    · have e := Sum.inr.inj h
      have he : b.name i ∘ z = b.name i ∘ w := congrArg (fun p => p.1.val) e
      have hj : j = k := congrArg Prod.snd e
      have hw : z = w := funext fun s => (b.name i).injective (congrFun he s)
      rw [hj, hw]
  · exact fun _ _ h => eq_of_heq (Sigma.mk.inj h).2

def rates (p : b.Request A → ℝ) : b.Good A → ℝ := Sum.elim p fun _ => 1

/-- Shared prices extend arbitrarily outside the set of possible requests. -/
def quote (p : b.Request A → ℝ) (z : S → I) (a : Tensor K S) : ℝ :=
  if h : z ∈ Set.range b.tuple ∧ a ∈ A then p (.inr (⟨z, h.1⟩, A.equivFin ⟨a, h.2⟩)) else 0

theorem rates_assign (p : b.Request A → ℝ) (i : I) :
    b.rates A p ∘ b.assign A i =
      (b.shape i).rates A (p (.inl i)) (fun z => b.quote A p (b.name i ∘ z)) := by
  funext a
  rcases a with (_ | ⟨z, j⟩) | e
  · rfl
  · have h : b.name i ∘ z ∈ Set.range b.tuple ∧ (A.equivFin.symm j).val ∈ A :=
      ⟨⟨⟨i, z⟩, rfl⟩, (A.equivFin.symm j).property⟩
    change _ = b.quote A p (b.name i ∘ z) (A.equivFin.symm j).val
    simp only [quote, dite_eq_left h, Subtype.eta, Equiv.apply_symm_apply]
    rfl
  · rfl

def home [Nonempty S] : b.Request A → I
  | .inl i => i
  | .inr (z, _) => z.val (Classical.arbitrary S)

def support (i : I) := Finset.univ.map (b.name i)

omit [Fintype I] [DecidableEq I] [DecidableEq S] in
theorem home_mem [Nonempty S] (i : I) (j : (b.shape i).Goods A) (x : b.Request A)
    (h : b.assign A i j = .inl x) : b.home A x ∈ b.support i := by
  rcases j with (_ | ⟨z, k⟩) | e
  · rw [← Sum.inl.inj h]
    exact Finset.mem_map.mpr ⟨_, Finset.mem_univ _, b.origin i⟩
  · rw [← Sum.inl.inj h]
    exact Finset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · contradiction

omit [Fintype I] [DecidableEq I] in
theorem card_support (i : I) : (b.support i).card ≤ N := by
  simp only [support, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  exact Nat.lt_succ_iff.mp (b.size i).isLt

theorem count_support (x : I) : (Finset.univ.filter fun i => x ∈ b.support i).card ≤ N := by
  obtain ⟨U, hU, hu⟩ := b.overlap x
  refine (Finset.card_le_card ?_).trans hU
  intro i hi
  obtain ⟨t, _, ht⟩ := Finset.mem_map.mp (Finset.mem_filter.mp hi).2
  exact hu i t ht

theorem card_request :
    Fintype.card (b.Request A) ≤ Fintype.card I * (1 + N ^ Fintype.card S * A.card) := by
  have ht : Fintype.card (Set.range (b.tuple (S := S))) ≤ Fintype.card I * N ^ Fintype.card S := by
    refine (Fintype.card_le_of_surjective (Set.rangeFactorization b.tuple) ?_).trans ?_
    · rintro ⟨_, j, rfl⟩
      exact ⟨j, rfl⟩
    · simp only [Fintype.card_sigma, Fintype.card_fun, Site, Fintype.card_fin]
      calc
        _ ≤ ∑ _ : I, N ^ Fintype.card S := Finset.sum_le_sum fun i _ =>
          Nat.pow_le_pow_left (Nat.lt_succ_iff.mp (b.size i).isLt) _
        _ = _ := by simp
  simp only [Request, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    mul_add, mul_one, ← mul_assoc]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _

end Market
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Placing all the selected trades

No greedy packing is needed for the stock bound: each request has a
home site, and only centers whose balls contain that site can affect it.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Market
open Spectral
open scoped Classical

variable {K I S : Type} [Field K] [Fintype I] [DecidableEq I]
  [Fintype S] [DecidableEq S] {N : ℕ} {M ρ : ℝ}
  (b : Market I N) (A : Finset (Tensor K S))

abbrev code (i : I) : Shape N := ⟨b.size i, b.shape i⟩

def Fails (p : b.Request A → ℝ) (ρ : ℝ) (i : I) : Prop :=
  ¬ NearPrices ((b.shape i).tensor A) ((b.shape i).demands A) ρ (b.rates A p ∘ b.assign A i)

def batch (i : I) (q : (b.code i).Move A) (m : ℕ) : Intervention (b.Request A) b.Edge :=
  q.trade (b.assign A i) ((b.shape i).links A) m

variable {A}

theorem choose_batch (a : Atlas N A M ρ) (hM : 1 ≤ M)
    (p : b.Request A → ℝ) (hp : ∀ j, p j ∈ Set.Icc 0 M)
    (i : I) (hi : b.Fails A p ρ i) :
    ∃ q ∈ a.menu (b.code i), ∀ m,
      (b.batch A i q m).Covers (b.tensor A ∘ Sum.inl) (b.tensor A ∘ Sum.inr) ∧
      (b.batch A i q m).Efficient p a.margin a.capacity m := by
  let _ : Nonempty (b.Site i) := ⟨(b.shape i).src⟩
  let E := b.shape i
  let g := b.assign A i
  have h (j : E.Goods A) : b.rates A p (g j) ∈ Set.Icc 0 M := by
    cases g j with
    | inl x => exact hp x
    | inr x => exact ⟨zero_le_one, hM⟩
  obtain ⟨q, hq, hd, _, hw⟩ := (a.detect (b.code i) (b.rates A p ∘ g)
    ⟨fun j => (h j).1, fun j => (h j).2⟩).resolve_left hi
  have h₁ : ∀ j ∈ q.demand, ∃ l, g j = .inl l := by
    intro j hj
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp (hd hj)
    exact ⟨_, rfl⟩
  have h₂ : ∀ j ∈ E.links A, ∃ l, g j = .inr l := by
    intro j hj
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hj
    exact ⟨_, rfl⟩
  have h₃ : ((E.links A).card : ℝ) ≤ E.edges.card := by simp [BallShape.links]
  obtain ⟨hb, ho⟩ := a.small _ q hq
  refine ⟨q, hq, fun m => ⟨?_, ?_⟩⟩
  · exact q.trade_covers g (E.links A) m h₁ (E.broadcast A) (b.name i) (b.tensor A)
      (b.place_tensor A i)
  · exact q.trade_efficient g (E.links A) m (b.assign_injective A i)
      h₁ h₂ h₃ a.positive.le hw hb ho

theorem batch_overlap [Nonempty S] (J : Finset I)
    (q : (i : J) → (b.code i).Move A) (m : ℕ) (x : b.Request A) :
    ∃ U : Finset J, U.card ≤ N ∧ ∀ j, (b.batch A j.val (q j) m).affects x → j ∈ U := by
  let U := Finset.univ.filter fun j : J => b.home A x ∈ b.support j
  have h : U.map (Function.Embedding.subtype _) ⊆
      Finset.univ.filter (fun j => b.home A x ∈ b.support j) := by
    rintro _ hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  refine ⟨U, ?_, fun j he => ?_⟩
  · simpa only [Finset.card_map] using (Finset.card_le_card h).trans (b.count_support _)
  · obtain ⟨k, hk⟩ := (q j).trade_support _ _ _ he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.home_mem A j k x hk⟩

end OAI.LinearAlgebra.MatrixExponent.Routing.Market
end

/-!
# Choosing a chart by local observations only

A chart lists a word representing each site of the ball. Its validity
is a finite test of equalities between words at the center. Choosing
from the legal charts therefore needs only a fixed table.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open scoped Classical Pointwise

variable {G : Type} [Group G] (H : Finset G) (r : ℕ)

abbrev Board := Σ s : Shape (H ^ r).card, Fin s.1.val → ↥(H ^ r)

namespace Board
variable {H r}

abbrev Site (b : Board H r) := Fin b.1.1.val

def word (b : Board H r) (i : b.Site) : G := (b.2 i).val⁻¹

def Valid (g : G) (x : Root G) (b : Board H r) : Prop :=
  (∀ i j, x.see (b.word i) (b.word j) = true → i = j) ∧
  (∀ t : ↥(H ^ r), ∃ i, x.see (b.word i) t.val⁻¹ = true) ∧
  x.see (b.word b.1.2.src) 1 = true ∧ x.see (b.word b.1.2.dst) g⁻¹ = true ∧
  ∀ i j, (i, j) ∈ b.1.2.edges ↔ ∃ t : H,
    x.see (t.val⁻¹ * b.word i) (b.word j) = true ∨
    x.see (t.val⁻¹ * b.word j) (b.word i) = true

def name (x : Root G) (b : Board H r) (i : b.Site) : ball H r x.center :=
  ⟨x.label (b.word i), mem_ball _ (b.2 i).property⟩

theorem valid_iff (g : G) (x : Root G) (b : Board H r) :
    Valid g x b ↔ Function.Bijective (name x b) ∧
      (name x b b.1.2.src).val = x.center ∧ (name x b b.1.2.dst).val = g⁻¹ • x.center ∧
      ∀ i j, (i, j) ∈ b.1.2.edges ↔ link H (name x b i).val (name x b j).val ∨
        link H (name x b j).val (name x b i).val := by
  simp only [Valid, Root.see, decide_eq_true_eq]
  simp only [Root.label, one_smul, mul_smul]
  have hi : (∀ i j, b.word i • x.center = b.word j • x.center → i = j) ↔
      Function.Injective (name x b) :=
    ⟨fun h _ _ he => h _ _ (congrArg Subtype.val he), fun h _ _ he => h (Subtype.ext he)⟩
  have hs : (∀ t : ↥(H ^ r), ∃ i, b.word i • x.center = t.val⁻¹ • x.center) ↔
      Function.Surjective (name x b) := by
    constructor
    · rintro h ⟨y, hy⟩
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨i, hi⟩ := h ⟨t, ht⟩
      exact ⟨i, Subtype.ext hi⟩
    · intro h t
      obtain ⟨i, hi⟩ := h ⟨_, mem_ball _ t.property⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  rw [hi, hs, ← and_assoc]
  simp only [Function.Bijective, name, Root.label, link, exists_or, Subtype.exists, exists_prop]

variable (H) (hH : 1 ∈ H) (r) (g : G) (hg : g ∈ H ^ r)

include hH hg in
theorem exists_valid (x : Root G) : ∃ b : Board H r, Valid g x b := by
  let V := ball H r x.center
  let e := V.equivFin
  let s := BallShape.chart e ⟨x.center, center_mem_ball hH r x.center⟩
    ⟨g⁻¹ • x.center, mem_ball _ hg⟩ (link H) (ball_connected hH r _)
  have hs (i : Fin V.card) : ∃ a : ↥(H ^ r), a.val⁻¹ • x.center = (e.symm i).val := by
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (e.symm i).property
    exact ⟨⟨a, ha⟩, he⟩
  choose w hw using hs
  let b : Board H r := ⟨⟨⟨V.card, Nat.lt_succ_of_le Finset.card_image_le⟩, s⟩, w⟩
  have he : name x b = e.symm := funext fun i => Subtype.ext (hw i)
  refine ⟨b, (valid_iff _ _ _).mpr ?_⟩
  rw [he]
  exact ⟨e.symm.bijective, congrArg Subtype.val (e.symm_apply_apply _),
    congrArg Subtype.val (e.symm_apply_apply _), fun _ _ => by simp [b, s, BallShape.chart]⟩

def choose (x : Root G) : Board H r := Classical.choose (exists_valid H r hH g hg x)

theorem valid_choose (x : Root G) : Valid g x (choose H r hH g hg x) :=
  Classical.choose_spec (exists_valid H r hH g hg x)

theorem local_choose : Root.Local (choose H r hH g hg) := by
  let V := (H ^ r)⁻¹
  let W := insert 1 (insert g⁻¹ (V ∪ H⁻¹ * V))
  have hV (t : ↥(H ^ r)) : t.val⁻¹ ∈ V := by simp [V]
  have hv (t : ↥(H ^ r)) : t.val⁻¹ ∈ W := by simp [W, hV t]
  have hw (t : H) (u : ↥(H ^ r)) : t.val⁻¹ * u.val⁻¹ ∈ W := by
    have h : t.val⁻¹ * u.val⁻¹ ∈ H⁻¹ * V := Finset.mul_mem_mul (by simp) (hV u)
    simp [W, h]
  refine ⟨W, fun x y he => ?_⟩
  have same : Valid (H := H) (r := r) g x = Valid g y := by
    funext b
    have h (i : b.Site) (u : ↥(H ^ r)) : x.see (b.word i) u.val⁻¹ = y.see (b.word i) u.val⁻¹ :=
      he _ (hv (b.2 i)) _ (hv u)
    have h' (i j : b.Site) : x.see (b.word i) (b.word j) = y.see (b.word i) (b.word j) :=
      h i (b.2 j)
    have hm (i j : b.Site) (t : H) :
        x.see (t.val⁻¹ * b.word i) (b.word j) = y.see (t.val⁻¹ * b.word i) (b.word j) :=
      he _ (hw t (b.2 i)) _ (hv (b.2 j))
    have h₀ := he (b.word b.1.2.src) (hv _) 1 (by simp [W])
    have h₁ := he (b.word b.1.2.dst) (hv _) g⁻¹ (by simp [W])
    simp only [Valid, h, h', hm, h₀, h₁]
  unfold choose
  congr

end Board
end OAI.LinearAlgebra.MatrixExponent.Routing
end
