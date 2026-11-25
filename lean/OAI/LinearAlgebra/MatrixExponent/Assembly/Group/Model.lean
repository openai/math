import OAI.LinearAlgebra.MatrixExponent.Packing.BadBases
import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Assembly.Matching
import OAI.LinearAlgebra.MatrixExponent.Packing.ResetLocation
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute
import OAI.LinearAlgebra.MatrixExponent.Processor.Labels
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Packing.Projection

section
/-! # Locality of dyadic marks -/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Group
open Packing

variable {V U : Type} (E : V → Finset V) (d : V → V → ℕ)

/-- The index records the accumulated change of depth. -/
inductive Walk (v : V) : ℕ → V → Prop
  | root : Walk v 0 v
  | edge {i a b} : Walk v i a → b ∈ E a → Walk v (i + 2 * d a b) b

variable (A : U → Finset U) (c : U → U → ℕ) (p : U → V) (v : U) (h : ℕ)

/-- Slots may repeat a host. Edges that can only act above the height
budget need not be stored. -/
structure Window : Prop where
  edge : ∀ i j, j ∈ A i → p j ∈ E (p i) ∧ c i j = d (p i) (p j)
  full : ∀ i j k, Walk E d (p v) k (p i) → j ∈ E (p i) → k + 2 * d (p i) j < h →
    ∃ t ∈ A i, p t = j

variable {E d A c p v h} {M : V → (i : ℕ) → Cell i → Prop}

private theorem shift {x y : V} {i k : ℕ} (he : y ∈ E x) (hk : k = d x y)
    (j : Cell (i + 2 * k)) (hj : Spread E d M y _ j) :
    Spread E d M x i (ancestor (by omega) j) := by
  subst k
  exact .move he j hj

variable (w : Window E d A c p v h)
include w

private theorem push {u i z} (m : Spread A c (fun a => M (p a)) u i z) :
    Spread E d M (p u) i z := by
  induction m with
  | start m => exact .start m
  | @move x y i e z _ ih =>
    obtain ⟨he, hd⟩ := w.edge _ _ e
    exact shift he hd z ih

private theorem pull (hb : ∀ t i z, M t i z → i < h) {x i z} (m : Spread E d M x i z) :
    ∀ {a k}, p a = x → Walk E d (p v) k x → k ≤ i → Spread A c (fun a => M (p a)) a i z := by
  induction m with
  | start m => rintro a k rfl _ _; exact .start m
  | @move x y i e z hm ih =>
    rintro a k rfl hpath hk
    obtain ⟨b, he, hy⟩ := w.full a y k hpath e (lt_of_le_of_lt (Nat.add_le_add_right hk _) (hm.depth hb))
    have hs := ih hy (hpath.edge e) (Nat.add_le_add_right hk _)
    have hd : d (p a) y = c a b := by rw [← hy, (w.edge a b he).2]
    exact shift he hd z hs

theorem Window.spread (hb : ∀ t i z, M t i z → i < h) :
    Spread A c (fun a => M (p a)) v = Spread E d M (p v) := by
  funext i z
  exact propext ⟨push w, fun m => pull w hb m rfl .root (Nat.zero_le _)⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Group
end

section
/-! # Bounded records for local grouping decisions -/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Group
open Coloring

/-- Live bit, the two neighbor masks, then loads of all group members
at the visible hosts. Position zero is the center. -/
abbrev Patch (q h b : ℕ) := Format.pair .bit (.pair
  (.vec q (.vec q (.pair .bit .bit))) (.vec q (.vec h (.addr b))))

abbrev Labels (h : ℕ) := Format.vec h (.addr (h + 1))

/-- Split counts and all candidate labelings. -/
abbrev Summary (h : ℕ) := Format.pair (.vec h (.addr h)) (.vec h (Labels h))

theorem width_patch (q h b : ℕ) : (Patch q h b).width = 1 + 2 ^ q * (2 ^ q * 2 + 2 ^ h * b) := by
  simp [Patch, mul_add]

theorem width_summary (h : ℕ) : (Summary h).width = 2 ^ h * (h + 2 ^ h * (h + 1)) := by
  simp only [Summary, Labels, Format.width_pair, Format.width_vec, Format.width_addr, mul_add]
  rw [Format.width_addr (h + 1), mul_add, mul_add]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Group
end

/-!
# Electing the common mixer and recovering dyadic leaf labels

Only local load and incidence records index the table of candidates.
The common mixer is elected by summing the split counts over live hosts.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Group
open Coloring Finset Packing
open scoped Classical

variable {V : Type} {q h b m : ℕ}

def graph (x : (Patch q h b).obj) (i : B q) : Finset (B q) :=
  univ.filter fun j => (x.2.1 i j).1

def core (x : (Patch q h b).obj) (i : B q) : Finset (B q) :=
  univ.filter fun j => (x.2.1 i j).2

def load (f : B b → ℝ) (x : (Patch q h b).obj) (i : B q) (u : Cell h) :=
  f (x.2.2 i (cellIndex h u))

def atLeaf (M : (i : ℕ) → Cell i → Prop) (x : Cell h) : B (h + 1) :=
  intervalCode h ⟨⟨leafDepth M x, Nat.lt_succ_of_le (leafDepth_le M x)⟩,
    ancestor (leafDepth_le M x) x⟩

def summarize (Δ D : ℕ) (f : B b → ℝ) (x : (Patch q h b).obj) : (Summary h).obj :=
  let E := graph x
  let d := delay (core x) Δ D
  let l := load f x
  (fun t => if x.1 then ⟨splits E d l t 0, splits_le E d l t 0⟩ else 0,
   fun t i => atLeaf (marks E d l t 0) (menu h t ((cellIndex h).symm i)))

def winner (x : B m → (Summary h).obj) : B h :=
  elect ⊥ (fun t i => (x i).1 t)

def decideAll (Δ D : ℕ) (f : B b → ℝ) (x : B m → (Patch q h b).obj) :
    B m → (Labels h).obj :=
  let y := summarize Δ D f ∘ x
  fun i => (y i).2 (winner y)

variable (E : V → Finset V) (d : V → V → ℕ) (l : V → Cell h → ℝ)
  (Δ D : ℕ) (f : B b → ℝ) (x : B m → (Patch q h b).obj) (host : V ↪ B m)

structure Represents : Prop where
  live : ∀ i, (x i).1 = true ↔ i ∈ Set.range host
  patch : ∀ v, ∃ p : B q → V, p 0 = v ∧
    Window E d (graph (x (host v))) (delay (core (x (host v))) Δ D) p 0 h ∧
    load f (x (host v)) = l ∘ p

variable {E d l Δ D f x host}
  (H : Represents E d l Δ D f x host) (hb : ∀ v u, l v u ≤ 1)
include H hb

theorem Represents.marks (v : V) (t : B h) :
    Packing.marks (graph (x (host v))) (delay (core (x (host v))) Δ D)
      (load f (x (host v))) t 0 = Packing.marks E d l t v := by
  obtain ⟨p, hp, w, he⟩ := H.patch v
  rw [he]
  let M i := heavy (l i) (menu h t).toEquiv
  have ht := w.spread (M := M) (fun v _ _ z => heavy.lt (hb v) z)
  rw [hp] at ht
  exact ht

theorem Represents.best [Fintype V] : best E d l (winner (summarize Δ D f ∘ x)) := by
  let y := summarize Δ D f ∘ x
  have eq (t : B h) : ∑ i, ((y i).1 t).val = ∑ v, splits E d l t v := by
    rw [← sum_subset (subset_univ (univ.map host))]
    · rw [sum_map]
      apply sum_congr rfl
      intro v _
      have he := (H.live (host v)).mpr ⟨v, rfl⟩
      simp only [y, Function.comp_apply, summarize, he, ↓reduceIte, splits, H.marks hb]
    · intro i _ hi
      have he : (x i).1 ≠ true := fun e => by
        obtain ⟨v, rfl⟩ := (H.live _).mp e
        exact hi (mem_map.mpr ⟨v, mem_univ _, rfl⟩)
      simp [y, summarize, he]
  intro t
  rw [← eq, ← eq]
  exact elect_min (fun t i => (y i).1 t) t

theorem Represents.label (v : V) (u : Cell h) :
    let pick := winner (summarize Δ D f ∘ x)
    decideAll Δ D f x (host v) (cellIndex h u) =
      atLeaf (Packing.marks E d l pick v) (menu h pick u) := by
  simp only [decideAll, Function.comp_apply, summarize, Equiv.symm_apply_apply, H.marks hb]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Group
end

/-!
# Uniform grouping network

There are two table labels. Their arities are independent of the number
of hosts and the number of groups. The only long-range operation is
the election on columns of short split counts.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Group
open Coloring
open scoped Classical

def electionCost (m h : ℕ) :=
  2 ^ h * (2 ^ m * (100 + h) ^ 5 + (100 + (h + (h + m))) ^ 42)

abbrev Query (h : ℕ) := Format.pair (.addr h) (Summary h)

def result (h : ℕ) (x : (Query h).obj) : (Labels h).obj := x.2.2 x.1

variable (F : Type) [Field F]

private theorem query_net (m h : ℕ) :
    Circuit F (.vec m (Summary h)) (.vec m (Query h)) (fun x i => (winner x, x i))
      (16 * (2 ^ m * (h + (Summary h).width)) + electionCost m h) := by
  let R := Format.vec m (Summary h)
  let D := Format.vec h (.vec m (.addr h))
  have pr : Circuit F R D (fun x t i => (x i).1 t) (R.width + 2 * D.width) := by
    apply Circuit.project (A := R) (D := D) (fun i => (i.2.1, .inl (i.1, i.2.2)))
    exact fun _ _ => rfl
  have hd : D.width ≤ R.width := by
    simp only [R, D, Format.width_vec, Format.width_addr]
    rw [width_summary h, mul_left_comm]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
  let A := Format.pair (.addr h) R
  let B := Format.vec m (Query h)
  have post : Circuit F A B (fun y i => (y.1, y.2 i)) (A.width + 2 * B.width) := by
    apply Circuit.project (A := A) (D := B) (fun i => Sum.elim Sum.inl (fun t => Sum.inr (i.1, t)) i.2)
    rintro x ⟨i, t | t⟩ <;> rfl
  have hn := ((pr.comp (election F m h h ⊥)).pair (Circuit.id F R)).comp post
  refine hn.mono ?_
  change 5 * R.width + (R.width + 2 * D.width + electionCost m h) + R.width +
    (A.width + 2 * B.width) ≤ _
  have hpos : h ≤ 2 ^ m * h := Nat.le_mul_of_pos_left _ (by positivity)
  rw [show A.width = h + R.width by simp [A],
    show B.width = 2 ^ m * (h + (Summary h).width) by simp only [B, Query, Format.width_vec,
      Format.width_pair, Format.width_addr]]
  rw [show R.width = 2 ^ m * (Summary h).width from Format.width_vec _ _] at hd ⊢
  rw [mul_add]
  omega

def keys (q h b Δ D : ℕ) (f : B b → ℝ) : Finset (Table F) :=
  {lookup F (Patch q h b) (Summary h) (fun x y => @ite F (summarize Δ D f x = y) (Classical.propDecidable _) 1 0),
   lookup F (Query h) (Labels h) (fun x y => @ite F (result h x = y) (Classical.propDecidable _) 1 0)}

def arity (q h b : ℕ) := (Patch q h b).width + (Summary h).width + h + (Labels h).width

def cost (m q h b : ℕ) := 100 * (2 ^ m * (1 + arity q h b)) + 4 * electionCost m h

variable {q h b Δ D : ℕ} {f : B b → ℝ}

theorem card_keys : (keys F q h b Δ D f).card ≤ 2 := Finset.card_le_two

theorem arity_keys {T : Table F} (ht : T ∈ keys F q h b Δ D f) :
    Processor.arity T ≤ arity q h b := by
  simp only [keys, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl <;>
    simp only [Processor.arity, lookup, wd_word, arity, Query, Format.width_pair,
      Format.width_addr] <;> omega

theorem compute {u : ℕ} {L : Set (Table F)} (m : ℕ) (hu : 3 ≤ u)
    (hb : arity q h b ≤ u) (hL : (keys F q h b Δ D f : Set _) ⊆ L) :
    Map F u L (.vec m (Patch q h b)) (.vec m (Labels h)) (decideAll Δ D f) (cost m q h b) := by
  have ht : Map F u L (Patch q h b) (Summary h) (summarize Δ D f) (1 + arity q h b) := by
    apply Kernel.mono (Kernel.lookup (by unfold arity at hb; omega) (hL (by simp [keys])))
    unfold arity
    omega
  have hr : Map F u L (Query h) (Labels h) (result h) (1 + arity q h b) := by
    have he : (Query h).width = h + (Summary h).width := by simp only [Query,
      Format.width_pair, Format.width_addr]
    apply Kernel.mono (Kernel.lookup (by unfold arity at hb; omega) (hL (by simp [keys])))
    unfold arity
    omega
  have first := Map.vec (t := m) _ (fun _ => ht)
  have last := Map.vec (t := m) _ (fun _ => hr)
  refine ((first.comp (Map.circuit hu (query_net F m h))).comp last).mono ?_
  unfold cost
  have ha := Nat.mul_le_mul_left (2 ^ m) (show h + (Summary h).width ≤ 1 + arity q h b by
    unfold arity; omega)
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Group
end

/-! # The computed labels certify a balanced partition -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Group

open Coloring Packing

variable {V : Type} [Fintype V] {q h b m k Δ D : ℕ} {E C : V → Finset V}
  {l : V → Cell h → ℝ} {B' : ℝ} {f : B b → ℝ} {x : B m → (Patch q h b).obj} {host : V ↪ B m}

theorem Represents.grouping
    (H : Represents E (delay C Δ D) (relative k B' l) Δ D f x host)
    (hΔ : 0 < Δ) (hD : 0 < D) (hk : 1 ≤ k) (hkh : k ≤ h) (hB : 0 < B')
    (eSym : ∀ v u, u ∈ E v → v ∈ E u) (cSym : ∀ v u, u ∈ C v → v ∈ C u)
    (sub : ∀ v, C v ⊆ E v) (eDeg : ∀ v, (E v).card ≤ D) (cDeg : ∀ v, (C v).card ≤ Δ)
    (hl : ∀ v i, 0 ≤ l v i ∧ l v i ≤ B') :
    ∃ g : Grouping E C Δ D k B' l, ∀ v i,
      decideAll Δ D f x (host v) (cellIndex h i) = intervalCode h (g.here v i).2 := by
  have hb (v : V) (i : Cell h) : relative k B' l v i ≤ 1 := by
    apply (div_le_one (mul_pos (by positivity) hB)).mpr
    exact (hl v i).2.trans (le_mul_of_one_le_left hB.le (one_le_pow₀ (by norm_num)))
  let pick := winner (summarize Δ D f ∘ x)
  let g := groupBy E C Δ D hΔ hD eSym cSym sub eDeg cDeg hk hkh B' hB l hl pick (H.best hb)
  exact ⟨g, fun v i => H.label hb v i⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Group
end

/-!
# Names and neighbors of child hosts

An address consists of a parent host and a dyadic interval. Only
intersecting intervals at nearby depths need neighbor slots. Their
enumeration is fixed by the height and degree, independently of the
parent graph. A third neighborhood gives the post-contraction graph.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Child
open Packing Coloring
open scoped Classical
variable {V : Type} {m h D d : ℕ}

abbrev Interval (h : ℕ) := Σ i : Fin (h + 1), Cell i.val

def host (p : V ↪ B m) (h : ℕ) : Site V h ↪ B (m + (h + 1)) :=
  (p.prodMap (intervalCode h)).trans (Match.rowIndex m (h + 1)).symm.toEmbedding

@[simp] theorem host_parts (p : V ↪ B m) (v : Site V h) :
    Match.rowIndex m (h + 1) (host p h v) = (p v.1, intervalCode h v.2) :=
  (Match.rowIndex m (h + 1)).apply_symm_apply _

def close (D : ℕ) (x : Interval h) : Finset (Site Unit h) :=
  near (fun _ => {()}) D ((), x)

private theorem interval_contains (x : Interval h) : ∃ i, Site.contains ((), x) i := by
  let f (i : Fin h) := if e : i.val < x.1 then x.2 ⟨i.val, e⟩ else 0
  refine ⟨f, funext fun i => ?_⟩
  simp [ancestor, f, show i.val < x.1.val from i.isLt]
  rfl

theorem near_iff [Fintype V] (N : V → Finset V) (D : ℕ) (x y : Site V h) :
    y ∈ near N D x ↔ y = x ∨ y.1 ∈ N x.1 ∧ ((), y.2) ∈ close D x.2 := by
  rw [mem_near, close, mem_near]
  constructor
  · rintro (rfl | ⟨ha, hb, hc, hd⟩)
    · exact .inl rfl
    · exact .inr ⟨ha, .inr ⟨by simp, hb, hc, hd⟩⟩
  · rintro (rfl | ⟨ha, he | ⟨_, hb, hc, hd⟩⟩)
    · exact .inl rfl
    · have hj : y.2 = x.2 := congrArg (fun p : Site Unit h => p.2) he
      rcases x with ⟨v, j⟩
      rcases y with ⟨w, k⟩
      change k = j at hj
      subst k
      obtain ⟨i, hi⟩ := interval_contains j
      exact .inr ⟨ha, ⟨i, hi, hi⟩, Nat.le_add_right _ _, Nat.le_add_right _ _⟩
    · exact .inr ⟨ha, hb, hc, hd⟩

def width (h D : ℕ) := min (h + 1) (Nat.clog 2 ((4 * D) ^ 300))

private theorem close_card (hD : 0 < D) (x : Interval h) :
    (close D x).card ≤ 2 ^ width h D := by
  unfold width
  rcases min_choice (h + 1) (Nat.clog 2 ((4 * D) ^ 300)) with e | e <;> rw [e]
  · refine (Finset.card_le_univ _).trans ?_
    simpa [pow_succ'] using Site.card Unit h
  · exact (near_card _ _ hD (by simp; omega) _).trans (Nat.le_pow_clog (by decide) _)

def seat (h D : ℕ) (x : B (h + 1)) (j : B (width h D)) : Option (B (h + 1)) :=
  if hx : x ∈ Set.range (intervalCode h) then
    let S := close D hx.choose
    if hj : j.val < S.card then some (intervalCode h (S.equivFin.symm ⟨j.val, hj⟩).val.2)
    else none
  else none

private theorem seat_at (x : Interval h) (j : B (width h D)) :
    seat h D (intervalCode h x) j =
      if e : j.val < (close D x).card then
        some (intervalCode h ((close D x).equivFin.symm ⟨j.val, e⟩).val.2) else none := by
  have hx : intervalCode h x ∈ Set.range (intervalCode h) := ⟨x, rfl⟩
  have eq := (intervalCode h).injective hx.choose_spec
  rw [seat, dite_eq_left hx, eq]

theorem hits (hD : 0 < D) (x : Interval h) (y : B (h + 1)) :
    (∃ j, seat h D (intervalCode h x) j = some y) ↔
      ∃ w : Interval h, ((), w) ∈ close D x ∧ intervalCode h w = y := by
  let S := close D x
  constructor
  · rintro ⟨j, hj⟩
    rw [seat_at] at hj
    split at hj
    next h =>
      let p := S.equivFin.symm ⟨j.val, h⟩
      exact ⟨p.val.2, p.property, Option.some.inj hj⟩
    next => contradiction
  · rintro ⟨w, hw, rfl⟩
    let j := S.equivFin ⟨((), w), hw⟩
    refine ⟨Fin.castLE (close_card hD x) j, ?_⟩
    rw [seat_at, dite_eq_left (show (Fin.castLE (close_card hD x) j).val < (close D x).card from j.isLt)]
    change some (intervalCode h (S.equivFin.symm j).val.2) = _
    rw [show S.equivFin.symm j = _ from S.equivFin.symm_apply_apply _]

abbrev Input (m d : ℕ) := Format.vec m (.vec d (.pair .bit (.addr m)))
abbrev nextWidth (h D d : ℕ) := (d + width h D + 1) * 3

def step (h D : ℕ) (x : (Input m d).obj) (i : B (m + (h + 1))) (j : B (d + width h D)) :=
  let p := Match.rowIndex m (h + 1) i
  let q := Match.rowIndex d (width h D) j
  let r := x p.1 q.1
  if r.1 then (seat h D p.2 q.2).elim i (fun z => (Match.rowIndex m (h + 1)).symm (r.2, z)) else i

def neighbors (h D : ℕ) (x : (Input m d).obj) : (Neighborhood.Rows (m + (h + 1)) (nextWidth h D d)).obj :=
  Neighborhood.expand 3 (step h D x)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Child
end

/-! # Exact support of the child host dictionary -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Child
open Packing Coloring Neighborhood
open scoped Classical
variable {V : Type} {m d h D : ℕ} {N : V → Finset V} {p : V ↪ B m} {X : (Input m d).obj}

structure Presents (N : V → Finset V) (p : V ↪ B m) (X : (Input m d).obj) : Prop where
  live : ∀ v u, (∃ i, X (p v) i = (true, u)) ↔ ∃ w ∈ N v, p w = u
  idle : ∀ v ∉ Set.range p, ∀ i, (X v i).1 = false

theorem Presents.step_idle (H : Presents N p X) {x : B (m + (h + 1))}
    (hx : x ∉ Set.range (host p h)) (i : B (d + width h D)) : step h D X x i = x := by
  let y := Match.rowIndex m (h + 1) x
  by_cases hp : y.1 ∈ Set.range p
  · obtain ⟨v, hv⟩ := hp
    have hi : y.2 ∉ Set.range (intervalCode h) := by
      rintro ⟨k, hk⟩
      refine hx ⟨(v, k), (Match.rowIndex m (h + 1)).injective ?_⟩
      rw [host_parts]
      exact Prod.ext hv hk
    have hs (j) : seat h D y.2 j = none := dite_eq_right hi
    unfold step
    simp only [show (Match.rowIndex m (h + 1)) x = y from rfl, hs, Option.elim_none, ite_self]
  · unfold step
    simp only [show (Match.rowIndex m (h + 1)) x = y from rfl, H.idle _ hp, Bool.false_eq_true,
      ↓reduceIte]

theorem Presents.idle_neighbors (H : Presents N p X) {x : B (m + (h + 1))}
    (hx : x ∉ Set.range (host p h)) (i : B (nextWidth h D d)) : neighbors h D X x i = x := by
  have go {k y} (hy : Reach (step h D X) k x y) : y = x := by
    induction k with
    | zero => exact Eq.symm hy
    | succ k ih =>
      obtain ⟨z, hz, he⟩ := hy
      have eq : z = x := hz.elim id (fun ⟨j, hj⟩ => hj.symm.trans (H.step_idle hx j))
      exact ih (eq ▸ he)
  exact go (k := 3) (Neighborhood.mem.mp ⟨i, rfl⟩)

variable [Fintype V] (H : Presents N p X) (hD : 0 < D)
include H hD

theorem Presents.step_mem (v : Site V h) (y : B (m + (h + 1))) :
    (y = host p h v ∨ ∃ i, step h D X (host p h v) i = y) ↔
      ∃ u ∈ near N D v, host p h u = y := by
  have idle : ∃ u ∈ near N D v, host p h u = host p h v := ⟨v, near_self .., rfl⟩
  constructor
  · rintro (rfl | ⟨i, rfl⟩)
    · exact idle
    let t := Match.rowIndex d (width h D) i
    simp only [step, host_parts]
    change ∃ u ∈ _, host p h u = if (X (p v.1) t.1).1 then
      (seat h D (intervalCode h v.2) t.2).elim _ _ else _
    cases he : X (p v.1) t.1 with
    | mk b z =>
      cases b
      · exact idle
      cases hz : seat h D (intervalCode h v.2) t.2 with
      | none => exact idle
      | some w =>
        obtain ⟨a, ha, rfl⟩ := (H.live v.1 z).mp ⟨t.1, he⟩
        obtain ⟨b, hb, rfl⟩ := (hits hD v.2 w).mp ⟨t.2, hz⟩
        exact ⟨(a, b), (near_iff _ _ _ _).mpr (.inr ⟨ha, hb⟩), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    rcases (near_iff _ _ _ _).mp hu with rfl | ⟨ha, hb⟩
    · exact .inl rfl
    obtain ⟨i, hi⟩ := (H.live _ _).mpr ⟨_, ha, rfl⟩
    obtain ⟨j, hj⟩ := (hits hD _ _).mpr ⟨_, hb, rfl⟩
    refine .inr ⟨(Match.rowIndex d (width h D)).symm (i, j), ?_⟩
    simp only [step, host_parts, Equiv.apply_symm_apply, hi, hj, ↓reduceIte, Option.elim_some]
    rfl

theorem Presents.mem (v : Site V h) (y : B (m + (h + 1))) :
    (∃ i, neighbors h D X (host p h v) i = y) ↔ ∃ u ∈ cube (near N D) v, host p h u = y := by
  unfold neighbors
  rw [Neighborhood.mem]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, rfl⟩
    obtain ⟨a, hva, rfl⟩ := (H.step_mem hD _ _).mp ha
    obtain ⟨b, hab, rfl⟩ := (H.step_mem hD _ _).mp hb
    obtain ⟨c, hbc, rfl⟩ := (H.step_mem hD _ _).mp hc
    exact ⟨c, (mem_cube ..).mpr ⟨a, hva, b, hab, hbc⟩, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨a, ha, b, hb, he⟩ := (mem_cube ..).mp hu
    exact ⟨_, (H.step_mem hD _ _).mpr ⟨a, ha, rfl⟩, _, (H.step_mem hD _ _).mpr ⟨b, hb, rfl⟩,
      _, (H.step_mem hD _ _).mpr ⟨u, he, rfl⟩, rfl⟩

theorem Presents.reciprocal (hs : ∀ v u, u ∈ N v → v ∈ N u)
    (A : Format) (f : B (m + (h + 1)) → A.obj) :
    Fmt.Reciprocal A (fun i => (neighbors h D X i, f i)) := by
  intro x j hj
  by_cases hx : x ∈ Set.range (host p h)
  · obtain ⟨v, rfl⟩ := hx
    obtain ⟨u, hu, he⟩ := (H.mem hD v _).mp ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := (H.mem hD u _).mpr ⟨v, cube_symm _ (near_symm hs D) _ _ hu, rfl⟩
    rw [he] at hi
    exact ⟨i, hi, fun _ hk => Neighborhood.unique hk hi hj.symm⟩
  · exact (hj (H.idle_neighbors hx j)).elim

omit H hD

def select (test : B d → Bool) : B d :=
  if test 0 then 0 else if h : ∃ i, test i = true then h.choose else 0

theorem select_spec (test : B d → Bool) (h : ∃ i, test i = true) : test (select test) = true := by
  unfold select
  split
  · assumption
  · exact h.choose_spec

def index (g : B m → B d → B m) (x y : B m) : B d :=
  select (fun i => decide (g x i = y))

include H hD in
theorem Presents.nav (x y : Site V h) (hy : y ∈ cube (near N D) x) :
    let g := neighbors h D X
    g (host p h x) (index g (host p h x) (host p h y)) = host p h y := by
  obtain ⟨i, hi⟩ := (H.mem hD x _).mpr ⟨y, hy, rfl⟩
  exact of_decide_eq_true (select_spec (fun i => decide (neighbors h D X (host p h x) i = host p h y)) ⟨i, decide_eq_true hi⟩)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Child
end

/-! # The grouping record at a host and group index -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Group
open Coloring

abbrev Flags (d : ℕ) := Format.vec d (.pair .bit .bit)
abbrev Parcel (d a h b : ℕ) := Format.pair .bit (.pair (Flags d) (.vec a (.vec h (.addr b))))
abbrev Input (m d a h b : ℕ) := Fmt.bank m d (Parcel d a h b)
abbrev Patches (m d a h b : ℕ) := Format.vec (m + a) (Patch ((d + 1) * h) h b)

variable {m d a h b : ℕ} (X : (Input m d a h b).obj)

def hosts := Neighborhood.expand h (fun j => (X j).1)

def links (y z : B m) : Bool × Bool :=
  (decide (∃ j, (X y).1 j = z ∧ ((X y).2.2.1 j).1 = true),
   decide (∃ j, (X y).1 j = z ∧ ((X y).2.2.1 j).2 = true))

def patches : (Patches m d a h b).obj := fun t =>
  let i := Match.rowIndex m a t
  let p := hosts X i.1
  ((X i.1).2.1, fun j k => links X (p j) (p k), fun j => (X (p j)).2.2.2 i.2)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Group
end

/-! # Interpreting the live rows of a grouping controller -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Group

open Coloring Packing Neighborhood
open scoped Classical

variable {V : Type} {m d a h b Δ D : ℕ}

def embed (g : V ↪ B m) (a : ℕ) : V × Cell a ↪ B (m + a) :=
  (g.prodMap (cellIndex a).toEmbedding).trans (Match.rowIndex m a).symm.toEmbedding

@[simp] theorem row_embed (g : V ↪ B m) (x : V × Cell a) :
    Match.rowIndex m a (embed g a x) = (g x.1, cellIndex a x.2) :=
  (Match.rowIndex m a).apply_symm_apply _

private theorem pad_reach {q : B m → B d → B m} {x y : B m} {r t : ℕ}
    (hp : Reach q r x y) (h : r ≤ t) : Reach q t x y := by
  induction t, h using Nat.le_induction with
  | base => exact hp
  | succ _ _ ih => exact ih.tail (.inl rfl)

private theorem delay_pos (C : V → Finset V) (hΔ : 0 < Δ) (hD : 0 < D) (x y : V) :
    0 < delay C Δ D x y := by
  apply Nat.mul_pos (by decide : 0 < 32)
  apply Nat.clog_pos (by decide)
  split_ifs <;> omega

variable (X : (Input m d a h b).obj) (g : V ↪ B m)
  (E C : V → Finset V) (l : V × Cell a → Cell h → ℝ) (f : B b → ℝ)

/-- The two masks distinguish graph edges and core edges from padding.
The address of every neighbor of a live host is itself live. -/
structure Presents : Prop where
  live : ∀ i, (X i).2.1 = true ↔ i ∈ Set.range g
  closed : ∀ v j, (X (g v)).1 j ∈ Set.range g
  edge : ∀ v y, y ∈ E v ↔ ∃ j, (X (g v)).1 j = g y ∧ ((X (g v)).2.2.1 j).1 = true
  core : ∀ v y, y ∈ C v ↔ ∃ j, (X (g v)).1 j = g y ∧ ((X (g v)).2.2.1 j).2 = true
  load : ∀ v i j, f ((X (g v)).2.2.2 (cellIndex a i) (cellIndex h j)) = l (v, i) j

variable {X g E C l f} (H : Presents X g E C l f)
include H

private theorem live_reach {k : ℕ} {x y : B m}
    (hw : Reach (fun i => (X i).1) k x y) (hx : x ∈ Set.range g) : y ∈ Set.range g := by
  induction k generalizing x with
  | zero => exact hw ▸ hx
  | succ k ih =>
    obtain ⟨z, hz, hw⟩ := hw
    refine ih hw ?_
    rcases hz with rfl | ⟨i, rfl⟩
    · exact hx
    · obtain ⟨v, rfl⟩ := hx
      exact H.closed v i

private theorem walk_reach (hΔ : 0 < Δ) (hD : 0 < D) {v y : V × Cell a} {k : ℕ}
    (hw : Walk (inGroup a E) (delay (inGroup a C) Δ D) v k y) :
    Reach (fun i => (X i).1) k (g v.1) (g y.1) := by
  induction hw with
  | root => rfl
  | @edge k p q _ he ih =>
    obtain ⟨j, hj, _⟩ := (H.edge _ _).mp ((mem_inGroup ..).mp he).1
    have := delay_pos (inGroup a C) hΔ hD p q
    exact pad_reach (ih.tail (.inr ⟨j, hj⟩)) (by omega)

theorem Presents.represents (hΔ : 0 < Δ) (hD : 0 < D) :
    Represents (inGroup a E) (delay (inGroup a C) Δ D) l Δ D f (patches X) (embed g a) := by
  constructor
  · intro i
    change (X (Match.rowIndex m a i).1).2.1 = true ↔ _
    rw [H.live]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨(v, (cellIndex a).symm (Match.rowIndex m a i).2), (Match.rowIndex m a).injective ?_⟩
      simp [hv]
    · rintro ⟨v, rfl⟩
      exact ⟨v.1, by rw [row_embed]⟩
  intro v
  have hs (i) : hosts X (g v.1) i ∈ Set.range g :=
    live_reach H (Neighborhood.mem.mp ⟨i, rfl⟩) ⟨v.1, rfl⟩
  choose y hy using hs
  let p i := (y i, v.2)
  have hp : p 0 = v := Prod.ext (g.injective ((hy 0).trans Neighborhood.origin)) rfl
  let q := patches X (embed g a v)
  have ha (i j) : j ∈ graph q i ↔ p j ∈ inGroup a E (p i) := by
    simp only [graph, Finset.mem_filter, Finset.mem_univ, true_and, q, patches, row_embed,
      ← hy, links, decide_eq_true_eq, mem_inGroup, p, and_true]
    exact (H.edge _ _).symm
  have hc (i j) : j ∈ Group.core q i ↔ p j ∈ inGroup a C (p i) := by
    simp only [Group.core, Finset.mem_filter, Finset.mem_univ, true_and, q, patches, row_embed,
      ← hy, links, decide_eq_true_eq, mem_inGroup, p, and_true]
    exact (H.core _ _).symm
  refine ⟨p, hp, ⟨?_, ?_⟩, ?_⟩
  · intro i j hj
    refine ⟨(ha i j).mp hj, ?_⟩
    change delay (Group.core q) Δ D i j = _
    simp only [delay, hc]
    split <;> rfl
  · intro i j k hw he hk
    have hr := pad_reach (walk_reach H hΔ hD (hw.edge he)) hk.le
    rw [hp] at hr
    obtain ⟨t, ht⟩ := Neighborhood.mem.mpr hr
    have eq : p t = j :=
      Prod.ext (g.injective ((hy t).trans ht)) ((mem_inGroup ..).mp he).2.symm
    exact ⟨t, (ha i t).mpr (eq ▸ he), eq⟩
  · funext i j
    simp only [Group.load, patches, row_embed, ← hy, H.load, Function.comp_apply, p]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Group
end

/-! # Computing the child contact lists -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Child

open Coloring Install
open scoped Classical

variable {m d h D : ℕ}

/-- The seat of a candidate is fixed by the output index. Each output
bit reads an activity flag and at most one parent-address bit. -/
theorem step_depends :
    Depends ((Neighborhood.Rows (m + (h + 1)) (d + width h D)).code ∘
      step h D ∘ (Input m d).code.symm) 2 := by
  rintro ⟨i, j, b⟩
  let p := Match.rowIndex m (h + 1) i
  let q := Match.rowIndex d (width h D) j
  let T := Input m d
  let r (x : T.pins → Bool) := T.code.symm x p.1 q.1
  let flag : T.pins := (p.1, q.1, .inl ())
  obtain ⟨k, hk⟩ := Match.append_pin m (h + 1) b
  let bit : T.pins := k.elim (fun z => (p.1, q.1, .inr z)) (fun _ => flag)
  refine ⟨{flag, bit}, Finset.card_le_two, fun x y he => ?_⟩
  have flags (v : T.pins → Bool) : (r v).1 = v flag :=
    congrFun (T.code.apply_symm_apply v) flag
  have parent (v : T.pins → Bool) (z : slots (word m)) :
      (Format.addr m).code (r v).2 z = v (p.1, q.1, .inr z) :=
    congrFun (T.code.apply_symm_apply v) (p.1, q.1, .inr z)
  have selected : (r x).1 = (r y).1 := by rw [flags, flags, he flag (by simp)]
  let out (v : T.pins → Bool) :=
    if (r v).1 then (seat h D p.2 q.2).elim i (fun z => (Match.rowIndex m (h + 1)).symm ((r v).2, z))
    else i
  change (Format.addr _).code (out x) b = (Format.addr _).code (out y) b
  unfold out
  rw [selected]
  split
  · cases seat h D p.2 q.2 with
    | none => rfl
    | some z =>
      simp only [Option.elim_some, hk]
      have hbit := he bit (by simp)
      cases k with
      | inl k => simpa only [Sum.elim_inl, parent, bit] using hbit
      | inr k => rfl
  · rfl

variable (F : Type) [Field F]

/-- Construct the one-step graph and then enumerate the third neighborhood. -/
theorem cheap (m d h D : ℕ) :
    Cheap F (m + (h + 1)) (m + (h + 1) + 2 ^ nextWidth h D d)
      (Input m d) (Neighborhood.Rows (m + (h + 1)) (nextWidth h D d)) (neighbors h D) 201 := by
  let M := m + (h + 1)
  let n := d + width h D
  let t := M + 2 ^ nextWidth h D d
  have hn : 2 ^ n ≤ 100 + t := by
    have h' := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show n ≤ nextWidth h D d by unfold n nextWidth; omega)
    unfold t
    omega
  have hd : 2 ^ d ≤ 100 + t :=
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right d _)).trans hn
  have hM : M ≤ 100 + t := (Nat.le_add_right M _).trans (Nat.le_add_left _ _)
  have hm : 1 + m ≤ 100 + t := (show 1 + m ≤ M by unfold M; omega).trans hM
  have hm' : 2 ^ m ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  have hi : (Input m d).width ≤ 2 ^ M * (100 + t) ^ 2 := by
    rw [Format.width_vec, Format.width_vec, Format.width_pair, Format.width_bit, Format.width_addr,
      pow_two]
    exact Nat.mul_le_mul hm' (Nat.mul_le_mul hd hm)
  have ho : (Neighborhood.Rows M n).width ≤ 2 ^ M * (100 + t) ^ 2 := by
    rw [Format.width_vec, Format.width_vec, Format.width_addr, pow_two]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hn hM)
  have stepCheap : Cheap F M t (Input m d) (Neighborhood.Rows M n) (step h D) 3 := by
    refine ⟨_, step_depends.bnet F, ?_⟩
    change (Input m d).width + (Neighborhood.Rows M n).width +
      ((Input m d).width + 68 * (Neighborhood.Rows M n).width) ≤ _
    calc
      _ ≤ 100 * (2 ^ M * (100 + t) ^ 2) := by omega
      _ ≤ _ := by
        rw [mul_comm 100, pow_succ (100 + t) 2, ← mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.le_add_right 100 t)
  exact stepCheap.comp (Neighborhood.cheap F M n 3 (by decide))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Child
end
