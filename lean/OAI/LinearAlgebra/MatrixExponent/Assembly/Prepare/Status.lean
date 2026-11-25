import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Contacts
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Terminal
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Hop
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.One
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents

/-! # Preparing the common pattern and host chart for local concentration -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing Rounds
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} (D : Template F)

structure Binning (a H T R : ℕ) (θ : ℝ) : Prop where
  ha : a < D.scheme.h
  hH : (4 * 5) ^ 300 < H
  hT : 0 < T
  hR : 0 < R
  hRT : R * H ^ 2 ≤ T
  floor : 0 < θ

namespace Binning
variable {D} {a H T R : ℕ} {θ L : ℝ} (B : D.Binning a H T R θ)

omit [Field F] in
theorem pos (B : D.Binning a H T R θ) : 0 < H := (Nat.zero_le _).trans_lt B.hH

abbrev depth (_ : D.Binning a H T R θ) := Presents.Plan.depth H θ
abbrev raw := Parcel.scheme D.scheme (D.childM a) (D.childD a 5) a (Sheet.slots H) B.depth
abbrev target := B.raw.padded R
abbrev frame (r : D.format.obj) := D.childFrame a B.ha 5 H T r B.pos B.depth
abbrev data (r : D.format.obj) : B.target.format.obj := Parcel.encode D.scheme (B.frame r)

variable {r : D.format.obj} {P : Rounds.Board F x y D.scheme.h} (p : D.Presents r P)

/-- A branch of the input family with a grouping elected by the controller. -/
structure Trial (L : ℝ) where
  ready : P.Ready 5 H T L θ
  slack : (P.seats : ℝ) * H * T ≤ L * (2 : ℝ) ^ (D.scheme.h - a)
  ext : ((wd x + wd y : ℕ) : ℝ) * H ≤ L
  neutral : ∀ v, P.diagram.arity v = 0 → ∀ t, Transcript.sample (P.diagram.table v) t = 1
  loopless : ∀ i, P.diagram.source i ≠ P.diagram.target i
  plan : p.Plan B.ha 5 H T

namespace Trial
variable {B p} (t : B.Trial p L)

private theorem five : 0 < 5 := by decide
abbrev cells := t.plan.cells five B.pos B.hT t.ready t.slack
abbrev bin := t.plan.bin five B.pos B.hT t.ready t.slack

theorem sep : (Cells.before P).Separated (t.cells.seat t.bin) :=
  t.plan.separated five B.pos B.hT t.ready t.slack t.loopless
theorem room : t.plan.Room B.depth := t.plan.room five B.pos B.hT t.ready t.slack B.floor

abbrev layout := t.plan.manifest B.pos five B.hT t.ready t.slack t.room
abbrev input := t.plan.input five B.pos B.hT t.ready t.slack B.hH B.hR B.hRT t.ext
abbrev post : B.target.Presentation (B.data r) t.input.diagram :=
  t.layout.padded t.sep t.neutral p.directed R

theorem directed : t.post.Directed := t.layout.padded_directed t.sep t.neutral p.directed R

def chart : t.input.HostChart B.target (B.data r) where
  host := Child.host p.host (D.scheme.h - a)
  block := (cellIndex a).toEmbedding
  adjacent _ _ hij _ := ⟨_, Presents.Plan.reach (p := p) (ha := B.ha) five hij⟩
  reciprocal := (Presents.Plan.childPresent p B.ha).reciprocal five P.sym _ _

def mobile (B : D.Binning a H T R θ) (v : B.target.Vtx) := decide (v.2.2 ≠ 0)

theorem location (v : t.input.diagram.V) :
    ((t.post.vertex v).1, (t.post.vertex v).2.1) = t.chart.coord (t.input.grid.cell v) := rfl

theorem flag (v : t.input.diagram.V) : decide (t.input.mobile v) = mobile B (t.post.vertex v) := by
  unfold mobile
  apply decide_eq_decide.mpr
  change v.val.2 ≠ none ↔ Sheet.number H v.val.2 ≠ 0
  rw [← Sheet.number_none H, (Sheet.number H).injective.ne_iff]

abbrev normal (q : ℕ) := t.chart.normalized t.post t.directed q
abbrev order := t.post.toOrdered t.directed
abbrev atlas (q : ℕ) := t.chart.next t.post t.directed q

theorem placed (q : ℕ) : (t.normal q).Placed t.order (t.atlas q).coord
    (fun i => ((t.atlas q).tone q i).val) (mobile B) :=
  t.chart.normalized_placed t.post t.directed q (mobile B) t.location t.flag

theorem ranks (q : ℕ) (h : 2 ≤ q) : (t.normal q).LocalRanks :=
  t.chart.normalized_ranks t.post t.directed q h (mobile B) t.location t.flag

theorem eval (q : ℕ) : (t.normal q).diagram.eval = P.diagram.eval :=
  (t.input.normalize_eval _ _ _).trans
    (t.plan.input_eval five B.pos B.hT t.ready t.slack t.loopless B.hH B.hR B.hRT t.ext t.neutral)

theorem seats (q : ℕ) : Fintype.card (t.normal q).V * 2 ^ a ≤ 2 * P.seats := t.cells.seats

end Trial
end Binning
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # Size of the grouped station records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
open Coloring

variable {F : Type} [Field F] {D : Template F} {a H T R : ℕ} {θ : ℝ} (b : D.Binning a H T R θ)

theorem fields :
    b.target.ℓ = 2 ^ b.depth * (Sheet.slots H + (D.scheme.ℓ + 2 ^ D.scheme.e * (b.target.d + (Sheet.slots H + b.depth)))) :=
  Parcel.width D.scheme _ _ _

theorem shape : b.target.m = D.scheme.m + (D.scheme.h - a + 1) ∧ b.target.h = a ∧
    b.target.d = D.childD a 5 ∧ b.target.k = Sheet.slots H ∧ b.target.e = b.depth + D.scheme.e + 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem capacity : 2 ^ b.target.m * 2 ^ b.target.h = 2 * (2 ^ D.scheme.m * 2 ^ D.scheme.h) := by
  rw [b.shape.1, b.shape.2.1, ← pow_add, ← pow_add, ← pow_succ']
  have := b.ha
  congr 1; omega

private theorem clog_bound (n : ℕ) : 2 ^ Nat.clog 2 n ≤ 2 * (n + 1) := by
  cases h : Nat.clog 2 n with
  | zero => rw [pow_zero]; omega
  | succ i =>
    have he : ¬ n ≤ 2 ^ i := by
      intro hn
      have := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hn
      omega
    rw [pow_succ']
    exact Nat.mul_le_mul_left _ (by omega)

private theorem large (n : ℕ) (h : 2 ≤ n) : 64 ≤ (4 * 5 : ℕ) ^ n :=
  (by decide : 64 ≤ (4 * 5 : ℕ) ^ 2).trans (Nat.pow_le_pow_right (by decide) h)

private theorem bounded_slots {N K : ℕ} (n : ℕ) (h : N < K) :
    2 ^ min n (Nat.clog 2 N) ≤ 2 * K :=
  (Nat.pow_le_pow_right (by decide) (min_le_right ..)).trans
    ((clog_bound N).trans (Nat.mul_le_mul_left 2 h))

theorem nav_bound (hd : D.scheme.d ≤ 4) : 2 ^ (b.target.d + 1) ≤ H ^ 10 := by
  have hH : 64 ≤ H := (large 300 (by decide)).trans b.hH.le
  have hw : 2 ^ Child.width (D.scheme.h - a) 5 ≤ 2 * H := bounded_slots _ b.hH
  have hs : 2 ^ (D.scheme.d + Child.width (D.scheme.h - a) 5 + 1) ≤ H ^ 2 := calc
    _ = (2 ^ D.scheme.d * 2 ^ Child.width (D.scheme.h - a) 5) * 2 := by rw [pow_succ, pow_add]
    _ ≤ (2 ^ 4 * (2 * H)) * 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hd) hw)
    _ = 64 * H := by ring
    _ ≤ H ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right H hH
  change 2 ^ ((D.scheme.d + Child.width (D.scheme.h - a) 5 + 1) * 3 + 1) ≤ _
  rw [pow_succ, pow_mul]
  calc
    _ ≤ (H ^ 2) ^ 3 * H := Nat.mul_le_mul (Nat.pow_le_pow_left hs _) (by omega)
    _ = H ^ 7 := by rw [← pow_mul, ← pow_succ]
    _ ≤ _ := Nat.pow_le_pow_right b.pos (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
end

/-!
# Recovering the predecessor of an exterior span

The new host address includes the old host as a prefix. Within
that host the active-row rank determines the old suffix and the
span number retains the old stub.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
open Coloring Packing Rounds BatchDescent
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {D : Template F} {a H T R : ℕ} {θ L : ℝ}
    (b : D.Binning a H T R θ)

local notation "n" => D.scheme.h - a
local notation "parent" => Match.rowIndex D.scheme.m (n + 1)

def pointer (q : (D.Sheet n).obj) (z : B (n + 1)) (l : B a) (e : B b.target.e) : Option (B 0 × Trail.Stub D.scheme) :=
  let u := (Parcel.index b.depth D.scheme.e).symm ((Pattern.tag b.raw.e).symm e).2
  (Sheet.find D q b.depth z u.2.1).map (fun j => (0, D.position a b.ha.le l j, 0, u.2.2))

def marked (q : (D.Sheet n).obj) (z : B (n + 1)) (l : B a) (s : B b.target.ℓ)
    (v : B b.target.k) (e : B b.target.e) :=
  if 0 < (b.target.decode s).width v e ∧ (b.target.decode s).peer v e = none
  then b.pointer q z l e else none

def move (r : D.format.obj) : Trail.Move D.scheme b.target 0 where
  nav i _ := (parent i).1
  read q :=
    let i := parent q.1.1
    b.marked (D.sheet a b.ha 5 H T r i.1 q.1.2.1) i.2 q.1.2.1 ((b.data r q.1.1).2 q.1.2.1)
      q.1.2.2 q.2

theorem read_eq (r : D.format.obj) (q : b.target.Span) :
    (b.move r).read q =
      if 0 < b.target.width (b.data r) q ∧ b.target.peer (b.data r) q = none then
        b.pointer (D.sheet a b.ha 5 H T r (parent q.1.1).1 q.1.2.1) (parent q.1.1).2 q.1.2.1 q.2
      else none := by
  simp only [move, marked, Scheme.width, Scheme.peer, Scheme.pattern, Option.map_eq_none_iff]

namespace Trial
variable {b} {r : D.format.obj} {P : Rounds.Board F x y D.scheme.h} {p : D.Presents r P}
  (t : b.Trial p L)

private theorem outer_eq {S : Scheme F} {r : S.format.obj} {G : Diagram F x y} (p : S.Presentation r G)
    (i : slots x ⊕ slots y) : (p.boundary i).val = p.toSeating.ends (boundaryEnd G i) := by cases i <;> rfl

theorem outer (i : slots x ⊕ slots y) :
    (t.order.boundary i).val = b.raw.liftPad (b.data r) R false (t.layout.route (Parcel.copy P.diagram false i)) := by
  rw [outer_eq, order, Scheme.Presentation.ordered_ends]
  exact t.layout.padded_end t.sep t.neutral p.directed R i

def dest (v : P.diagram.V) (s : B D.scheme.e) :=
  b.raw.seatPad R false (t.layout.span (some false) v s)

theorem outer_span (i : slots x ⊕ slots y) :
    (t.order.boundary i).val.1 = t.dest (portEnd P.diagram i) (p.pres.boundary i).val.1.2 := by
  rw [t.outer, outer_eq]
  exact congrArg (b.raw.seatPad R false) (t.layout.copy_span false i)

private theorem dest_eq (v : P.diagram.V) (s : B D.scheme.e) :
    t.dest v s = (((t.plan.addr v).1, (t.plan.addr v).2, 0),
      Pattern.tag b.raw.e (false, Parcel.index b.depth D.scheme.e (false, t.plan.rank b.depth v, s))) := rfl

private theorem pointer_eq (v : P.diagram.V) (hv : 0 < P.diagram.arity v) (s : B D.scheme.e) :
    let q := t.dest v s
    b.pointer (D.sheet a b.ha 5 H T r (parent q.1.1).1 q.1.2.1) (parent q.1.1).2 q.1.2.1 q.2 =
      some (0, (p.pres.vertex v).2.1, 0, s) := by
  simp only [dest_eq, Presents.Plan.addr, Presents.Plan.cell_parts, Equiv.apply_symm_apply, pointer, Equiv.symm_apply_apply]
  rw [t.plan.found t.room v hv, Option.map_some, Presents.Plan.given (ha := b.ha)]

theorem follows : (b.move r).Agrees p.pres t.order where
  mapped i := by
    let v := portEnd P.diagram i
    let s := (p.pres.boundary i).val.1.2
    have he : (p.pres.boundary i).val.1 = (p.pres.vertex v, s) := by
      refine Prod.ext ?_ rfl
      rw [outer_eq, p.pres.end_station, station_boundary]
    have hp : 0 < P.diagram.arity v := Parcel.Manifest.positive (he ▸ (p.pres.boundary i).val.2.pos)
    have hz := (t.order.boundary i).property
    have hw := (t.order.boundary i).val.2.pos
    refine ⟨?_, ?_, ?_⟩
    · rw [Trail.Move.previous, read_eq, ite_eq_left ⟨hw, hz⟩, t.outer_span, t.pointer_eq v hp, Option.map_some, he]
      simp only [move, dest_eq, Presents.Plan.addr, Presents.Plan.cell_parts, Equiv.apply_symm_apply, Trail.locate]
      rw [p.vertex]
    · rw [t.outer_span, dest, Scheme.width_pad, he]
      exact t.layout.width_eq hp s (some false) (fun _ => he ▸ (p.pres.boundary i).property)
    · rw [t.outer, outer_eq]
      exact (t.layout.offset _).trans (by rw [Parcel.axis_copy])
  active s hs := by
    rw [read_eq] at hs
    split at hs
    · rename_i ht
      obtain ⟨q, hq⟩ := t.order.boundary.surjective ⟨⟨s, ⟨0, ht.1⟩⟩, ht.2⟩
      exact ⟨q, congrArg (fun x => x.val.1) hq⟩
    · contradiction

end Trial
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
end

/-! # Grouping and padding do not increase the set of origins at a host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
open Coloring Packing Rounds BatchDescent
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {D : Template F} {a H T R : ℕ} {θ L : ℝ}
    (b : D.Binning a H T R θ)

abbrev parent (i : B b.target.m) := (Match.rowIndex D.scheme.m (D.scheme.h - a + 1) i).1

namespace Trial
variable {b} {r : D.format.obj} {P : Rounds.Board F x y D.scheme.h} {p : D.Presents r P}
  (t : b.Trial p L)

theorem ancestor_owner (i : slots x ⊕ slots y) :
    b.parent (t.order.boundary i).val.1.1.1 = (p.pres.boundary i).val.1.1.1 := by
  have h := (t.follows.mapped i).1
  obtain ⟨s, _, he⟩ := Option.map_eq_some_iff.mp h
  exact congrArg (fun v : D.scheme.Span => v.1.1) he

include t in
theorem load_le (i : B b.target.m) :
    b.target.load (b.data r) i ≤ D.scheme.load r.1 (b.parent i) := by
  let f := t.order.boundary.symm.trans p.pres.boundary
  have he (j : b.target.exposed (b.data r)) :
      D.scheme.owner r.1 (f j) = b.parent (b.target.owner (b.data r) j) := by
    obtain ⟨s, rfl⟩ := t.order.boundary.surjective j
    rw [show f (t.order.boundary s) = p.pres.boundary s by simp only [f, Equiv.trans_apply, Equiv.symm_apply_apply]]
    exact (t.ancestor_owner s).symm
  let g (x : b.target.fiber (b.data r) i) : D.scheme.fiber r.1 (b.parent i) :=
    ⟨f x.val, by rw [he, x.property]⟩
  exact Fintype.card_le_of_injective g fun _ _ h => Subtype.ext (f.injective (congrArg Subtype.val h))

include t in
theorem fits {k v : ℕ} (h : D.scheme.Fits r.1 v k) :
    b.target.Fits (b.data r) (2 ^ b.target.m + wd x + wd y) k :=
  t.order.fits le_rfl (fun i => (t.load_le i).trans (h.2 _))

variable {h u : ℕ} {Q : Rounds.Board F (copies x (2 ^ h * u)) (copies y (2 ^ h * u)) D.scheme.h}
  {q : D.Presents r Q} (s : b.Trial q L)

theorem origins_le (i : B b.target.m) :
    Trail.origins s.order i ⊆ Trail.origins q.pres (b.parent i) := by
  intro j hj
  obtain ⟨_, u, v, he⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, v, (s.ancestor_owner _).symm.trans (congrArg b.parent he)⟩

theorem tracks {d e : ℕ} {name : Stack.Outer x y ↪ (Fin e → Bool)}
    {z : Trail.Record D.scheme h d e} (hu : 0 < u) (hd : 0 < d)
    (cap : ∀ i, (Trail.origins q.pres i).card ≤ d) (hT : Trail.Tracks q.pres name z) :
    Trail.Tracks s.order name ((b.move r).update d z) :=
  hT.update s.follows hu hd fun i => (Finset.card_le_card (s.origins_le i)).trans (cap _)

end Trial
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
end

/-!
# Host status and the exact one-step graph

Routing uses the third neighborhood. The shorter list of actual
neighbors is marked in this list by a Boolean column per host.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
open Coloring Packing Rounds
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {a H T R : ℕ} {θ : ℝ} (b : D.Binning a H T R θ)
local notation "n" => D.scheme.h - a
local notation "m" => b.target.m
local notation "d" => b.target.d

abbrev Flags := Format.vec m (.pair .bit (.vec d .bit))

abbrev step (r : D.format.obj) := Child.step n 5 (D.childInput a b.ha r)
def status (r : D.format.obj) : b.Flags.obj := fun v =>
  (D.childLive a r v, Child.coreFlags (D.binNav a b.ha 5 r) (b.step r) v)

namespace Trial
variable {b} {x y : Wire} {L : ℝ} {r : D.format.obj} {P : Rounds.Board F x y D.scheme.h}
    {p : D.Presents r P} (t : b.Trial p L) (q : ℕ)

local notation "host" => (Input.HostChart.host (t.atlas q))
local notation "nav" => (Input.HostChart.graph (t.atlas q))

theorem nonempty (h : Nonempty P.V) : Nonempty (t.normal q).V :=
  ⟨(h.some, ⟨0, 0⟩)⟩

theorem live_status (i : B m) : (b.status r i).1 = true ↔ i ∈ Set.range host := by
  change D.childLive a r i = true ↔ i ∈ Set.range (Child.host p.host n)
  simp only [childLive, Bool.and_eq_true, decide_eq_true_eq, p.live]
  constructor
  · rintro ⟨⟨v, hv⟩, ⟨s, hs⟩⟩
    refine ⟨(v, s), (Match.rowIndex D.scheme.m (n + 1)).injective ?_⟩
    rw [Child.host_parts]
    exact Prod.ext hv hs
  · rintro ⟨v, rfl⟩
    rw [Child.host_parts]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

theorem closed (v : (t.normal q).V) (k : B d) : nav (host v) k ∈ Set.range host := by
  obtain ⟨u, _, hu⟩ := ((Presents.Plan.childPresent p b.ha).mem (by decide : 0 < 5) v _).mp ⟨k, rfl⟩
  exact ⟨u, hu⟩

theorem edge_status (v w : (t.normal q).V) (hne : v ≠ w) :
    w ∈ (t.normal q).adj v ↔ ∃ k, nav (host v) k = host w ∧ (b.status r (host v)).2 k = true := by
  have h := (Presents.Plan.childPresent p b.ha).step_mem (by decide : 0 < 5) v (host w)
  constructor
  · intro hw
    obtain ⟨k, hk⟩ := (t.atlas q).adjacent v w hw hne
    refine ⟨k, hk, ?_⟩
    unfold status Child.coreFlags; dsimp only
    apply decide_eq_true
    obtain ⟨j, hj⟩ := (h.mpr ⟨w, hw, rfl⟩).resolve_left ((host).injective.ne hne.symm)
    exact ⟨j, hj.trans hk.symm⟩
  · rintro ⟨k, hk, hf⟩
    unfold status Child.coreFlags at hf; dsimp only at hf
    obtain ⟨j, hj⟩ := of_decide_eq_true hf
    obtain ⟨u, hu, he⟩ := h.mp (.inr ⟨j, hj.trans hk⟩)
    exact (host).injective he ▸ hu

end Trial
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
end
