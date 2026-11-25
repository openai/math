import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Network
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.BoardPush
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Length
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Checks

/-! # Controlled construction of child windows from the elected poll -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h) (b Δ C : ℕ)

abbrev Raw := Window.Tile.raw D.scheme.m D.scheme.d a (D.scheme.h - a) (D.degree a Δ C) (D.WithCount a b)

def poll_raw (P : Gadget F) (x : (D.Poll a b).obj) : (D.Raw a b Δ C).obj :=
  (D.childLive a x.1, D.layout a b P x, D.childNav a ha Δ C x.1, D.counted a ha b x)

private abbrev Copies := Format.pair D.format (.pair (D.Poll a b) (D.Poll a b))
private abbrev Fields := Format.pair (.pair (D.Status a) (D.Graph a Δ C)) (.pair .bit (D.Counted a b))

def rawCost (t : ℕ) :=
  4 * ((D.Poll a b).width + 2 * (D.Copies a b).width) +
    (D.childCost a Δ C + (D.layoutCost a b t + 4 * ((D.Poll a b).width + 2 * (D.Counted a b).width))) +
    4 * ((D.Fields a b Δ C).width + 2 * (D.Raw a b Δ C).width)

/-- Every poll has a deterministic result. Invalid padded selectors have zero weight. -/
theorem raw_net {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u)
    (fit : (D.PollRow a b).width + (Side.Input (D.scheme.h - a + D.scheme.e) b).width ≤ u)
    (allow : D.markTable a b ∈ L) (P : Gadget F) (t : ℕ) (hw : 2 ^ b ≤ t) (hp : 4 * P.b ≤ 2 ^ t) :
    Action F u L (D.Poll a b) (D.Raw a b Δ C) (D.poll_raw a ha b Δ C P) (D.valid a b P)
      (D.rawCost a b Δ C t) := by
  have copy : Circuit F (D.Poll a b) (D.Copies a b) (fun x => (x.1, x, x))
      ((D.Poll a b).width + 2 * (D.Copies a b).width) :=
    Circuit.project (Sum.elim Sum.inl (Sum.elim id id)) (by rintro x (i | (i | i)) <;> rfl)
  let pin : (D.Raw a b Δ C).pins → (D.Fields a b Δ C).pins
    | .inl i => .inl (.inl i)
    | .inr (.inl i) => .inr (.inl i)
    | .inr (.inr (.inl i)) => .inl (.inr i)
    | .inr (.inr (.inr i)) => .inr (.inr i)
  have reorder : Circuit F (D.Fields a b Δ C) (D.Raw a b Δ C) (fun x => (x.1.1, x.2.1, x.1.2, x.2.2))
      ((D.Fields a b Δ C).width + 2 * (D.Raw a b Δ C).width) :=
    Circuit.project pin (by rintro x (i | (i | (i | i))) <;> rfl)
  have H := (Action.of_map (D.child_map a ha Δ C hu)).par
    ((D.layout_net a b hu fit allow P t hw hp).par (Action.of_map (Map.circuit hu (D.counted_circuit a ha b))))
  have K := (H.pre (Map.circuit hu copy)).post (Map.circuit hu reorder)
  simp only [mul_one, one_mul] at K
  exact K

namespace Selection
variable {D a ha b Δ C} {T : Type} [Fintype T] {x y : Wire} {L : Fringe x y T}
  {P : Gadget F} {z k : ℕ} {r : D.format.obj} {G : HostNet F L D.scheme.h (P.b * z)}
  {p : D.Encodes r G} {B' σ : ℝ} {hu : 0 < P.b * z} (s : D.Selection a ha b k B' Δ C p σ hu)
  (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b) (i : s.choices) (v : Site (G.V × Cell a) (D.scheme.h - a))

def canonicalBoard : (s.state hb i v).Board (D.degree a Δ C) (D.WithCount a b) Prod.fst :=
  s.board hb i v (D.childNav a ha Δ C r) (D.childLive a r) (D.childSelf a ha Δ C r)

theorem canonical_live : (s.canonicalBoard hb i v).Live := D.child_live a p

theorem poll_raw_eq :
    D.poll_raw a ha b Δ C P (D.prepared a ha b k B' Δ C (r, (s.selector hb).write i)) =
      (s.canonicalBoard hb i v).raw := by
  rw [poll_raw, s.layout_eq hb i]
  rfl

end Selection
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # Combining selector checks with the child host headers -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h) (b Δ C : ℕ)

abbrev Headed := (D.Raw a b Δ C).pair (D.ChildHeader a Δ C)

def headed (P : Gadget F) (x : (D.Poll a b).obj) : (D.Headed a b Δ C).obj :=
  (D.poll_raw a ha b Δ C P x, D.childHeader a ha Δ C x.1)

def headedCost (t : ℕ) :=
  4 * ((D.Poll a b).width + 2 * ((D.Poll a b).pair D.format).width) +
    (D.rawCost a b Δ C t + 4 * D.headerCost a Δ C)

theorem headed_net {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u)
    (fit : (D.PollRow a b).width + (Side.Input (D.scheme.h - a + D.scheme.e) b).width ≤ u)
    (allow : D.markTable a b ∈ L) (P : Gadget F) (t : ℕ) (hw : 2 ^ b ≤ t) (hp : 4 * P.b ≤ 2 ^ t) :
    Action F u L (D.Poll a b) (D.Headed a b Δ C) (D.headed a ha b Δ C P) (D.valid a b P)
      (D.headedCost a b Δ C t) := by
  have copy : Circuit F (D.Poll a b) ((D.Poll a b).pair D.format) (fun x => (x, x.1))
      ((D.Poll a b).width + 2 * ((D.Poll a b).pair D.format).width) :=
    Circuit.project (Sum.elim id Sum.inl) (by rintro x (i | i) <;> rfl)
  have H := ((D.raw_net a ha b Δ C hu fit allow P t hw hp).par
    (Action.of_map (Map.circuit hu (D.header_net a ha Δ C)))).pre (Map.circuit hu copy)
  simp only [mul_one] at H
  exact H

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # Reading the new charges from the same window as the new table -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing
open scoped Classical

namespace State.Board
variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F}
  {a h z Δ D k b d : ℕ} {B' : ℝ} {u v : State S P a h z Δ D k B'} {A : Format}
  {read : A.obj → (Window.Source S (h - a) b).obj}

def routed (p : u.Board d A read) (f : A.obj → Cell (h - a) → ℝ) :=
  push (Function.uncurry (u.g.route u.m u.col)) (fun t =>
    f ((p.parent (u.p.placeGroup a t.1).1).2 (u.p.placeGroup a t.1).2) t.2) u.v

theorem routed_eq {p : u.Board d A read} {q : v.Board d A read} (he : p.look = q.look)
    (f : A.obj → Cell (h - a) → ℝ) : p.routed f = q.routed f :=
  push_eq he _ _ (fun _ _ hr t => congrArg (fun s => f s t) (source_eq he hr))

end State.Board

namespace Template
variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T}
  (D : Template F) (a b : ℕ)

def beforePark (x : (D.WithCount a b).obj) (t : Cell (D.scheme.h - a)) :=
  D.park (x.2 (cellIndex _ t))

def beforePast (x : (D.WithCount a b).obj) (t : Cell (D.scheme.h - a)) : ℝ :=
  (D.past (x.2 (cellIndex _ t)) + (D.scheme.decode (x.1.1 (cellIndex _ t))).volume true : ℕ)

namespace Selection

variable {D a b} {P : Gadget F} {z k Δ C : ℕ} {ha : a ≤ D.scheme.h}
  {r : D.format.obj} {G : HostNet F L D.scheme.h (P.b * z)} {p : D.Encodes r G}
  {B' σ : ℝ} {hu : 0 < P.b * z} (s : D.Selection a ha b k B' Δ C p σ hu)
  (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b)
  (i : s.choices) (v : Site (G.V × Cell a) (D.scheme.h - a)) (hc : Δ ≤ C)

local notation "E" => splitAddr G.V a ha
local notation "H" => G.regroup a ha
local notation "pr" => G.project a ha Δ C hc
local notation "Q" => HostNet.contracted pr s.group s.matching (Nat.pos_of_mul_pos_left hu) hc i
local notation "bd" => s.canonicalBoard hb i v

private theorem pos (w : G.V × Cell D.scheme.h) :
    D.position a ha (cellIndex _ (E w).1.2) (cellIndex _ (E w).2) = p.post.block w.2 := by
  change D.position a ha (cellIndex _ ((splitCell a ha) w.2).1)
    (cellIndex _ ((splitCell a ha) w.2).2) = _
  simp only [position, Equiv.symm_apply_apply, Prod.mk.eta, p.block]

theorem routed_park :
    (bd).routed (D.beforePark a b) = push (Q).park L.charge ((pr).place v) := by
  refine Eq.trans ?_ (HostNet.park_route pr s.group s.matching _ hc i v)
  apply congrArg (fun f => push (Function.uncurry (s.group.route s.matching
    (s.group.layout s.matching P i))) f v)
  funext w
  obtain ⟨w, rfl⟩ := (E).surjective w
  change D.park (D.counter r (p.post.host w.1)
    (D.position a ha (cellIndex _ (E w).1.2) (cellIndex _ (E w).2))) = push (H).park L.charge (E w)
  rw [pos (p := p), p.park, G.regroup_park]

theorem routed_past :
    (bd).routed (D.beforePast a b) = ((Q).past ((pr).place v) : ℝ) := by
  refine Eq.trans ?_ (HostNet.past_route pr s.group s.matching _ hc i v)
  apply congrArg (fun f => push (Function.uncurry (s.group.route s.matching
    (s.group.layout s.matching P i))) f v)
  funext w
  obtain ⟨w, rfl⟩ := (E).surjective w
  let j := D.position a ha (cellIndex _ (E w).1.2) (cellIndex _ (E w).2)
  change ((D.past (D.counter r (p.post.host w.1) j) +
    (D.scheme.decode ((r.1 (p.post.host w.1)).2 j)).volume true : ℕ) : ℝ) =
      (G.past ((E).symm (E w)) + Packing.degree (H).pair (E w) * (P.b * z) : ℕ)
  rw [show j = p.post.block w.2 from pos (p := p) w, p.past, Equiv.symm_apply_apply, G.regroup_degree]
  exact congrArg (fun k => ((G.past w + k : ℕ) : ℝ)) (p.post.internal_volume w)

end Selection
end Template
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# The first, validating half of a wire-saving controller

The scheme and optional side information are retained so that the
second half can move exterior records along the selected assignment.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] (D : Template F) (P : Gadget F) (a : ℕ) (ha : a ≤ D.scheme.h)
    (b k : ℕ) (cost : ℝ) (Δ C : ℕ) (A : Format)

local notation "n" => (D.scheme.h - a)
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d
local notation "q" => ((d + 1) * n)
local notation "X" => Format.pair (D.format.pair A) (D.Candidate a b)
local notation "Y" => D.scheme.format.pair A
local notation "Z" => Format.pair (D.Headed a b Δ C) Y

def start (x : (X).obj) : (Z).obj :=
  (D.headed a ha b Δ C P (D.prepared a ha b k cost Δ C (x.1.1, x.2)), x.1.1.1, x.1.2)

def check (x : (X).obj) := D.valid a b P (D.prepared a ha b k cost Δ C (x.1.1, x.2))

variable {u N N' v v' : ℕ} {L : Set (Table F)} {I : Type*}

theorem start_net (hu : 3 ≤ u) (hn : 0 < n)
    (hg : Access F u L (m + q) v N) (hv : (Group.Parcel d a n D.count).width ≤ v)
    (hc : Access F u L (m + d) v' N') (hv' : (Window.LabelSet a n).width ≤ v')
    (hb : D.arity a b ≤ u) (hL : (D.keys a b k cost Δ C : Set _) ⊆ L)
    (fit : (D.PollRow a b).width + (Side.Input (n + D.scheme.e) b).width ≤ u)
    (allow : D.markTable a b ∈ L) (t : ℕ) (hw : 2 ^ b ≤ t) (hp : 4 * P.b ≤ 2 ^ t)
    (x : I → (X).obj)
    (recip : ∀ i, Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) (x i).1.1.1) :
    Computes F u L X Z x (D.start P a ha b k cost Δ C A ∘ x) (D.check P a ha b k cost Δ C A ∘ x)
      (100 * (X).width + D.prepareCost a b v N v' N' + D.headedCost a b Δ C t) := by
  let R := D.Request a b
  let load : (X).obj → R.obj := fun x => (x.1.1, x.2)
  let save : (X).obj → (Y).obj := fun x => (x.1.1.1, x.1.2)
  have hload : Circuit F X R load ((X).width + 2 * R.width) :=
    Circuit.project (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (by rintro x (i|i) <;> rfl)
  have hsave : Circuit F X Y save ((X).width + 2 * (Y).width) :=
    Circuit.project (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr))
      (by rintro x (i|i) <;> rfl)
  have h₁ := Computes.of_map (L := L) (x := x) (Map.circuit hu hload) (fun _ => rfl)
  have h₂ := D.prepare_net a ha b k cost Δ C hu hn hg hv hc hv' hb hL (load ∘ x) recip
  have h₃ := D.headed_net a ha b Δ C hu fit allow P t hw hp
  have h₄ := Computes.of_map (L := L) (x := x) (Map.circuit hu hsave) (fun _ => rfl)
  have h := ((h₁.comp h₂).comp (Computes.of_action h₃ (fun _ => rfl) (fun _ => rfl))).pair hu h₄
  simp only [one_mul, mul_one] at h
  refine h.mono ?_
  simp only [R, Request, format, Format.width_pair]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # Widths of the lookup tables in the first half of the contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring
open scoped Classical
variable {F : Type} [Field F] (D : Template F) (a b k : ℕ) (cost : ℝ) (Δ C : ℕ)

theorem keys_width (s : Table F) (hs : s ∈ D.keys a b k cost Δ C) :
    Processor.arity s ≤ D.arity a b := by
  simp only [keys, Finset.mem_insert] at hs
  unfold arity
  rcases hs with rfl | rfl | rfl | h
  · simp only [stubTable, Processor.arity, weightTable, lookup, wd_word, Format.width_addr, tableWidth]
    omega
  · simp only [lightTable, Processor.arity, weightTable, lookup, wd_word]
    rw [Format.width_addr]
    omega
  · simp only [voteTable, Processor.arity, weightTable, lookup, wd_word]
    omega
  · have := Group.arity_keys F h
    omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # A family of elected wire-saving branches with one common decoder -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing History
open scoped Classical

variable {F : Type} [Field F] (D : Template F) (P : Gadget F) (a : ℕ) (ha : a ≤ D.scheme.h)
  (b k : ℕ) (cost : ℝ) (Δ C z : ℕ) (σ : ℝ) (hu : 0 < P.b * z)

structure Branch where
  T : Type
  [finite : Fintype T]
  x : Wire
  y : Wire
  L : Fringe x y T
  G : HostNet F L D.scheme.h (P.b * z)
  r : D.format.obj
  p : D.Encodes r G
  s : D.Selection a ha b k cost Δ C p σ hu
  i : s.choices
  v : Site (G.V × Cell a) (D.scheme.h - a)

attribute [instance] Branch.finite

variable {P z} {hz : 0 < z}

abbrev after (M : Book D.scheme P z hz) (e cap : ℕ) (K : Meter) : Template F where
  scheme := M.scheme (D.size a) (D.degree a Δ C) a e cap
  count := K.count
  load := K.load
  park := K.park
  past := K.past
  order := Post.order (D.degree a Δ C) e M.d cap
  full := D.full

namespace Branch
variable {D a ha b k cost Δ C σ hu} (t : D.Branch P a ha b k cost Δ C z σ hu)
    (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b) (hc : Δ ≤ C)

abbrev state := t.s.state hb t.i t.v
abbrev board := t.s.canonicalBoard hb t.i t.v
abbrev layout := HostNet.contracted (t.G.project a ha Δ C hc) t.s.group t.s.matching
  (Nat.pos_of_mul_pos_left hu) hc t.i

variable {e : ℕ} (M : Book D.scheme P z hz) (room : (t.state hb).Room e) (cap : ℕ)

abbrev assign := (t.board hb).assign M room cap hc
abbrev Ready := (t.state hb).Ready M room cap (t.assign hb hc M room cap) (D.childNav a ha Δ C t.r)
abbrev records := (t.state hb).records M room cap (t.assign hb hc M room cap)
abbrev written := (t.state hb).output M room cap (t.assign hb hc M room cap) (D.childNav a ha Δ C t.r)

/-- Only occupied child addresses carry counters. -/
def counters (K : Meter) : B (D.size a) → B a → B K.count :=
  Function.extend (Child.host t.p.post.host (D.scheme.h - a))
    (fun v j => K.read (t.layout hc) (v, (cellIndex a).symm j)) (fun _ _ => 0)

theorem counters_at (K : Meter) (v : Site t.G.V (D.scheme.h - a)) (j : Cell a) :
    t.counters hc K (Child.host t.p.post.host (D.scheme.h - a) v) (cellIndex a j) =
      K.read (t.layout hc) (v, j) := by
  rw [counters, (Child.host _ _).injective.extend_apply, Equiv.symm_apply_apply]

theorem counters_vacant (K : Meter) (i : B (D.size a)) (j : B a) (hi : D.childLive a t.r i = false) :
    t.counters hc K i j = 0 := by
  rw [counters, Function.extend_apply' _ _ _ (fun h => Bool.noConfusion (hi.symm.trans ((D.child_live a t.p i).mpr h)))]

end Branch
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # The charge counter of a child depends only on its local window -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Branch
open Coloring Packing History State.Board
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {P : Gadget F} {a : ℕ} {ha : a ≤ D.scheme.h}
    {b k : ℕ} {cost : ℝ} {Δ C z : ℕ} {σ : ℝ} {hu : 0 < P.b * z} {hz : 0 < z} {e : ℕ}
    {s t : D.Branch P a ha b k cost Δ C z σ hu}
    {hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b} {hc : Δ ≤ C}
    {M : Book D.scheme P z hz} {rs : (s.state hb).Room e} {rt : (t.state hb).Room e} {cap : ℕ}
    (hs : s.Ready hb hc M rs cap) (ht : t.Ready hb hc M rt cap)
    {v : Site (s.G.V × Cell a) (D.scheme.h - a)} {w : Site (t.G.V × Cell a) (D.scheme.h - a)}

include hs ht in
theorem counters_eq (he : ((s.board hb).recenter v).look = ((t.board hb).recenter w).look) (K : Meter) :
    s.counters hc K (Child.host s.p.post.host (D.scheme.h - a) (v.1.1, v.2)) (cellIndex a v.1.2) =
    t.counters hc K (Child.host t.p.post.host (D.scheme.h - a) (w.1.1, w.2)) (cellIndex a w.1.2) := by
  let X := (s.G.project a ha Δ C hc).place v
  let Y := (t.G.project a ha Δ C hc).place w
  have h := (agrees he).1.localRecord (le_refl 8) M (rs.recenter v) (rt.recenter w)
    cap (s.assign hb hc M rs cap) (t.assign hb hc M rt cap) (index_eq he) hs.ranked ht.ranked
  have hr := ((s.state hb).record_at M rs cap (s.assign hb hc M rs cap) v).trans
    (h.trans ((t.state hb).record_at M rt cap (t.assign hb hc M rt cap) w).symm)
  let Z := M.scheme (D.size a) (D.degree a Δ C) a e cap
  have eq : hs.posting.atBlock X = ht.posting.atBlock Y :=
    congrArg (Z.decode ∘ (Post.record (D.degree a Δ C) e M.d (.addr cap)).serial) hr
  have internal := (hs.posting.internal_volume X).symm.trans
    ((congrArg (fun r => r.volume true) eq).trans (ht.posting.internal_volume Y))
  have external := (hs.posting.exterior_volume X).symm.trans
    ((congrArg (fun r => r.volume false) eq).trans (ht.posting.exterior_volume Y))
  have park := (s.s.routed_park hb s.i v hc).symm.trans
    ((routed_eq he (D.beforePark a b)).trans (t.s.routed_park hb t.i w hc))
  have past := (s.s.routed_past hb s.i v hc).symm.trans
    ((routed_eq he (D.beforePast a b)).trans (t.s.routed_past hb t.i w hc))
  rw [counters_at, counters_at]
  exact congr (congrArg₂ K.encode (congrArg₂ (· + ·) external internal) park) (Nat.cast_injective past)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Branch
end

/-! # The encoded output of a selected subround -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Branch
open Coloring Packing History
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {P : Gadget F} {a : ℕ} {ha : a ≤ D.scheme.h}
    {b k : ℕ} {cost : ℝ} {Δ C z : ℕ} {σ : ℝ} {hu : 0 < P.b * z} {hz : 0 < z} {e : ℕ}
    (t : D.Branch P a ha b k cost Δ C z σ hu)
    (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b) (hc : Δ ≤ C)
    (M : Book D.scheme P z hz) (room : (t.state hb).Room e) (cap : ℕ) (K : Meter)

def output : (D.after a Δ C M e cap K).format.obj :=
  (t.written hb hc M room cap, fun i =>
    let q := D.childHeader a ha Δ C t.r i
    (q.1, q.2, t.counters hc K i))

def encodes (hd : 0 < Δ) (ready : t.Ready hb hc M room cap) (valid : K.Valid (t.layout hc)) :
    (D.after a Δ C M e cap K).Encodes (t.output hb hc M room cap K) (t.layout hc) where
  post := ready.posting
  block _ := rfl
  live := D.child_live a t.p
  frozen := D.child_frozen a t.p
  closed := D.child_closed a ha Δ C t.p hd hc
  reciprocal := D.child_reciprocal a ha Δ C t.p hd hc _ (fun i => (t.written hb hc M room cap i).2)
  edge := D.child_edge a ha Δ C t.p hd hc
  core := D.child_core a ha Δ C t.p hd hc
  load v j := (congrArg K.load (t.counters_at hc K v j)).trans (valid (v, j)).1
  park v j := (congrArg K.park (t.counters_at hc K v j)).trans (valid (v, j)).2.1
  past v j := (congrArg K.past (t.counters_at hc K v j)).trans (valid (v, j)).2.2

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Branch
end

/-! # Separating short child labels from the common graph and headers -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing History Window
open scoped Classical

variable {F : Type} [Field F] (D : Template F) (a b Δ C : ℕ)
  {P : Gadget F} {z : ℕ} {hz : 0 < z} (M : Book D.scheme P z hz) (e cap : ℕ) (K : Meter) (W : Format)

local notation "Z" => D.after a Δ C M e cap K
local notation "Out" => Tile.output D.scheme.m a (D.scheme.h - a)

abbrev Envelope := (D.Graph a Δ C).pair (D.ChildHeader a Δ C)
abbrev Label := Format.pair (.addr (Z).scheme.ℓ) (.pair (.addr K.count) W)
abbrev Labels := Out (D.Label a Δ C M e cap K W)
abbrev Issued := (Z).format.pair (Out W)

def envelope (x : (D.Headed a b Δ C).obj) : (D.Envelope a Δ C).obj := (x.1.2.2.1, x.2)

def joinLabels (x : ((D.Envelope a Δ C).pair (D.Labels a Δ C M e cap K W)).obj) :
    (D.Issued a Δ C M e cap K W).obj :=
  ((fun i => (x.1.1 i, fun j => (x.2 i j).1),
    fun i => ((x.1.2 i).1, (x.1.2 i).2, fun j => (x.2 i j).2.1)), fun i j => (x.2 i j).2.2)

local notation "A₀" => D.Headed a b Δ C
local notation "A₁" => D.Envelope a Δ C
local notation "A₂" => D.Raw a b Δ C
local notation "A₃" => D.Labels a Δ C M e cap K W
local notation "A₄" => D.Issued a Δ C M e cap K W

private theorem join_net : Circuit F ((A₁).pair A₃) A₄ (D.joinLabels a Δ C M e cap K W)
    (((A₁).pair A₃).width + 2 * (A₄).width) := by
  let pin : (A₄).pins → ((A₁).pair A₃).pins
    | .inl (.inl (i, .inl q)) => .inl (.inl (i, q))
    | .inl (.inl (i, .inr (j, q))) => .inr (i, j, .inl q)
    | .inl (.inr (i, .inl q)) => .inl (.inr (i, .inl q))
    | .inl (.inr (i, .inr (.inl q))) => .inl (.inr (i, .inr q))
    | .inl (.inr (i, .inr (.inr (j, q)))) => .inr (i, j, .inr (.inl q))
    | .inr (i, j, q) => .inr (i, j, .inr (.inr q))
  refine Circuit.project pin ?_
  rintro x ((⟨i, q | ⟨j, q⟩⟩ | ⟨i, q | (q | ⟨j, q⟩)⟩) | ⟨i, j, q⟩) <;> rfl

def joinCost (N : ℕ) :=
  20 * (A₀).width + (4 * ((A₀).width + 2 * (A₁).width) + (4 * ((A₀).width + 2 * (A₂).width) + N)) +
    4 * (((A₁).pair A₃).width + 2 * (A₄).width)

theorem join_computes {u N : ℕ} {L : Set (Table F)} (hu : 3 ≤ u)
    {I : Type*} (x : I → (A₀).obj) (y : I → (A₃).obj)
    (net : Computes F u L A₂ A₃ (fun i => (x i).1) y (fun _ => 1) N) :
    Computes F u L A₀ A₄ x (fun i => D.joinLabels a Δ C M e cap K W (D.envelope a b Δ C (x i), y i))
      (fun _ => 1) (D.joinCost a b Δ C M e cap K W N) := by
  have keep : Circuit F A₀ A₁ (D.envelope a b Δ C) ((A₀).width + 2 * (A₁).width) :=
    Circuit.project (Sum.elim (fun q => .inl (.inr (.inr (.inl q)))) Sum.inr) (by rintro x (i|i) <;> rfl)
  have pr : Circuit F A₀ A₂ Prod.fst ((A₀).width + 2 * (A₂).width) :=
    Circuit.project Sum.inl (fun _ _ => rfl)
  have h := Computes.of_map (L := L) (x := x) (Map.circuit hu keep) (fun _ => rfl)
  have k := Computes.of_map (L := L) (x := x) (Map.circuit hu pr) (fun _ => rfl)
  have all := (h.pair hu (k.comp net)).comp
    (Computes.of_map (Map.circuit hu (D.join_net a Δ C M e cap K W)) (fun _ => rfl))
  simp only [mul_one] at all
  exact all

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # Fitting the contraction history and propagating the tag estimate -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Branch
open Coloring Packing History
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {P : Gadget F} {a : ℕ} {ha : a ≤ D.scheme.h}
    {b k : ℕ} {cost : ℝ} {Δ C z : ℕ} {σ : ℝ} {hu : 0 < P.b * z} {hz : 0 < z} {e : ℕ}
    (t : D.Branch P a ha b k cost Δ C z σ hu)
    (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b) (hc : Δ ≤ C)
    (hd : 0 < Δ) (hs : 0 ≤ σ) (hp : 0 ≤ cost) (bounds : t.G.Bounded Δ C cost)

local notation "H" => t.layout hc
local notation "A" => t.state hb

include hd hs hp bounds in
theorem estimates :
    (H).Bounded ((4 * Δ) ^ 900) ((4 * C) ^ 900) (9 * ((4 * Δ) ^ 300 : ℕ) * ((2 : ℝ) ^ k * cost)) ∧
    ((H).X : ℝ) ≤ (1 - 1 / (8 * (P.b : ℝ))) * t.G.X + (t.L.Z + σ) ∧
    t.G.Preserves H ∧ (H).mass = t.G.mass + 2 * t.G.X ∧ t.G.Tracks H ((Δ + 1) * 2) :=
  (t.G.projected_bounds P (Nat.pos_of_mul_pos_left hu) a k Δ C hd hc ha cost σ hp hs bounds
    t.s.group t.s.matching t.s.saving t.i).2

include hp hd bounds in
theorem room (he : (10 : ℝ) * (4 * Δ) ^ 300 * 2 ^ k * cost ≤ 2 ^ e * z)
    (floor : ∀ j, P.b * z ≤ t.p.post.toPresentation.borderWidth j) : (A).Room e where
  budget := ⟨Nat.pos_of_mul_pos_left hu, hp, hd, (t.G.regroup_bounded a ha bounds).1, he⟩
  contacts := Scheme.Presentation.contacts («H» := t.G.regroup a ha) t.p.post.toPresentation floor
  floor j := (Nat.le_mul_of_pos_left _ P.pos).trans (floor j)

variable (M : Book D.scheme P z hz) (rm : (t.state hb).Room e) {unit c B cap : ℕ}

include hd in
theorem fitted (neutral : ∀ v, t.G.diagram.arity v = 0 → ∀ x, Transcript.sample (t.G.diagram.table v) x = 1)
    (sizes : ∀ j, M.len (M.put (t.p.post.toPresentation.borderWidth j)) = t.p.post.toPresentation.borderWidth j)
    (tag : (A).Charged M.ord unit c) (hv : 0 < unit)
    (mass : (H).mass ≤ t.L.cap) (bound : ∀ v i, (H).load v i ≤ (B : ℝ) * unit)
    (budget : M.overhead e + c * (2 ^ t.L.discount * B) ≤ cap) :
    t.Ready hb hc M rm cap := by
  constructor
  · exact fun _ => rfl
  · exact sizes
  · exact D.child_hop a ha Δ C t.p hd hc
  · exact neutral
  · intro v
    exact (Nat.add_le_add_left (((A).recenter v).inherited_bound hc tag hv B mass bound) _).trans budget

theorem charged_after (ready : t.Ready hb hc M rm cap) (K : Meter)
    (tag : (A).Charged M.ord unit c) (hv : 0 < unit) (hle : unit ≤ z)
    (w : (H).V × Cell a) (active : 0 < (H).tetherLoad w + Packing.degree (H).pair w * z) :
    (D.after a Δ C M e cap K).tagLength (t.output hb hc M rm cap K)
      (ready.posting.host w.1) (ready.posting.block w.2) * unit ≤
      (c + (Post.headerFmt (D.degree a Δ C) e M.d).width + M.overhead e) * (H).footprint w := by
  have floor := (H).active_floor (ready.posting.toPresentation.contacts (State.Ready.floor ready (State.Room.floor rm))) w active
  let v := (t.G.project a ha Δ C hc).place.symm w
  let W := (Post.headerFmt (D.degree a Δ C) e M.d).width + M.overhead e
  have ho := ready.stored v
  have hi := ((A).recenter v).inherited_charge hc tag hv
  have hf : W * unit ≤ W * (H).footprint w := Nat.mul_le_mul_left W (hle.trans floor)
  change ((A).recenter v).inherited M.ord * unit ≤ c * (H).footprint w at hi
  calc
    _ ≤ (W + ((A).recenter v).inherited M.ord) * unit := Nat.mul_le_mul_right _ ho
    _ ≤ W * (H).footprint w + c * (H).footprint w := by rw [Nat.add_mul]; exact Nat.add_le_add hf hi
    _ = _ := by rw [← Nat.add_mul, Nat.add_comm W, Nat.add_assoc]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Branch
end

/-!
# Producing contracted descriptions for a family of branches

One shared local table emits the new atom, counter, and any extra
fields determined by the same window. The host names bypass the table.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing History Window State.Board
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {P : Gadget F} {a : ℕ} {ha : a ≤ D.scheme.h}
    {b k : ℕ} {cost : ℝ} {Δ C z : ℕ} {σ : ℝ} {hu : 0 < P.b * z} {hz : 0 < z}
    (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b)

def Branch.head (t : D.Branch P a ha b k cost Δ C z σ hu) : (D.Headed a b Δ C).obj :=
  ((t.board hb).raw, D.childHeader a ha Δ C t.r)

theorem Branch.headed_eq (t : D.Branch P a ha b k cost Δ C z σ hu) :
    D.headed a ha b Δ C P (D.prepared a ha b k cost Δ C (t.r, (t.s.selector hb).write t.i)) =
      t.head hb := Prod.ext (t.s.poll_raw_eq hb t.i t.v) rfl

variable (D a b Δ C) (M : Book D.scheme P z hz) (e cap : ℕ) (K : Meter) (W : Format)

local notation "Y" => D.Label a Δ C M e cap K W
local notation "A" => D.WithCount a b
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d
local notation "n" => (D.scheme.h - a)
local notation "q" => D.degree a Δ C

def issueWidth := (Tile.word d a n q A).width + (Y).width

def issueCost (v N l : ℕ) := D.joinCost a b Δ C M e cap K W
  (Tile.bankCost m d a n q A v N l + Tile.cost m d a n q A Y)

variable {a b Δ C e} (hc : Δ ≤ C) {I : Type*}
    (t : I → D.Branch P a ha b k cost Δ C z σ hu)
    (room : ∀ i, ((t i).state hb).Room e)
    (ready : ∀ i, (t i).Ready hb hc M (room i) cap)
    (extra : I → (Tile.output D.scheme.m a (D.scheme.h - a) W).obj)

include ready in
theorem issue_net (blank : W.obj)
    (agree : ∀ i j x y, (((t i).board hb).recenter x).look = (((t j).board hb).recenter y).look →
      extra i (childAt x) (cellIndex a x.1.2) = extra j (childAt y) (cellIndex a y.1.2))
    (vacant : ∀ i x y, D.childLive a (t i).r x = false → extra i x y = blank) :
    ∃ table : Table F, wd table.1 + wd table.2.1 = D.issueWidth a b Δ C M e cap K W ∧
      ∀ {u v N l : ℕ} {L : Set (Table F)},
      3 ≤ u → table ∈ L → D.issueWidth a b Δ C M e cap K W ≤ u →
      Access F u L (m + d) v N → 2 ^ a * (Walks 8 d A).width ≤ v →
      D.size a ≤ l → 2 ^ (Tile.radius d + (n + 1)) ≤ l → 2 ^ q ≤ l →
      Computes F u L (D.Headed a b Δ C) (D.Issued a Δ C M e cap K W)
        (fun i => (t i).head hb) (fun i => ((t i).output hb hc M (room i) cap K, extra i))
        (fun _ => 1) (D.issueCost a b Δ C M e cap K W v N l) := by
  let X := Post.record q e M.d (.addr cap)
  let post (i : I) (x : B (D.size a)) (y : B a) (v : X.obj) : (Y).obj :=
    (X.serial v, (t i).counters hc K x y, extra i x y)
  let idle : (Y).obj := (X.serial Post.vacant, 0, blank)
  obtain ⟨gate, size, h⟩ := print_net M cap hc (fun i => (t i).state hb) (fun i => (t i).board hb)
    room Y idle post (fun i => (t i).s.canonical_live hb (t i).i (t i).v)
    (fun i j x y he v => Prod.ext rfl (Prod.ext (Branch.counters_eq (ready i) (ready j) he K)
      (agree i j x y he)))
    (fun i x y hv => Prod.ext rfl (Prod.ext ((t i).counters_vacant hc K x y hv) (vacant i x y hv)))
    (fun i => (t i).p.reciprocal)
  refine ⟨gate, size, ?_⟩
  intro u v N l L h3 hg fit acc bound hm hr hq
  have net := h h3 hg fit acc bound hm hr hq
  exact D.join_computes a b Δ C M e cap K W h3 (fun i => (t i).head hb) _ net

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-!
# A fixed number of contractions

When the number of steps and the ratio of the load to a unit are
bounded in advance, the local atom count gives a direct estimate
without any global reserve for the retired ports.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing History
open scoped Classical

namespace State
variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k : ℕ} {B' : ℝ}
  {u : State S P a h z Δ D k B'} {e : ℕ}

theorem Room.inherited (rm : u.Room e) (ord : B S.ℓ ≃ B S.ℓ) :
    u.inherited ord ≤ 2 ^ e * S.ℓ := by
  let J := History.Subround.Receipt P u.H u.g u.m u.i u.v
  have hi (i : J) : Kind.carried S P (S.e + 2) ord (u.kind i.val) ≤ S.ℓ := by
    rcases u.kind i.val with ⟨x, j⟩ | t
    · exact Dense.used_le.mpr (ord x).isLt
    · simp
  have hcard : Fintype.card J ≤ 2 ^ e := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective rm.atoms rm.atoms.injective
  calc
    _ ≤ ∑ _ : J, S.ℓ := Finset.sum_le_sum fun i _ => hi i
    _ = Fintype.card J * S.ℓ := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hcard

end State

namespace Template.Branch
variable {F : Type} [Field F] {D : Template F} {P : Gadget F} {a : ℕ} {ha : a ≤ D.scheme.h}
    {b k : ℕ} {cost : ℝ} {Δ C z : ℕ} {σ : ℝ} {hu : 0 < P.b * z} {hz : 0 < z} {e : ℕ}
    (t : D.Branch P a ha b k cost Δ C z σ hu)
    (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b) (hc : Δ ≤ C) (hd : 0 < Δ)
    (M : Book D.scheme P z hz) (rm : (t.state hb).Room e)

include hd in
theorem direct
    (neutral : ∀ v, t.G.diagram.arity v = 0 → ∀ x, Transcript.sample (t.G.diagram.table v) x = 1)
    (sizes : ∀ j, M.len (M.put (t.p.post.toPresentation.borderWidth j)) = t.p.post.toPresentation.borderWidth j) :
    t.Ready hb hc M rm (M.overhead e + 2 ^ e * D.scheme.ℓ) := by
  constructor
  · exact fun _ => rfl
  · exact sizes
  · exact D.child_hop a ha Δ C t.p hd hc
  · exact neutral
  · exact fun v => Nat.add_le_add_left ((rm.recenter v).inherited M.ord) _

end Template.Branch
end OAI.LinearAlgebra.MatrixExponent.Assembly
end
