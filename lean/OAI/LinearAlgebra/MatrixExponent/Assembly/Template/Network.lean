import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Assembly.Hold
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.BoardPush
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Guard

/-! # Recovering both projected graph masks on the child address list -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing
open scoped Classical

variable {F T : Type} (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h) (Δ C : ℕ)

abbrev ChildHeader := Format.vec (D.size a) (.pair (.pair .bit .bit) (Group.Flags (D.degree a Δ C)))

def childHeader (r : D.format.obj) : (D.ChildHeader a Δ C).obj :=
  fun i => ((D.childLive a r i, D.childFrozen a r i),
    fun j => (true, Child.coreFlags (D.childNav a ha Δ C r) (D.childCore a ha Δ r) i j))

variable [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u : ℕ} {r : D.format.obj}
  {G : HostNet F L D.scheme.h u} (p : D.Encodes r G) (hd : 0 < Δ) (hc : Δ ≤ C)

local notation "H" => Child.host p.post.host (D.scheme.h - a)
local notation "nav" => D.childNav a ha Δ C r
local notation "meta" => D.childHeader a ha Δ C r
local notation "Q" => G.project a ha Δ C hc

theorem child_frozen (v : Site G.V (D.scheme.h - a)) :
    D.childFrozen a r (H v) = true ↔ G.frozen v.1 := by
  rw [childFrozen, Child.host_parts]
  exact p.frozen v.1

include hd hc in
theorem child_closed (v : Site G.V (D.scheme.h - a)) (j : B (D.degree a Δ C)) :
    nav (H v) j ∈ Set.range H := by
  obtain ⟨w, _, hw⟩ := ((D.child_presents a ha p).mem (D.bound_pos Δ C hd hc) v _).mp ⟨j, rfl⟩
  exact ⟨w, hw⟩

include hd in
theorem child_edge (v w : Site G.V (D.scheme.h - a)) :
    w ∈ (if D.full then (Q).N else (Q).C) v ↔
      ∃ j, nav (H v) j = H w ∧ ((meta (H v)).2 j).1 = true := by
  have he : (∃ j, nav (H v) j = H w) ↔ w ∈ cube (near (D.adj G) (D.bound Δ C)) v := by
    refine ((D.child_presents a ha p).mem (D.bound_pos Δ C hd hc) v _).trans ?_
    simp
  simp only [childHeader, and_true]
  rw [he]
  by_cases ht : D.full = true
  · rw [adj, bound, ite_eq_left ht, ite_eq_left ht, ite_eq_left ht]
    rfl
  · rw [adj, bound, ite_eq_right ht, ite_eq_right ht, ite_eq_right ht]
    rfl

include hd in
theorem child_core (v w : Site G.V (D.scheme.h - a)) :
    w ∈ (Q).C v ↔ ∃ j, nav (H v) j = H w ∧ ((meta (H v)).2 j).2 = true := by
  have he : (∃ j, D.childCore a ha Δ r (H v) j = H w) ↔ w ∈ (Q).C v := by
    refine ((D.core_presents a ha p).mem hd v _).trans ?_
    change (∃ u ∈ cube (near G.C Δ) v, H u = H w) ↔ w ∈ cube (near G.C Δ) v
    simp
  simp only [childHeader, Child.coreFlags, decide_eq_true_eq]
  constructor
  · intro hw
    have hh := D.child_hop a ha Δ C p hd hc v w hw
    exact ⟨_, hh, by rw [hh]; exact he.mpr hw⟩
  · rintro ⟨j, hj, k, hk⟩
    exact he.mp ⟨k, hk.trans hj⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-!
# Computing the common affine color on grouped records

The first pass only reads the interval tags and outgoing stubs. Each
group at a live host votes for all the colors at once. Unused hosts
always give a zero ballot.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing
open scoped Classical

variable {F T : Type} [Field F] (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h) (b : ℕ)

abbrev Candidate := Branches.format D.scheme.m a ((D.scheme.h - a) + D.scheme.e) b

abbrev Source := Window.Source D.scheme (D.scheme.h - a) b
abbrev Batch := Fmt.groups D.scheme.m D.scheme.d a (D.Source a b)

def light (i : B ((D.scheme.h - a) + 1)) (j : B (D.scheme.h - a)) := decide (thick (colorIndex (D.scheme.h - a) i) ((cellIndex (D.scheme.h - a)).symm j))

def recolor (x : (D.Source a b).obj) (c : B ((D.scheme.h - a) + 1)) : (D.Source a b).obj :=
  (x.1, x.2.1, D.light a c, x.2.2.2)

def score (x : (D.Source a b).obj) (c : B ((D.scheme.h - a) + 1)) : B ((D.scheme.h - a) + D.scheme.e + 1) :=
  let row := Match.rows (D.recolor a b x c).2.2
  ⟨(Finset.univ.filter fun i => row.control.1 i).card, by
    refine (Finset.card_filter_le _ _).trans_lt ?_
    rw [Finset.card_univ, Fintype.card_fin, pow_succ]
    have : 0 < (2 : ℕ) ^ ((D.scheme.h - a) + D.scheme.e) := by positivity
    omega⟩

abbrev Vote := Format.vec ((D.scheme.h - a) + 1) (.addr ((D.scheme.h - a) + D.scheme.e + 1))
def vote (x : Bool × (D.Source a b).obj) : (D.Vote a).obj :=
  if x.1 then D.score a b x.2 else fun _ => 0

def sample (r : D.format.obj) (X : (D.Batch a b).obj) (i : B (D.scheme.m + a)) :=
  let y := Match.rowIndex D.scheme.m a i
  (D.live r y.1, (X y.1).2 y.2)

def winner (r : D.format.obj) (X : (D.Batch a b).obj) : B ((D.scheme.h - a) + 1) :=
  elect ⊤ (fun c i => D.vote a b (D.sample a b r X i) c)

def scout (r : D.format.obj) (labels : (Window.Tags D.scheme a (D.scheme.h - a)).obj)
    (x : (D.Candidate a b).obj) : (D.Batch a b).obj :=
  Window.gather D.scheme a (D.scheme.h - a) b (D.position a ha) (r.1, labels, fun _ => false, x)

variable [Fintype T] {x y : Wire} {L : Fringe x y T} {u : ℕ} {r : D.format.obj}
  {G : HostNet F L D.scheme.h u} (p : D.Encodes r G)
  {Δ C k : ℕ} {cost : ℝ}
  (g : Grouping (inGroup a G.N) (inGroup a G.C) Δ C k cost (G.regroup a ha).load)

theorem nav_eq (v : G.V) (t : B D.scheme.d) :
    p.post.host (p.post.nav v t) = D.nav r (p.post.host v) t := by
  have h : ∃ w, p.post.host w = (r.1 (p.post.host v)).1 t := p.closed v t
  rw [Scheme.Posting.nav, dite_eq_left h]
  exact h.choose_spec

variable (labels : (Window.Tags D.scheme a (D.scheme.h - a)).obj) (z : (D.Candidate a b).obj)
  (hl : ∀ v i j, labels (p.post.host v) (cellIndex a i) (cellIndex (D.scheme.h - a) j) = intervalCode (D.scheme.h - a) (g.here (v, i) j).2)

include hl in
theorem records (c : B ((D.scheme.h - a) + 1)) (v : G.V) (i : Cell a) :
    (D.recolor a b ((D.scout a ha b r labels z (p.post.host v)).2 (cellIndex a i)) c).2.2 =
      p.post.records a ha g (colorIndex (D.scheme.h - a) c) (v, i) := by
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext j
    obtain ⟨j, rfl⟩ := (cellIndex (D.scheme.h - a)).surjective j
    let w := (splitCell a ha).symm (i, j)
    simp only [recolor, scout, Window.gather, Scheme.Posting.records, position, Equiv.symm_apply_apply]
    exact Prod.ext (hl v i j) (by rw [Scheme.Posting.localStub, p.block])
  · funext j t
    obtain ⟨j, rfl⟩ := (cellIndex (D.scheme.h - a)).surjective j
    simp only [recolor, scout, Window.gather, Scheme.Posting.records, Equiv.symm_apply_apply]
    change labels (D.nav r (p.post.host v) t) _ _ = _
    rw [← D.nav_eq p]
    exact hl _ _ _

include hl in
theorem winner_eq : colorIndex (D.scheme.h - a) (D.winner a b r (D.scout a ha b r labels z)) =
    p.post.color a ha g (Group.embed p.post.host a) := by
  let X := D.scout a ha b r labels z
  let f := Group.embed p.post.host a
  have he : (fun c i => D.vote a b (D.sample a b r X i) c) = ballots f (p.post.colorScore a ha g) := by
    funext c i
    by_cases h : i ∈ Set.range f
    · obtain ⟨⟨v, j⟩, rfl⟩ := h
      simp only [ballots, f.injective.extend_apply, sample, f, Group.row_embed, vote,
        (p.live _).mpr ⟨v, rfl⟩, ↓reduceIte]
      apply Fin.ext
      simp only [score, Scheme.Posting.colorScore]
      erw [D.records a ha b p g labels z hl c v j]
    · have hz : D.live r (Match.rowIndex D.scheme.m a i).1 ≠ true := by
        intro h'
        obtain ⟨v, hv⟩ := (p.live _).mp h'
        let j := (cellIndex a).symm (Match.rowIndex D.scheme.m a i).2
        refine h ⟨(v, j), (Match.rowIndex _ _).injective ?_⟩
        simp only [f, Group.row_embed, hv, j, Equiv.apply_symm_apply]
      simp only [ballots, Function.extend_apply' _ _ _ h, sample, vote]
      erw [ite_eq_right hz]
  exact congrArg (fun x => colorIndex (D.scheme.h - a) (elect ⊤ x)) he

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # Recovering both projected graph masks on the child address list -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h) (Δ C : ℕ)

local notation "m" => D.size a
local notation "d" => D.degree a Δ C
local notation "q" => Child.nextWidth (D.scheme.h - a) Δ D.scheme.d

private abbrev Lists := Format.pair (.pair (D.Status a) (D.Status a)) (.vec m (.vec d .bit))

private def collate (x : (D.Lists a Δ C).obj) : (D.ChildHeader a Δ C).obj :=
  fun i => ((x.1.1 i, x.1.2 i), fun j => (true, x.2 i j))

private theorem collate_net : Circuit F (D.Lists a Δ C) (D.ChildHeader a Δ C)
    (D.collate a Δ C) ((D.Lists a Δ C).width + 34 * (D.ChildHeader a Δ C).width) := by
  have h : Install.Depends ((D.ChildHeader a Δ C).code ∘ D.collate a Δ C ∘ (D.Lists a Δ C).code.symm) 1 := by
    rintro ⟨i, (⟨⟩ | ⟨⟩) | ⟨j, ⟨⟩ | ⟨⟩⟩⟩
    · exact ⟨{.inl (.inl (i, ()))}, by simp, fun x y h => h _ (Finset.mem_singleton_self _)⟩
    · exact ⟨{.inl (.inr (i, ()))}, by simp, fun x y h => h _ (Finset.mem_singleton_self _)⟩
    · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
    · exact ⟨{.inr (i, j, ())}, by simp, fun x y h => h _ (Finset.mem_singleton_self _)⟩
  exact h.bnet F

def headerCost :=
  5 * D.format.width + (5 * D.format.width + D.statusCost a + (D.format.width + 2 * (D.Status a).width)) +
    (5 * D.format.width + D.navCost a d + D.navCost a q + 2 ^ m * (100 + (m + 2 ^ d + 2 ^ q)) ^ 16) +
    ((D.Lists a Δ C).width + 34 * (D.ChildHeader a Δ C).width)

theorem header_net : Circuit F D.format (D.ChildHeader a Δ C)
    (D.childHeader a ha Δ C) (D.headerCost a Δ C) := by
  have hf : Circuit F D.format (D.Status a) (D.childFrozen a) (D.format.width + 2 * (D.Status a).width) :=
    Circuit.project (fun i => .inr ((Match.rowIndex _ _ i.1).1, .inl (.inr i.2))) (fun _ _ => rfl)

  obtain ⟨k, hk, h⟩ := Child.cheap_coreFlags F (t := m + 2 ^ d + 2 ^ q)
    ((Nat.le_add_right m (2 ^ d)).trans (Nat.le_add_right _ _))
    ((Nat.le_add_left (2 ^ d) m).trans (Nat.le_add_right _ _)) (Nat.le_add_left (2 ^ q) _)
  have flags := hk.mono (show k ≤ 2 ^ m * (100 + (m + 2 ^ d + 2 ^ q)) ^ 16 from le_trans (Nat.le_add_left _ _) h)
  have nav : Circuit F D.format (Neighborhood.Rows m d) (D.childNav a ha Δ C) (D.navCost a d) :=
    D.nav_net a ha false (D.bound Δ C)
  have core : Circuit F D.format (Neighborhood.Rows m q) (D.childCore a ha Δ) (D.navCost a q) :=
    D.nav_net a ha true Δ
  have lists := nav.pair core
  have all := (((D.status_net a).pair hf).pair (lists.comp flags)).comp (D.collate_net a Δ C)
  unfold headerCost
  exact all

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-!
# Cost of the common color decision

Only a local group is inspected by a lookup. The large array
of ballots is then reduced by a trivalent integer summation tree.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring
open scoped Classical

variable {F : Type} [Field F] (D : Template F) (a b : ℕ)
  {u : ℕ} {L : Set (Table F)}
local notation "j" => (D.scheme.m + a)
local notation "n" => (D.scheme.h - a)
local notation "c" => (n + 1)
local notation "w" => (n + D.scheme.e + 1)

abbrev Poll := D.format.pair (D.Batch a b)
abbrev PollRow := Format.pair .bit (D.Source a b)
abbrev Polls := Format.vec j (D.PollRow a b)
abbrev Votes := Format.vec j (D.Vote a)

def voteTable := weightTable (A := D.PollRow a b) (D := D.Vote a) (D.vote a b) (fun _ => (1 : F))

def pollCost := 4 * ((D.Poll a b).width + 2 * (D.Polls a b).width) +
  2 ^ j * (1 + (D.PollRow a b).width + (D.Vote a).width) +
  4 * (3 * (D.Votes a).width + 2 ^ c * (2 ^ j * (100 + w) ^ 5 + (100 + (c + (w + j))) ^ 42))

theorem sampling :
    Circuit F (D.Poll a b) (D.Polls a b) (fun x => D.sample a b x.1 x.2)
      ((D.Poll a b).width + 2 * (D.Polls a b).width) := by
  let pins : (D.Polls a b).pins → (D.Poll a b).pins
    | (i, .inl t) => .inl (.inr ((Match.rowIndex D.scheme.m a i).1, .inl (.inl t)))
    | (i, .inr t) => .inr ((Match.rowIndex D.scheme.m a i).1, .inr ((Match.rowIndex D.scheme.m a i).2, t))
  exact Circuit.project pins (by rintro _ ⟨i, t|t⟩ <;> rfl)

private theorem tally :
    Circuit F (D.Votes a) (.addr c) (fun x => elect ⊤ fun y t => x t y)
      (3 * (D.Votes a).width + 2 ^ c * (2 ^ j * (100 + w) ^ 5 + (100 + (c + (w + j))) ^ 42)) := by
  let X := Format.vec c (.vec j (.addr w))
  have flip : Circuit F (D.Votes a) X (fun x i t => x t i) ((D.Votes a).width + 2 * X.width) :=
    Circuit.project (fun t => (t.2.1, t.1, t.2.2)) fun _ _ => rfl
  have eq : X.width = (D.Votes a).width := by
    simp only [X, Votes, Vote, Format.width_vec, mul_left_comm]
  rw [eq, show (D.Votes a).width + 2 * (D.Votes a).width = 3 * (D.Votes a).width by omega] at flip
  have hk := flip.comp (election F j c w ⊤)
  simp only [Function.comp_def] at hk
  exact hk

theorem map_winner (hu : 3 ≤ u) (hw : (D.PollRow a b).width + (D.Vote a).width ≤ u)
    (hl : D.voteTable a b ∈ L) :
    Map F u L (D.Poll a b) (.addr c) (fun x => D.winner a b x.1 x.2) (D.pollCost a b) := by
  have lk : Map F u L (D.PollRow a b) (D.Vote a) (D.vote a b)
      (1 + (D.PollRow a b).width + (D.Vote a).width) := Kernel.lookup hw hl
  have v := Map.vec _ (fun _ : B j => lk)
  exact ((Map.circuit hu (D.sampling a b)).comp v).comp (Map.circuit hu (D.tally a))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # Retaining the parent counters in each grouped window -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring

variable {F : Type} [Field F] (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h) (b : ℕ)

abbrev WithCount := Format.pair (D.Source a b) (.vec (D.scheme.h - a) (.addr D.count))

abbrev Counted := Fmt.groups D.scheme.m D.scheme.d a (D.WithCount a b)

def counted (x : (D.Poll a b).obj) : (D.Counted a b).obj :=
  fun i => ((x.2 i).1, fun j => ((x.2 i).2 j, fun k => D.counter x.1 i (D.position a ha j k)))

theorem counted_circuit : Circuit F (D.Poll a b) (D.Counted a b) (D.counted a ha b)
    ((D.Poll a b).width + 2 * (D.Counted a b).width) := by
  let pins : (D.Counted a b).pins → (D.Poll a b).pins
    | (i, .inl q) => .inr (i, .inl q)
    | (i, .inr (j, .inl q)) => .inr (i, .inr (j, q))
    | (i, .inr (j, .inr (k, q))) => .inl (.inr (i, .inr (.inr (D.position a ha j k, q))))
  exact Circuit.project pins (by rintro x ⟨i, q | ⟨j, q | ⟨k, q⟩⟩⟩ <;> rfl)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-!
# Preparing the color ballot

Group labels are already determined when the selector seats are
inspected. The first collection uses a dummy color column.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring
open scoped Classical

variable {F : Type} [Field F] (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h) (b : ℕ)
local notation "S" => D.scheme
local notation "n" => (D.scheme.h - a)
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d
local notation "q" => ((d + 1) * n)
abbrev Request := D.format.pair (D.Candidate a b)
abbrev Elected := Format.vec (m + a) (Group.Labels n)

def columns (y : (D.Elected a).obj) : (Window.Tags S a n).obj :=
  fun v i => y ((Match.rowIndex m a).symm (v, i))

def setup (x : (D.Request a b).obj × (D.Elected a).obj) : (Window.Fields S a n b).obj :=
  (x.1.1.1, D.columns a x.2, fun _ => false, x.1.2)

private theorem setup_net :
    Circuit F ((D.Request a b).pair (D.Elected a)) (Window.Fields S a n b) (D.setup a b)
      (((D.Request a b).pair (D.Elected a)).width + 34 * (Window.Fields S a n b).width) := by
  let A := (D.Request a b).pair (D.Elected a)
  let B := Window.Fields S a n b
  have h : Install.Depends (B.code ∘ D.setup a b ∘ A.code.symm) 1 := by
    have pin (v : B.pins) (t : A.pins) (ht : ∀ x, B.code (D.setup a b x) v = A.code x t) :
        ∃ s : Finset A.pins, s.card ≤ 1 ∧ ∀ x y, (∀ i ∈ s, x i = y i) →
          (B.code ∘ D.setup a b ∘ A.code.symm) x v = (B.code ∘ D.setup a b ∘ A.code.symm) y v := by
      refine ⟨{t}, by simp, fun x y he => ?_⟩
      simp only [Function.comp_apply, ht, Equiv.apply_symm_apply]
      exact he t (by simp)
    rintro (i | (⟨v, i, j⟩ | (j | k)))
    · exact pin _ (.inl (.inl (.inl i))) fun _ => rfl
    · exact pin _ (.inr ((Match.rowIndex m a).symm (v, i), j)) fun _ => rfl
    · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
    · exact pin _ (.inl (.inr k)) fun _ => rfl
  exact h.bnet F

variable (k : ℕ) (B' : ℝ) (Δ C : ℕ)

def tags (r : D.format.obj) := D.columns a (D.intervals a ha k B' Δ C r)

def collect (z : (D.Request a b).obj) :=
  D.scout a ha b z.1 (D.tags a ha k B' Δ C z.1) z.2

def collectCost (v N v' N' p : ℕ) :=
  200 * ((D.Request a b).width + (D.groupInput a).width + (D.Elected a).width +
    (Window.Fields S a n b).width) +
  Group.patchCost m d a n D.count v N + Group.cost (m + a) q n D.count +
    Window.collectCost S a n b v' N' p

variable {v N v' N' p u : ℕ} {L : Set (Table F)} {I : Type*}

theorem computes_collect (hu : 3 ≤ u) (hn : 0 < n)
    (hg : Access F u L (m + q) v N) (hv : (Group.Parcel d a n D.count).width ≤ v)
    (hc : Access F u L (m + d) v' N') (hv' : (Window.LabelSet a n).width ≤ v')
    (hb : Group.arity q n D.count ≤ u)
    (hL : (Group.keys F q n D.count Δ C (D.relative k B') : Set _) ⊆ L)
    (out : Map F u L (.addr D.scheme.ℓ) (Window.Outgoing S) (fun i => (D.scheme.decode i).outgoing) p)
    (X : I → (D.Request a b).obj)
    (hx : ∀ i, Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) (X i).1.1) :
    Computes F u L (D.Request a b) (D.Batch a b) X (D.collect a ha b k B' Δ C ∘ X)
      (fun _ => 1) (D.collectCost a b v N v' N' p) := by
  let A := D.Request a b
  have pr : Circuit F A D.format Prod.fst (A.width + 2 * D.format.width) :=
    Circuit.project Sum.inl fun _ _ => rfl
  let Y i := D.groups a ha (X i).1
  have g := Computes.of_map (L := L) (x := X) (y := Y)
    (Map.circuit hu (pr.comp (D.groups_circuit a ha))) (fun _ => rfl)
  have h := g.comp (Group.labels_net hu hn hg hv Y hx hb hL)
  have keep := Computes.of_map (L := L) (x := X) (y := X) (Map.circuit hu (Circuit.id F A)) (fun _ => rfl)
  let Z i := D.setup a b (X i, D.intervals a ha k B' Δ C (X i).1)
  have fields := (keep.pair hu h).comp
    (Computes.of_map (y := Z) (Map.circuit hu (D.setup_net a b)) (fun _ => rfl))
  have hit := fields.comp (Window.computes_gather S a n b hu hc hv' out (D.position a ha) Z hx)
  simp only [one_mul] at hit
  refine hit.mono ?_
  have hA : D.format.width ≤ A.width := by simp [A, Request]
  unfold collectCost
  rw [Format.width_pair (D.Request a b) (D.Elected a)]
  unfold A at *
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-!
# A common grouping and matching decision

Inactive hosts cast a zero ballot. The score uses only outgoing
stubs and interval labels; branch selectors cannot affect it.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing
open scoped Classical

variable {F T : Type} [Field F] (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h) (b k : ℕ)
  (cost : ℝ) (Δ C : ℕ)
local notation "n" => (D.scheme.h - a)

def chosen (r : D.format.obj) : B (n + 1) :=
  D.winner a b r (D.collect a ha b k cost Δ C (r, fun _ => 0))

omit [Field F] in
theorem choose_eq (v : (D.Request a b).obj) :
    D.chosen a ha b k cost Δ C v.1 = D.winner a b v.1 (D.collect a ha b k cost Δ C v) := by
  unfold chosen winner
  apply congrArg (elect ⊤)
  funext c i
  unfold vote sample
  split <;> rfl

def prepared (v : (D.Request a b).obj) : (D.Poll a b).obj :=
  (v.1, Window.gather D.scheme a n b (D.position a ha)
    (v.1.1, D.tags a ha k cost Δ C v.1, D.light a (D.chosen a ha b k cost Δ C v.1), v.2))

variable [Fintype T] {x y : Wire} {L : Fringe x y T} {u : ℕ} {r : D.format.obj}
  {G : HostNet F L D.scheme.h u} (p : D.Encodes r G) (σ : ℝ) (hu : 0 < u)

structure Selection where
  group : Grouping (inGroup a G.N) (inGroup a G.C) Δ C k cost (G.regroup a ha).load
  tags : ∀ v i j, D.tags a ha k cost Δ C r (p.post.host v) (cellIndex a i) (cellIndex n j) =
    intervalCode n (group.here (v, i) j).2
  matching : Scheme.Posting.Matchings a ha group
  color : matching.color = colorIndex n (D.chosen a ha b k cost Δ C r)
  control : p.post.Controls hu a ha group matching
  saving : (G.X : ℝ) / 4 - (L.Z + σ) ≤ u * (matching.count : ℝ)

theorem selection (hΔ : 0 < Δ) (hC : 0 < C) (hk : 1 ≤ k) (hn : k ≤ n) (hb : 0 < cost)
    (hG : G.Bounded Δ C cost) (hbins : 256 * (coreBins Δ + 1) ≤ 2 ^ k)
    (slack : (2 : ℝ) ^ k * cost * (Fintype.card G.V * 2 ^ a : ℕ) ≤ σ)
    (delayed : D.full = false → n ≤ 32 * Nat.clog 2 (2 * C)) :
    Nonempty (D.Selection a ha b k cost Δ C p σ hu) := by
  obtain ⟨g, hg⟩ := D.grouping a ha p k cost Δ C hΔ hC hk hn hb hG delayed
  have ht v i j : D.tags a ha k cost Δ C r (p.post.host v) (cellIndex a i) (cellIndex n j) =
      intervalCode n (g.here (v, i) j).2 := hg (v, i) j
  obtain ⟨t, hc, hctl, hshrink⟩ :=
    p.post.elected_matching hu a ha g (Group.embed p.post.host a) σ hb hG hbins slack
  exact ⟨⟨g, ht, t, hc.trans (D.winner_eq a ha b p g _ _ ht).symm, hctl, hshrink⟩⟩

namespace Selection
variable {a ha b k cost Δ C p σ hu}

theorem prepared_at (s : D.Selection a ha b k cost Δ C p σ hu)
    (z : (D.Candidate a b).obj) (v : G.V) (i : Cell a) :
    Window.matching D.scheme
      (((D.prepared a ha b k cost Δ C (r, z)).2 (p.post.host v)).2 (cellIndex a i)) =
        p.post.records a ha s.group s.matching.color (v, i) := by
  rw [s.color]
  exact D.records a ha b p s.group _ z s.tags _ v i

end Selection
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # Reading the elected grouping and matching at every child host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Selection
open Coloring Packing
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T}
  {D : Template F} {P : Gadget F} {z a b k Δ C : ℕ} {ha : a ≤ D.scheme.h}
  {r : D.format.obj} {G : HostNet F L D.scheme.h (P.b * z)} {p : D.Encodes r G}
  {B' σ : ℝ} {hu : 0 < P.b * z} (s : D.Selection a ha b k B' Δ C p σ hu)
  (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b)

local notation "n" => (D.scheme.h - a)

abbrev choices := s.group.Choice s.matching P

def selector : Transcript.Selector s.choices (D.Candidate a b).obj :=
  p.post.branches hu a ha s.group s.matching s.control P hb

variable (i : s.choices) (v : Site (G.V × Cell a) (D.scheme.h - a))

def state : State D.scheme P a D.scheme.h z Δ C k B' where
  T := T
  x := x
  y := y
  L := L
  G := G
  r := r.1
  p := p.post
  ha := ha
  hz := Nat.pos_of_mul_pos_left hu
  g := s.group
  m := s.matching
  ctl := s.control
  i := i
  selector j := Branches.read P ((s.selector hb).write i (p.post.placeGroup a j.1, j.2))
  selected t := p.post.read_branch hu a ha s.group s.matching s.control P hb i t
  v := v

def fields : (Window.Fields D.scheme a n b).obj :=
  (r.1, D.tags a ha k B' Δ C r, D.light a (D.chosen a ha b k B' Δ C r), (s.selector hb).write i)

theorem supplied : (s.state hb i v).Supplied (D.position a ha) (s.fields hb i) where
  old := rfl
  closed := p.closed
  index t j := by
    change D.position a ha (cellIndex a t) j = p.post.block _
    rw [position, Equiv.symm_apply_apply, p.block]
  label v c j := by
    obtain ⟨j, rfl⟩ := (cellIndex n).surjective j
    rw [Equiv.symm_apply_apply]
    exact s.tags v c j
  color j := by
    change decide (thick (colorIndex _ (D.chosen a ha b k B' Δ C r)) ((cellIndex _).symm j)) =
      decide (thick s.matching.color _)
    rw [s.color]
  choice _ _ := rfl

abbrev parents := D.counted a ha b (D.prepared a ha b k B' Δ C (r, (s.selector hb).write i))

def board {d : ℕ} (child : (Neighborhood.Rows (D.scheme.m + (n + 1)) d).obj)
    (live : B (D.scheme.m + (n + 1)) → Bool) (self : ∀ j, child j 0 = j) :
    (s.state hb i v).Board d (D.WithCount a b) Prod.fst where
  parent := s.parents hb i
  child := child
  live := live
  self := self
  view := by
    have H := (s.supplied hb i v).view
    exact ⟨H.nav, H.data, H.recv, H.extra⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Selection
end

/-!
# Selecting a common contraction and checking its branch encoding

At a vacant parent the seat mask is zero. The selector word itself
is retained even there, since nonzero padding must fail the guard.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] (D : Template F) (a b : ℕ) (P : Gadget F)

local notation "n" => (D.scheme.h - a + D.scheme.e)
local notation "M" => D.scheme.m

abbrev Slots := Branches.Slot M a n

def seatIndex : B ((M + a) + n) ≃ D.Slots a :=
  (Match.rowIndex (M + a) n).trans ((Match.rowIndex M a).prodCongr (.refl _))

def mark (x : (D.PollRow a b).obj) : (Side.Input n b).obj :=
  fun i => (x.1 && (Match.rows (Window.matching D.scheme x.2)).control.1 i, x.2.2.1 i)

def marks (x : (D.Poll a b).obj) : (Branches.Marked (D.Slots a) b).obj :=
  fun t => D.mark a b (D.live x.1 t.1.1, (x.2 t.1.1).2 t.1.2) t.2

def layout (x : (D.Poll a b).obj) : Bool :=
  Side.pick (profileOf P ∘ Branches.read P) (D.marks a b x ∘ D.seatIndex a)

def valid (x : (D.Poll a b).obj) : F :=
  ∏ i, Branches.test F (Fintype.card (Branches.Tag P)) (D.marks a b x i).1 (D.marks a b x i).2

namespace Selection

variable {T : Type} [Fintype T] {x y : Wire} {L : Fringe x y T}
  {D a b P} {z k Δ C : ℕ} {ha : a ≤ D.scheme.h}
  {r : D.format.obj} {G : HostNet F L D.scheme.h (P.b * z)} {p : D.Encodes r G}
  {B' σ : ℝ} {hu : 0 < P.b * z} (s : D.Selection a ha b k B' Δ C p σ hu)
  (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b)


local notation "seats" => p.post.seats hu a ha s.group s.matching s.control

theorem mask (t : (D.Candidate a b).obj) (j : D.Slots a) :
    (D.marks a b (D.prepared a ha b k B' Δ C (r, t)) j).1 = true ↔
      j ∈ Set.range seats := by
  let y := D.prepared a ha b k B' Δ C (r, t)
  apply p.post.seats_iff hu a ha s.group s.matching s.control (fun i => (D.marks a b y i).1)
  · rintro ⟨v, i⟩ j
    have hl := (p.live _).mpr ⟨v, rfl⟩
    change (D.live r (p.post.host v) &&
      (Match.rows (Window.matching D.scheme ((y.2 (p.post.host v)).2 (cellIndex a i)))).control.1 j) = _
    rw [hl, Bool.true_and, show Window.matching _ _ = _ from prepared_at D s t v i]
  · rintro ⟨v, i⟩ hv j
    have hl : D.live r v = false := by
      apply Bool.eq_false_iff.mpr
      intro he
      obtain ⟨w, hw⟩ := (p.live v).mp he
      exact hv ⟨(w, (cellIndex a).symm i), Prod.ext hw ((cellIndex _).apply_symm_apply _)⟩
    change (D.live r v && _) = false
    rw [hl, Bool.false_and]

theorem valid_eq (t : (D.Candidate a b).obj) :
    D.valid a b P (D.prepared a ha b k B' Δ C (r, t)) = ((s.selector hb).read t).elim 0 (fun _ => 1) :=
  p.post.guard_branch hu a ha s.group s.matching s.control P hb _ (s.mask t) t

theorem layout_eq (i : s.choices) :
    D.layout a b P (D.prepared a ha b k B' Δ C (r, (s.selector hb).write i)) =
      s.group.layout s.matching P i := by
  let t := (s.selector hb).write i
  let j := D.seatIndex a
  let w := (seats).trans j.symm.toEmbedding
  unfold layout Grouping.layout
  apply Side.pick_eq_side _ (s.group.profile s.matching i) _ w
  · intro z
    refine (s.mask t (j z)).trans ?_
    exact ⟨fun ⟨x, he⟩ => ⟨x, j.symm_apply_eq.mpr he⟩,
      fun ⟨x, he⟩ => ⟨x, j.symm_apply_eq.mp he⟩⟩
  · intro z
    change profileOf P (Branches.read P (t (j (j.symm ((seats) z))))) = _
    rw [Equiv.apply_symm_apply]
    exact congrArg (profileOf P) (p.post.read_branch hu a ha s.group s.matching s.control P hb i z)

end Selection
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # Checking gadget seats and computing the layout on the same records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] (D : Template F) (a b : ℕ)
local notation "n" => (D.scheme.h - a + D.scheme.e)
local notation "j" => (D.scheme.m + a)

abbrev Entries := Branches.Marked (D.Slots a) b
private abbrev Groups := Format.vec j (Side.Input n b)

def markTable := weightTable (A := D.PollRow a b) (D := Side.Input n b) (D.mark a b) (fun _ => (1 : F))

def markCost :=
  4 * ((D.Poll a b).width + 2 * (D.Polls a b).width) +
    2 ^ j * (1 + (D.PollRow a b).width + (Side.Input n b).width) +
    4 * ((D.Groups a b).width + 2 * (D.Entries a b).width)

variable {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u)
    (size : (D.PollRow a b).width + (Side.Input (D.scheme.h - a + D.scheme.e) b).width ≤ u) (allowed : D.markTable a b ∈ L)

include hu size allowed in
theorem map_marks :
    Map F u L (D.Poll a b) (D.Entries a b) (D.marks a b) (D.markCost a b) := by
  let f (x : (D.Groups a b).obj) (i : D.Slots a) := x ((Match.rowIndex _ _).symm i.1) i.2
  have post : Circuit F (D.Groups a b) (D.Entries a b) f
      ((D.Groups a b).width + 2 * (D.Entries a b).width) :=
    Circuit.project (fun t => ((Match.rowIndex _ _).symm t.1.1, t.1.2, t.2)) (fun _ _ => rfl)
  have lk : Map F u L (D.PollRow a b) (Side.Input n b) (D.mark a b)
      (1 + (D.PollRow a b).width + (Side.Input n b).width) := Kernel.lookup size allowed
  have H := ((Map.circuit hu (D.sampling a b)).comp (Map.vec _ (fun _ : B j => lk))).comp
    (Map.circuit hu post)
  convert H using 1
  · funext x i
    simp only [Function.comp_apply, marks, f, sample, Equiv.apply_symm_apply]
  · rfl

def layoutCost (t : ℕ) :=
  D.markCost a b + Fintype.card (D.Slots a) * Branches.charge b +
    4 * ((D.Entries a b).width + 2 * (Side.Input (j + n) b).width) + 4 * (2 ^ (j + n) * (100 + t) ^ 8)

include hu size allowed in
theorem layout_net (P : Gadget F) (t : ℕ) (hw : 2 ^ b ≤ t) (hp : 4 * P.b ≤ 2 ^ t) :
    Action F u L (D.Poll a b) .bit (D.layout a b P) (D.valid a b P) (D.layoutCost a b t) := by
  let profile (i : B b) := profileOf P (Branches.read P i)
  have bound (i : B b) : ∑ s, profile i s < 2 ^ t := by
    unfold profile
    cases Branches.read P i with
    | none => simp [profileOf]
    | some q => exact (P.cost _ q.2.property).trans_le hp
  have perm : Circuit F (D.Entries a b) (Side.Input (j + n) b) (fun x => x ∘ D.seatIndex a)
      ((D.Entries a b).width + 2 * (Side.Input (j + n) b).width) :=
    Circuit.project (fun i => ⟨D.seatIndex a i.1, i.2⟩) (fun _ _ => rfl)
  have mask := D.map_marks a b hu size allowed
  have valid := (Branches.check (J := D.Slots a) (b := b) hu (Fintype.card (Branches.Tag P))).pre mask
  exact (valid.post (Map.circuit hu perm)).post (Side.map_pick profile F hu L _ t hw bound)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-!
# Broadcasting the elected color
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring
open scoped Classical

variable {F : Type} [Field F] (D : Template F) (a b : ℕ) {u : ℕ} {L : Set (Table F)}
local notation "n" => (D.scheme.h - a)

abbrev Colors := Format.vec n .bit
abbrev Colored := (D.Poll a b).pair (D.Colors a)

def relight (x : (D.Colored a b).obj) : (D.Poll a b).obj :=
  (x.1.1, fun i => ((x.1.2 i).1, fun j =>
    let r := (x.1.2 i).2 j
    (r.1, r.2.1, x.2, r.2.2.2)))

def lightTable := weightTable (A := .addr (n + 1)) (D := D.Colors a) (D.light a) (fun _ => (1 : F))

theorem relight_net :
    Circuit F (D.Colored a b) (D.Poll a b) (D.relight a b)
      ((D.Colored a b).width + 2 * (D.Poll a b).width) := by
  let read : (D.Poll a b).pins → (D.Colored a b).pins
    | .inr (_, .inr (_, .inr (.inr (.inl k)))) => .inr k
    | i => .inl i
  exact Circuit.project read (by rintro x (i | ⟨i, j|⟨j, k|(k|(k|k))⟩⟩) <;> rfl)

def lightCost := D.pollCost a b + 1 + (n + 1) + (D.Colors a).width +
  40 * (D.Colored a b).width

theorem computes_relight {I : Type*} (hu : 3 ≤ u)
    (hw : (D.PollRow a b).width + (D.Vote a).width ≤ u) (hl : D.voteTable a b ∈ L)
    (hd : n + 1 + (D.Colors a).width ≤ u) (hk : D.lightTable a ∈ L)
    (X : I → (D.Poll a b).obj) :
    Computes F u L (D.Poll a b) (D.Poll a b) X
      (fun i => D.relight a b (X i, D.light a (D.winner a b (X i).1 (X i).2)))
      (fun _ => 1) (D.lightCost a b) := by
  have he : Map F u L (.addr (n + 1)) (D.Colors a) (D.light a)
      (1 + (Format.addr (n + 1)).width + (D.Colors a).width) :=
    Kernel.lookup (by rwa [Format.width_addr]) hk
  have hm := (D.map_winner a b hu hw hl).comp he
  have ht := Computes.of_map (x := X) hm (fun _ => rfl)
  have hi := Computes.of_map (L := L) (x := X) (y := X)
    (Map.circuit hu (Circuit.id F (D.Poll a b))) (fun _ => rfl)
  have h := (hi.pair hu ht).comp (Computes.of_map (Map.circuit hu (D.relight_net a b)) (fun _ => rfl))
  simp only [one_mul, Function.comp_apply] at h
  refine h.mono ?_
  unfold lightCost
  rw [Format.width_addr]
  have hp : (D.Poll a b).width ≤ (D.Colored a b).width := by simp [Colored]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-!
# Grouping and coloring cost from a common input template
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring
open scoped Classical

variable {F : Type} [Field F] (D : Template F) (a : ℕ) (ha : a ≤ D.scheme.h) (b k : ℕ)
  (cost : ℝ) (Δ C : ℕ)
local notation "S" => D.scheme
local notation "n" => (D.scheme.h - a)
local notation "m" => D.scheme.m
local notation "d" => D.scheme.d
local notation "q" => ((d + 1) * n)
local notation "X₀" => D.Request a b

def stubTable := weightTable (A := .addr D.scheme.ℓ) (D := Window.Outgoing S)
  (fun i => (D.scheme.decode i).outgoing) (fun _ => (1 : F))

def tableWidth := D.scheme.ℓ + (Window.Outgoing S).width

def keys : Finset (Table F) :=
  insert D.stubTable (insert (D.lightTable a) (insert (D.voteTable a b)
    (Group.keys F q n D.count Δ C (D.relative k cost))))

theorem card_keys : (D.keys a b k cost Δ C).card ≤ 5 := by
  unfold keys
  apply (Finset.card_insert_le _ _).trans
  apply Nat.add_le_add_right
  apply (Finset.card_insert_le _ _).trans
  apply Nat.add_le_add_right
  apply (Finset.card_insert_le _ _).trans
  exact Nat.add_le_add_right (Group.card_keys F) _

def arity := D.tableWidth + Group.arity q n D.count + (n + 1 + (D.Colors a).width) +
  ((D.PollRow a b).width + (D.Vote a).width)

def prepareCost (v N v' N' : ℕ) :=
  40 * (X₀).width + D.collectCost a b v N v' N' (1 + D.tableWidth) + D.lightCost a b

variable {v N v' N' u : ℕ} {L : Set (Table F)} {I : Type*}

theorem prepare_net (hu : 3 ≤ u) (hn : 0 < n)
    (hg : Access F u L (m + q) v N) (hv : (Group.Parcel d a n D.count).width ≤ v)
    (hc : Access F u L (m + d) v' N') (hv' : (Window.LabelSet a n).width ≤ v')
    (hb : D.arity a b ≤ u) (hL : (D.keys a b k cost Δ C : Set _) ⊆ L)
    (X : I → (X₀).obj)
    (hx : ∀ i, Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) (X i).1.1) :
    Computes F u L X₀ (D.Poll a b) X (D.prepared a ha b k cost Δ C ∘ X)
      (fun _ => 1) (D.prepareCost a b v N v' N') := by
  unfold arity at hb
  simp only [keys, Finset.coe_insert, Set.insert_subset_iff] at hL
  have out : Map F u L (.addr D.scheme.ℓ) (Window.Outgoing S)
      (fun i => (D.scheme.decode i).outgoing) (1 + D.tableWidth) := by
    have he : (Format.addr D.scheme.ℓ).width + (Window.Outgoing S).width = D.tableWidth := by
      simp [tableWidth]
    rw [← he, ← add_assoc]
    exact Kernel.lookup (by rw [he]; omega) hL.1
  have h := D.computes_collect a ha b k cost Δ C hu hn hg hv hc hv' (by omega) hL.2.2.2 out X hx
  have pr : Circuit F X₀ D.format Prod.fst ((X₀).width + 2 * D.format.width) :=
    Circuit.project Sum.inl fun _ _ => rfl
  have keep := Computes.of_map (L := L) (x := X) (Map.circuit hu pr) (fun _ => rfl)
  let Y i := ((X i).1, D.collect a ha b k cost Δ C (X i))
  have step := D.computes_relight a b hu (by omega) hL.2.2.1 (by omega) hL.2.1 Y
  have val : (fun i => D.relight a b (Y i, D.light a (D.winner a b (Y i).1 (Y i).2))) =
      D.prepared a ha b k cost Δ C ∘ X := by
    funext i
    simp only [Function.comp_apply, prepared, D.choose_eq a ha b k cost Δ C (X i)]
    rfl
  rw [val] at step
  have all := (keep.pair hu h).comp step
  simp only [mul_one] at all
  refine all.mono ?_
  unfold prepareCost
  have he : D.format.width ≤ (X₀).width := by simp [Request]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end
