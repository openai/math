import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames
import OAI.LinearAlgebra.MatrixExponent.Assembly.Matching
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood

/-!
# Emitting raw history keys

A stamp contains the block and the optional return hop to the original
host. One stub number completes the record for an old wire end. For a
matched pair the two rows are in thick, thin order.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation
open Coloring Packing HostNet History.Subround Spectral.Tensor
open scoped Classical

namespace Emission

abbrev Stamp (d h : ℕ) := Option (B d) × B h
abbrev Tip (d w h : ℕ) := Stamp d h × B w

variable {d w h b : ℕ}

def station (x : Stamp d h) : AtomKey d w h := (x, .inl ())
def checker (x : Stamp d h) : AtomKey d w h := (x, .inr (.inr ()))

def party (col : Bool) (tips : Fin 2 → Bool → Tip d w h) (j : Fin 6) : AtomKey d w h :=
  let c := roleCode col j
  let x := tips c.1 c.2
  (x.1, .inr (.inl (x.2, j)))

def stub (x : Tip d w h) (side : Bool) : StubKey d w h := ((checker x.1, side), x.2)

def exterior (x : Stamp d h) (j : B w) : SpanKey d w h b := .inl ((station x, false), j)

def demand (x : Tip d w h) (side : Bool) : SpanKey d w h b := .inl (stub x side)

def supply (col : Bool) (tips : Fin 2 → Bool → Tip d w h) (kind : Match.Kind b) (side : Bool) :
    SupplyKey d w h b :=
  (side, match kind with
    | .inl (j, k) => .inl (party col tips (cond side (sixPair j).2 (sixPair j).1), j, k)
    | .inr k => .inr (stub (tips 1 side) side, k))

/-- A loop has one hidden name. Both of its ends refer to its source. -/
def pointer (col : Bool) (tips : Fin 2 → Bool → Tip d w h)
    (kind : Match.Kind b) (loop side : Bool) : Bool × SpanKey d w h b :=
  (loop, .inr (supply col tips kind (if loop then false else side)))

/-- An equality constraint reads its old full-width end and one
separate span per replacement bundle. All reads start at offset zero. -/
def check (tips : Bool → Tip d w h) (loop side : Bool) :
    Option (Fin b) → Bool × SpanKey d w h b
  | none => (true, demand (tips side) side)
  | some k => pointer false (fun _ => tips) (.inr k) loop side

end Emission

variable {T F : Type} [Fintype T] {x y : Wire} {L : Fringe x y T} {h u d w : ℕ}
  {G : HostNet F L h u} (q : Navigation G d w)
  {Δ D k : ℕ} {B' : ℝ} (g : Grouping G.N G.C Δ D k B' G.load)
  (m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix) (col : Bool)

def stamp (v : G.V × Cell h) : Emission.Stamp d h :=
  (q.reverse (g.route m col v.1 v.2).1 v.1, cellIndex h v.2)

def tip (e : G.E) (side : Bool) : Emission.Tip d w h :=
  (q.stamp g m col (Scheme.side G e side, G.ix e), q.stub e side)

def tips (t : m.items) (j : Fin 2) := q.tip g m col (m.pairEdge (t, j))

theorem atom_station (v : G.diagram.V) :
    q.atomKey g m col (.inl v) = Emission.station (q.stamp g m col (G.units.place v)) := rfl

theorem atom_checker (v : G.V × Cell h) :
    q.atomKey g m col (.inr (.inr v)) = Emission.checker (q.stamp g m col v) := rfl

theorem atom_party (t : m.items) (j : Fin 6) :
    q.atomKey g m col (.inr (.inl ⟨t, j⟩)) = Emission.party col (q.tips g m col t) j := by
  have he : g.rep m col t j = (Scheme.side G (G.via g m col j t) (roleCode col j).2,
      G.ix (G.via g m col j t)) := by rw [G.role]; cases (roleCode col j).2 <;> rfl
  change (q.stamp g m col (g.rep m col t j), _) = _
  rw [he]
  rfl

theorem stub_eq (e : G.E) (s : Bool) :
    q.stubKey g m col e s = Emission.stub (q.tip g m col e s) s := rfl

variable [Field F] (P : Gadget F) (i : g.Choice m P)

def eventTips : g.Supply m P i → Fin 2 → Bool → Emission.Tip d w h
  | .inl ⟨t, _, _⟩ => q.tips g m col t
  | .inr (e, _) => fun _ => q.tip g m col e.val

def eventKind : g.Supply m P i → Match.Kind P.b
  | .inl ⟨t, j, k⟩ => .inl (j, k.castLE (by
      exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
        (P.cost _ (i t).2.property).le))
  | .inr (_, j) => .inr j

theorem supply_eq (e : g.Supply m P i) (s : Bool) :
    q.supplyKey g m col P i e s =
      Emission.supply col (q.eventTips g m col P i e) (eventKind g m P i e) s := by
  rcases e with ⟨t, j, a⟩ | ⟨t, a⟩
  · cases s <;> simp only [supplyKey, supplyAtom, Grouping.supplies, eventKind, eventTips,
      Emission.supply, Bool.cond_false, Bool.cond_true, atom_party]
  · rfl

theorem hidden_old (e : G.E) (s : Bool) :
    q.hiddenKey g m P i (cond s (.inr (.inl e)) (.inl e)) =
      Emission.demand (q.tip g m (g.layout m P i) e s) s := by cases s <;> rfl

theorem hidden_new (e : g.Supply m P i) (s : Bool) :
    let c := g.layout m P i
    (true, q.hiddenKey g m P i (.inr (.inr e))) =
      Emission.pointer c (q.eventTips g m c P i e) (eventKind g m P i e) true s := by
  simp only [hiddenKey, Emission.pointer, ite_true, supply_eq]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation
open Coloring Packing History.Subround
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h z d : ℕ}
    (P : Gadget F) (G : HostNet F L h (P.b * z))
    {Δ D k : ℕ} {B' : ℝ} (g : Grouping G.N G.C Δ D k B' G.load)
    (m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix) (i : g.Choice m P)
    {S : Scheme F} {r : S.format.obj} (p : S.Presentation r G.diagram)
    (q : Navigation G d S.e)

theorem visible_old (e : p.BorderSpan) :
    q.faceKey P G g m i p (.inl e) =
      Emission.exterior (q.stamp g m (g.layout m P i) (G.units.place e.val.1)) e.val.2 := rfl

theorem visible_new (e : g.Survivors m P i) (s : Bool) :
    let c := g.layout m P i
    (false, q.faceKey P G g m i p (.inr (e, s))) =
      Emission.pointer c (q.eventTips g m c P i e.val) (eventKind g m P i e.val) false s := by
  simp only [faceKey, Emission.pointer, Bool.false_eq_true, ite_false, supply_eq]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation
end

/-! # Reading the stub and reverse hop of an emitted contact -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Posting
open Coloring Packing
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u h : ℕ}
  {S : Scheme F} {r : S.format.obj} {G : HostNet F L h u}
  (p : S.Posting r G) (hu : 0 < u) (a : ℕ) (ha : a ≤ h) {Δ D k : ℕ} {B' : ℝ}
  (g : Grouping (inGroup a G.N) (inGroup a G.C) Δ D k B' (G.regroup a ha).load)

local notation "H" => G.regroup a ha
local notation "q" => p.navigation hu a ha

theorem record_stub (c : Color (h - a)) (e : (H).E) :
    (((p.records a ha g c ((H).src e)).2.1 (cellIndex _ ((H).ix e))).2 ((q).stub e false)).2 =
      ((q).slot ((H).src e) ((H).dst e), (q).stub e true) := by
  change G.E at e
  change (p.localStub (G.src e) ((splitCell a ha).symm
    (ancestor ha (G.ix e), (cellIndex _).symm (cellIndex _ (suffix a (G.ix e)))))
    (p.stub e false)).2 = _
  rw [Equiv.symm_apply_apply, show (ancestor ha _, suffix a _) = splitCell a ha (G.ix e) from rfl,
    Equiv.symm_apply_apply]
  exact p.local_slot e

/-- Read the opposite stub at a given grouped occurrence. -/
def receiving (v : G.V × Cell a) (b : B (h - a)) (s : B S.e) :=
  (S.decode ((r (p.host v.1)).2 (p.block ((splitCell a ha).symm
    (v.2, (cellIndex _).symm b))))).peer 0 s

omit [Fintype T] in
theorem receiving_eq (e : (H).E) :
    p.receiving a ha ((H).dst e) (cellIndex _ ((H).ix e)) ((q).stub e true) =
      some ((q).slot ((H).dst e) ((H).src e), 0, (q).stub e false) := by
  change G.E at e
  unfold receiving
  rw [Equiv.symm_apply_apply]
  change (S.decode ((r (p.host (G.dst e))).2
    (p.block ((splitCell a ha).symm (splitCell a ha (G.ix e)))))).peer 0 (p.stub e true) = _
  rw [Equiv.symm_apply_apply]
  exact p.link e true

omit [Fintype T] in
theorem reverse_eq (e : (H).E) :
    (q).reverse ((H).dst e) ((H).src e) =
      if (H).dst e = (H).src e then none else
        (p.receiving a ha ((H).dst e) (cellIndex _ ((H).ix e)) ((q).stub e true)).map Prod.fst := by
  rw [receiving_eq]
  rfl

variable (m : Matchings a ha g) (ctl : p.Controls hu a ha g m)

local notation "data" => p.records a ha g m.color

/-- Locate the receiving stub of the thick mate of a sampled thin row. -/
def mateAddress {d n e l : ℕ} (x : (Match.Input d n e e l).obj) (b : B n) : B n × B e :=
  let ctrl := (Match.rows x).control
  let i := Match.rowIndex n e (ctrl.2 (Match.sampleRow ctrl.1 b))
  (i.1, ((x.2.1 i.1).2 i.2).2.2)

include ctl in
theorem mateAddress_eq (col : Bool) (v : (H).V) (b : Cell (h - a))
    (hm : (g.route m col v b).1 ≠ v) :
    ∃ e : (H).E, (H).src e = v ∧ (H).dst e = (g.route m col v b).1 ∧
      mateAddress (data v) (cellIndex _ b) = (cellIndex _ ((H).ix e), (q).stub e true) := by
  cases col
  · exact (hm rfl).elim
  let chart := p.chart hu a ha g m ctl
  let row := Match.rows (data v)
  let i := Match.sampleRow row.control.1 (cellIndex _ b)
  have hs : row.control.1 i = true := by
    have hh := (chart.stubs.motion_spec _ _ chart.records chart.controls
      (g.loc v b) b (chart.labels v b)).1
    change row.control.1 i = _ at hh
    rw [hh]
    cases he : m.plan (g.loc v b) b with
    | none =>
      exfalso
      apply hm
      change ((m.plan (g.loc v b) b).getD (g.loc v b)).1 = v
      rw [he]
      rfl
    | some _ => rfl
  obtain ⟨j, hj⟩ := (chart.marks (v, i)).mp hs
  have hjv : (H).src j.val = v := congrArg Prod.fst hj
  have hji : chart.stubs.pos j.val = i := congrArg Prod.snd hj
  have hjb : (H).ix j.val = b := by
    apply (cellIndex _).injective
    have hb := Match.sampleRow_block row.control.1 (cellIndex _ b)
    change (Match.rowIndex _ _ i).1 = _ at hb
    rw [← hji, Match.Stubs.pos, Equiv.apply_symm_apply] at hb
    exact hb
  let e := m.mate j
  have he : (H).src e = v := (congrArg Sigma.fst (m.spec j).2.1).trans hjv
  have hd : (H).dst e = (g.route m true v b).1 := by
    rw [← hjv, ← hjb, g.route_thin m true j]
    rfl
  refine ⟨e, he, hd, ?_⟩
  have hp := chart.controls.mate j
  change chart.stubs.pos e = (Match.rows (data ((H).src j.val))).control.2 (chart.stubs.pos j.val) at hp
  rw [hjv, hji] at hp
  unfold mateAddress
  dsimp only
  rw [← hp, Match.Stubs.pos, Equiv.apply_symm_apply, ← he]
  have hr := congrArg Prod.snd (p.record_stub hu a ha g m.color e)
  exact Prod.ext rfl hr

include ctl in
theorem reverse_move (col : Bool) (v : (H).V) (b : Cell (h - a)) :
    let t := (g.route m col v b).1
    let addr := mateAddress (data v) (cellIndex _ b)
    (q).reverse t v = if t = v then none else (p.receiving a ha t addr.1 addr.2).map Prod.fst := by
  dsimp only
  by_cases hm : (g.route m col v b).1 = v
  · rw [ite_eq_left hm]
    exact ite_eq_left hm
  obtain ⟨e, hs, hd, he⟩ := p.mateAddress_eq hu a ha g m ctl col v b hm
  rw [he, ← hd, ← hs]
  exact p.reverse_eq hu a ha e

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Posting
end

/-!
# Reading the raw history keys from row and movement records

A moved occurrence needs the return stub of the sampled row's mate.
The other three fields are the block, orientation and stub in an old
edge record. The computation uses no global edge identifier.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing
open scoped Classical

namespace Navigation.Emission

variable {V : Type} {d h w ℓ : ℕ}
    (nav : V → B d → V) (data : V → (Match.Input d h w w ℓ).obj)
    (recv : V → B h → B w → Option (B d)) (col : Bool)

def stampAt (v : V) (t : B h) : Stamp d h :=
  let dst := (Match.follow nav v (Match.action col (data v) t)).1
  let addr := Scheme.Posting.mateAddress (data v) t
  (if dst = v then none else recv dst addr.1 addr.2, t)

def tipAt (v : V) (i : B (h + w)) (side : Bool) : Tip d w h :=
  let (b, j) := Match.rowIndex h w i
  let dst := (((data v).2.1 b).2 j).2
  let host := cond side (nav v dst.1) v
  (stampAt nav data recv col host b, cond side dst.2 j)

def partyTips (v : V) (i : B (h + w)) (j : Fin 2) :=
  tipAt nav data recv col v (if j = 0 then (Match.rows (data v)).control.2 i else i)

def supplyTips {b : ℕ} (e : Match.Candidate V (h + w) b) : Fin 2 → Bool → Tip d w h :=
  match e.2 with
  | .inl _ => partyTips nav data recv col e.1.1 e.1.2
  | .inr _ => fun _ => tipAt nav data recv col e.1.1 e.1.2

end Navigation.Emission

namespace Scheme.Posting
open Navigation.Emission

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u h : ℕ}
  {S : Scheme F} {r : S.format.obj} {G : HostNet F L h u}
  (p : S.Posting r G) (hu : 0 < u) (a : ℕ) (ha : a ≤ h) {Δ D k : ℕ} {B' : ℝ}
  (g : Grouping (inGroup a G.N) (inGroup a G.C) Δ D k B' (G.regroup a ha).load)
  (m : Matchings a ha g) (ctl : p.Controls hu a ha g m) (col : Bool)

local notation "H" => G.regroup a ha
local notation "q" => p.navigation hu a ha
local notation "c" => p.chart hu a ha g m ctl
local notation "data" => p.records a ha g m.color

def recv (v : (H).V) (t : B (h - a)) (i : B S.e) : Option (B S.d) :=
  (p.receiving a ha v t i).map Prod.fst

include ctl in
theorem stamp_eq (v : (H).V) (t : Cell (h - a)) :
    (q).stamp g m col (v, t) =
      stampAt (p.groupNav a) data (p.recv a ha) col v (cellIndex _ t) := by
  have he := congrArg Prod.fst ((c).moved col v t)
  change (Match.follow _ v (Match.action col (data v) (cellIndex _ t))).1 = (g.route m col v t).1 at he
  let addr := mateAddress (data v) (cellIndex _ t)
  let f (w : (H).V) := if w = v then none else p.recv a ha w addr.1 addr.2
  have hr : (q).reverse (g.route m col v t).1 v = f (g.route m col v t).1 :=
    p.reverse_move hu a ha g m ctl col v t
  exact Prod.ext (hr.trans (congrArg f he.symm)) rfl

theorem tip_eq (e : (H).E) (b : Bool) :
    (q).tip g m col e b =
      tipAt (p.groupNav a) data (p.recv a ha) col ((H).src e) ((c).stubs.pos e) b := by
  have hpos : Match.rowIndex _ _ ((c).stubs.pos e) =
      (cellIndex _ ((H).ix e), (q).stub e false) := Equiv.apply_symm_apply _ _
  have hdst : p.groupNav a ((H).src e) ((q).slot ((H).src e) ((H).dst e)) = (H).dst e :=
    (c).contacts e
  unfold tipAt
  rw [hpos]
  simp only [p.record_stub hu a ha g m.color e, hdst]
  cases b <;> simp only [Navigation.tip, Scheme.side, Bool.cond_false, Bool.cond_true,
    p.stamp_eq hu a ha g m ctl] <;> rfl

theorem tips_eq (t : m.items) :
    (q).tips g m col t =
      partyTips (p.groupNav a) data (p.recv a ha) col ((H).src t.val) ((c).stubs.pos t.val) := by
  have hp : (Match.rows (data ((H).src t.val))).control.2 ((c).stubs.pos t.val) =
      (c).stubs.pos (m.mate t) := ((c).controls.mate t).symm
  have hs : (H).src (m.mate t) = (H).src t.val := congrArg Sigma.fst (m.spec t).2.1
  funext j b
  fin_cases j
  · change (q).tip g m col (m.mate t) b = tipAt _ _ _ _ _ _ _
    rw [p.tip_eq hu a ha g m ctl, hs, ← hp]
    rfl
  · exact p.tip_eq hu a ha g m ctl col t.val b

variable (P : Gadget F) (i : g.Choice m P)

theorem eventTips_eq (e : g.Supply m P i) :
    (q).eventTips g m col P i e =
      supplyTips (p.groupNav a) data (p.recv a ha) col ((c).event P i e) := by
  rcases e with ⟨t, j, s⟩ | ⟨t, s⟩
  · exact p.tips_eq hu a ha g m ctl col t
  · funext j b
    exact p.tip_eq hu a ha g m ctl col t.val b

theorem eventKind_eq (e : g.Supply m P i) :
    Navigation.eventKind (G := H) g m P i e = ((c).event P i e).2 := by
  rcases e with ⟨t, j, s⟩ | ⟨t, s⟩ <;> rfl

/-- Both endpoints use their old offset, even if the occurrence moves. -/
theorem old_offset (e : (H).E) (s : Bool) (t : Fin u) :
    let name := tipAt (p.groupNav a) data (p.recv a ha) col ((H).src e) ((c).stubs.pos e) s
    let j := p.toSeating.ends (endBit G e s t)
    j.1.2 = name.2 ∧ j.2.val = t.val := by
  dsimp only
  rw [← p.tip_eq hu a ha g m ctl]
  obtain ⟨he, ht⟩ := p.ordered e s t
  exact ⟨congrArg Prod.snd he, ht⟩

/-- Reading either address gives the anchor of the corresponding factor,
so the opposite endpoint can be located from this same event. -/
theorem event_anchor (e : g.Supply m P i) (s : Bool) :
    let j := (c).event P i e
    let path := Match.paths (p.groupNav a) data col j
    (c).site ((H).anchor g m col (Navigation.supplyAtom (G := H) g m P i e s)) =
      Match.readPath (p.groupNav a) j.1.1 (cond s path.2 path.1) := by
  have he := (c).read_event P i col e
  dsimp only
  rw [Navigation.supply_anchor (G := H) g m col P i e s]
  cases s
  · exact (congrArg Prod.fst he).symm
  · exact (congrArg Prod.snd he).symm

end Scheme.Posting
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Comparing rooted neighborhoods by short addresses

A walk is recorded last hop first. Equality of two neighborhoods
requires the same local records along every bounded walk and the
same coincidence pattern of visited hosts. Absolute names may differ.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Window
open Coloring Match Navigation.Emission
open scoped Classical

variable {V W X : Type} {d h e ℓ : ℕ}

def visit (nav : V → B d → V) (root : V) (path : List (B d)) :=
  path.foldr (fun i v => nav v i) root

structure Env (V X : Type) (d h e ℓ : ℕ) where
  nav : V → B d → V
  data : V → (Input d h e e ℓ).obj
  recv : V → B h → B e → Option (B d)
  extra : V → X
  root : V

namespace Env
variable (α : Env V X d h e ℓ)
def node := visit α.nav α.root
abbrev stamp := stampAt α.nav α.data α.recv
abbrev tip := tipAt α.nav α.data α.recv
abbrev tips := partyTips α.nav α.data α.recv
abbrev supplies {b : ℕ} := supplyTips (b := b) α.nav α.data α.recv
end Env

variable (α : Env V X d h e ℓ) (β : Env W X d h e ℓ)

def Related (n : ℕ) (v : V) (w : W) : Prop :=
  ∃ path, path.length ≤ n ∧ α.node path = v ∧ β.node path = w

structure Agree (n : ℕ) : Prop where
  same : ∀ p q, p.length ≤ n → q.length ≤ n →
    (α.node p = α.node q ↔ β.node p = β.node q)
  data : ∀ p, p.length ≤ n → α.data (α.node p) = β.data (β.node p)
  recv : ∀ p, p.length ≤ n → α.recv (α.node p) = β.recv (β.node p)
  extra : ∀ p, p.length ≤ n → α.extra (α.node p) = β.extra (β.node p)

variable {α β} {v v' : V} {w w' : W} {n k : ℕ}

theorem Agree.symm (a : Agree α β n) : Agree β α n :=
  ⟨fun p q h h' => (a.same p q h h').symm, fun p h => (a.data p h).symm,
    fun p h => (a.recv p h).symm, fun p h => (a.extra p h).symm⟩

theorem related_root : Related α β 0 α.root β.root := ⟨[], le_rfl, rfl, rfl⟩

variable (a : Agree α β n) (r : Related α β k v w)

theorem Related.widen (h : k ≤ n) (r : Related α β k v w) : Related α β n v w := by
  obtain ⟨p, hp, hv, hw⟩ := r
  exact ⟨p, hp.trans h, hv, hw⟩

include r in
theorem Related.next (j : B d) : Related α β (k + 1) (α.nav v j) (β.nav w j) := by
  obtain ⟨p, hp, rfl, rfl⟩ := r
  exact ⟨j::p, Nat.succ_le_succ hp, rfl, rfl⟩

include a in
theorem Agree.equal (r : Related α β n v w) (s : Related α β n v' w') :
    v = v' ↔ w = w' := by
  obtain ⟨p, hp, rfl, rfl⟩ := r
  obtain ⟨q, hq, rfl, rfl⟩ := s
  exact a.same p q hp hq

include a r

theorem Agree.records (hk : k ≤ n) :
    α.data v = β.data w ∧ α.recv v = β.recv w ∧ α.extra v = β.extra w := by
  obtain ⟨p, hp, rfl, rfl⟩ := r
  exact ⟨a.data p (hp.trans hk), a.recv p (hp.trans hk), a.extra p (hp.trans hk)⟩

omit a in
theorem Related.follow (x : (Move d ℓ).obj) :
    Related α β (k + 1) (follow α.nav v x).1 (follow β.nav w x).1 := by
  unfold Match.follow
  split_ifs
  · exact r.next _
  · exact r.widen (by omega)

omit a in
theorem Related.path (x : (Match.Path d ℓ).obj) :
    Related α β (k + 2) (readPath α.nav v x).1 (readPath β.nav w x).1 := by
  unfold readPath
  split_ifs
  · exact (r.next _).follow _
  · exact (r.follow _).widen (by omega)

theorem Agree.ends (hk : k + 1 ≤ n) (c : Bool) :
    localEnds α.nav α.data c v = localEnds β.nav β.data c w := by
  have remote : (fun i => action c (α.data (α.nav v i))) =
      (fun i => action c (β.data (β.nav w i))) := by
    funext i
    rw [(a.records (r.next i) hk).1]
  unfold localEnds
  rw [remote, (a.records r (by omega)).1]

theorem Agree.parties (hk : k + 1 ≤ n) (c : Bool) :
    localParties α.nav α.data c v = localParties β.nav β.data c w := by
  funext i
  unfold localParties
  rw [a.ends r hk c, (a.records r (by omega)).1]

theorem Agree.paths (hk : k + 1 ≤ n) (c : Bool) (i : B (h + e)) {b : ℕ} (j : Kind b) :
    Match.paths α.nav α.data c ((v, i), j) = Match.paths β.nav β.data c ((w, i), j) := by
  rcases j with ⟨j, t⟩|t
  · simp only [Match.paths, a.parties r hk c]
  · exact congrFun (a.ends r hk c) i

theorem Agree.stamp (hk : k + 1 ≤ n) (c : Bool) (i : B h) :
    α.stamp c v i = β.stamp c w i := by
  have hd := (a.records r (by omega)).1
  let x := action c (β.data w) i
  have t := r.follow x
  unfold Env.stamp stampAt
  rw [hd]
  change (if (follow α.nav v x).1 = v then none else _, i) =
    (if (follow β.nav w x).1 = w then none else _, i)
  have hr := (a.records t hk).2.1
  have he := a.equal (t.widen hk) (r.widen (by omega))
  dsimp only [x] at *
  simp only [he, hr]

theorem Agree.tip (hk : k + 2 ≤ n) (c : Bool) (i : B (h + e)) (s : Bool) :
    α.tip c v i s = β.tip c w i s := by
  have hd := (a.records r (by omega)).1
  unfold Env.tip tipAt
  rw [hd]
  cases s
  · exact Prod.ext (a.stamp r (by omega) c _) rfl
  · exact Prod.ext (a.stamp (r.next _) hk c _) rfl

theorem Agree.tips (hk : k + 2 ≤ n) (c : Bool) (i : B (h + e)) :
    α.tips c v i = β.tips c w i := by
  funext j s
  unfold Env.tips partyTips
  rw [(a.records r (by omega)).1]
  exact a.tip r hk c _ s

theorem Agree.supplies (hk : k + 2 ≤ n) (c : Bool) (i : B (h + e)) {b : ℕ} (j : Kind b) :
    α.supplies c ((v, i), j) = β.supplies c ((w, i), j) := by
  cases j
  · exact a.tips r hk c _
  · exact funext fun _ => funext fun s => a.tip r hk c _ s

end OAI.LinearAlgebra.MatrixExponent.Assembly.Window
end

/-!
# Gathering histories along bounded walks

Each announcement exchanges all groups in a single payload. Paths
are indexed independently of their endpoints, including when many
paths end at the same host.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Window
open Coloring Neighborhood

variable {m d a r : ℕ} {A : Format}

abbrev Walks (r d : ℕ) (A : Format) := Format.vec ((d + 1) * r) A

def reads (r : ℕ) (X : (Fmt.groups m d a A).obj) : (Fmt.groups m d a (Walks r d A)).obj :=
  fun i => ((X i).1, fun j k => (X (walks r (fun x => (X x).1) i k)).2 j)

private def previous (k : B ((d + 1) * (r + 1))) : B ((d + 1) * r) :=
  (path_surjective d r (path d (r + 1) k).2).choose

private def advance (d r : ℕ) (A : Format) (x : (Walks r d A).obj × (B d → (Walks r d A).obj)) :
    (Walks (r + 1) d A).obj :=
  fun k => ((path d (r + 1) k).1.elim x.1 x.2) (previous k)

private theorem continuation (X : (Fmt.groups m d a A).obj) :
    announce (A := Walks r d A) (H := Walks r d A) (O := Walks (r + 1) d A)
      id (advance d r A) (reads r X) = reads (r + 1) X := by
  funext i
  refine Prod.ext (show _ = _ from rfl) ?_
  funext j k
  have hk : path d r (previous k) = (path d (r + 1) k).2 :=
    (path_surjective d r (path d (r + 1) k).2).choose_spec
  simp only [announce, advance, id_eq, reads, walks, run]
  cases (path d (r + 1) k).1 <;> simp only [Option.elim_none, Option.elim_some, hk]

variable {F : Type} [Field F] {u v n : ℕ} {L : Set (Table F)}

private theorem advance_net :
    let Z := Walks r d A
    let W := Walks (r + 1) d A
    Circuit F (.pair Z (.vec d Z)) W (advance d r A)
      ((Format.pair Z (.vec d Z)).width + 2 * W.width) := by
  intro Z W
  let pin (q : W.pins) : (Format.pair Z (.vec d Z)).pins :=
    (path d (r + 1) q.1).1.elim (.inl (previous q.1, q.2)) (fun z => .inr (z, previous q.1, q.2))
  apply Circuit.project pin
  rintro x ⟨i, j⟩
  change A.code (advance d r A x i) j = _
  simp only [advance, pin]
  cases (path d (r + 1) i).1 <;> rfl

def readCost (m d v n : ℕ) := gatherCost m d v n + 1000 * (2 ^ m * (2 ^ d * (m + v) + v))

private theorem cost_bound (Z W : Format) (hz : 2 ^ a * Z.width ≤ v) (hw : 2 ^ a * W.width ≤ v) :
    announceCost m d a v n Z Z (4 * Z.width)
      (4 * ((Format.pair Z (.vec d Z)).width + 2 * W.width)) ≤ readCost m d v n := by
  have h₁ := Nat.mul_le_mul_left (2 ^ m) hz
  have h₂ := Nat.mul_le_mul_left (2 ^ m * 2 ^ d) hz
  have h₃ := Nat.mul_le_mul_left (2 ^ m) hw
  simp only [announceCost, readCost, Fmt.groups, Fmt.bank, Format.width_vec, Format.width_pair, Format.width_addr]
  ring_nf at h₁ h₂ h₃ ⊢
  omega

theorem reads_net {I : Type*} (hu : 3 ≤ u) (ht : Access F u L (m + d) v n)
    (X : I → (Fmt.groups m d a A).obj) (hx : ∀ i, Fmt.Reciprocal (.vec a A) (X i))
    (hr : 2 ^ a * (Walks r d A).width ≤ v) :
    Computes F u L (Fmt.groups m d a A) (Fmt.groups m d a (Walks r d A))
      X (fun i => reads r (X i)) (fun _ => 1) ((r + 1) * readCost m d v n) := by
  induction r with
  | zero =>
    let E := Fmt.groups m d a A
    let O := Fmt.groups m d a (Walks 0 d A)
    have c : Circuit F E O (reads 0) (E.width + 2 * O.width) := by
      let pin : O.pins → E.pins
        | (i, .inl j) => (i, .inl j)
        | (i, .inr (j, _, k)) => (i, .inr (j, k))
      apply Circuit.project pin
      rintro x ⟨i, j|⟨j, k, l⟩⟩ <;> rfl
    refine (Computes.of_map (Map.circuit hu c) (fun _ => rfl)).mono ?_
    simp only [E, O, Fmt.groups, Fmt.bank, Walks, Format.width_vec, Format.width_pair, Format.width_addr,
      mul_zero, pow_zero, one_mul, readCost, zero_add] at hr ⊢
    have hh := Nat.mul_le_mul_left (2 ^ m) hr
    ring_nf at hh ⊢
    omega
  | succ r ih =>
    let Z := Walks r d A
    let W := Walks (r + 1) d A
    have hz : 2 ^ a * Z.width ≤ v := le_trans (Nat.mul_le_mul_left _ (by
      unfold Z Walks
      simp only [Format.width_vec]
      gcongr; omega)) hr
    have h := computes_announce (L := L) hu ht (show (Format.vec a Z).width ≤ v by simpa using hz)
      (fun i => reads r (X i)) hx (Map.circuit hu (Circuit.id F Z))
      (Map.circuit hu (advance_net (r := r) (d := d) (A := A)))
    have hk := (ih hz).comp (h.mono (cost_bound Z W hz hr))
    rw [show (fun i => announce id (advance d r A) (reads r (X i))) = (fun i => reads (r + 1) (X i)) from funext (fun i => continuation (X i))] at hk
    simpa only [one_mul, Nat.succ_mul] using hk

end OAI.LinearAlgebra.MatrixExponent.Assembly.Window
end
