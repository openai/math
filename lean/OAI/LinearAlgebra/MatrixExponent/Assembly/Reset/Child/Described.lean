import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Ports.Eval
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Factor
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Apply
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Headers
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Follow
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep

/-!
# Relocating frozen stations after a reset

Retain the old seat and the suffix of the mixed block. The child block
supplies the prefix, so the inverse mixer recovers the original block.
The ownership test suppresses duplicates at all other children.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup

open Packing Coloring
open scoped Classical
variable {F : Type} [Field F] [Fintype F] {A : Template F} {u a Δ D Y w : ℕ} {W c : ℝ}
  [NeZero Y] [NeZero w] (T : Attachment A) (U : Setup A.scheme A.scheme.h u a Δ D Y w W)
  {R : Rotor F Y w} {fit : U.Fits R c} {e cap t d : ℕ} {b : Book A.scheme u e cap}

local notation "n" => A.scheme.h - a
local notation "k" => A.scheme.h - a + T.k

def recover (i : B a) (j : B n) : Cell A.scheme.h :=
  U.Z.π.symm ((splitCell a U.groups).symm ((cellIndex a).symm i, (cellIndex _).symm j))

omit [Fintype F] [NeZero Y] [NeZero w] in
theorem recover_eq (i : B a) (j : B n) (s : Cell A.scheme.h) :
    U.recover i j = s ↔ i = cellIndex a (U.Z.group s) ∧
      j = cellIndex _ (suffix a (U.Z.π s)) := by
  unfold recover
  rw [LinearEquiv.symm_apply_eq, Equiv.symm_apply_eq]
  change (_, _) = (U.Z.group s, suffix a (U.Z.π s)) ↔ _
  rw [Prod.mk.injEq, Equiv.symm_apply_eq, Equiv.symm_apply_eq]

def resetSlot (slot : U.T → B T.k) (i : U.T) : B k :=
  (Match.rowIndex n T.k).symm (cellIndex _ (suffix a (U.Z.π (U.G.park i).2)), slot i)

omit [Fintype F] [NeZero Y] [NeZero w] in
theorem resetSlot_pos (slot : U.T → B T.k) (hs : ∀ i, slot i ≠ 0) (i : U.T) :
    resetSlot T U slot i ≠ 0 := by
  intro h
  have hz : (Match.rowIndex n T.k 0).2 = 0 := by apply Fin.ext; simp [Match.rowIndex]
  have h' := congrArg (fun z => (Match.rowIndex n T.k z).2) h
  rw [resetSlot, Equiv.apply_symm_apply, hz] at h'
  exact hs i h'

variable {U} (M : Template.Meter) (L : U.Layout R fit b (A.scheme.m + t) d)
local notation "Out" => A.resetTarget b M (A.scheme.m + t) d a
local notation "P" => U.result R fit

def hosts (j : B (A.scheme.m + t)) (s : Cell A.scheme.h) :=
  ∃ v, L.host ((P).owner (v, s)).2 = j

def relocation : T.Relocation Out k where
  parent := Setup.parent A t
  prev v i j :=
    let y := Match.rowIndex n T.k j
    let s := U.recover i y.1
    if hosts L v s then some (cellIndex _ s, y.2) else none

variable {L} {locate : Coord R A.scheme.h a Δ ↪ B t} (pl : Placed A L locate)

include pl in
theorem Placed.owner_parent (v : U.G.V) (j : Cell A.scheme.h) :
    Setup.parent A t (L.host ((P).owner (v, j)).2) = U.post.host v := by
  rw [pl.parent, (P).origin_owner]

include pl in
theorem Placed.back (slot : U.T → B T.k) (i : U.T) (v : B (A.scheme.m + t)) (j : B a) (s : B k) :
    (relocation T M L).back (v, j, s) =
      some (U.post.host (U.G.park i).1, cellIndex _ (U.G.park i).2, slot i) ↔
    (v, j, s) = (L.host ((U.graph R fit).park i).1, cellIndex a ((U.graph R fit).park i).2,
      resetSlot T U slot i) := by
  let p := U.G.park i
  let q := Match.rowIndex n T.k
  let block := U.recover j (q s).1
  let grp := cellIndex a (U.Z.group p.2)
  let suffixIdx := cellIndex _ (suffix a (U.Z.π p.2))
  let dest := L.host ((P).owner p).2
  change Option.map (Prod.mk (Setup.parent A t v))
    (if hosts L v block then some (cellIndex _ block, (q s).2) else none) =
    some (U.post.host p.1, cellIndex _ p.2, slot i) ↔ (v, j, s) = (dest, grp, q.symm (suffixIdx, slot i))
  constructor
  · intro he
    split at he <;> try contradiction
    rename_i h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, (cellIndex _).injective.eq_iff] at he
    obtain ⟨hv, hb, hs⟩ := he
    obtain ⟨hj, hq⟩ := (U.recover_eq ..).mp hb
    obtain ⟨u, hu⟩ := h
    have hu' : u = p.1 := U.post.host.injective ((pl.owner_parent u block).symm.trans (hu ▸ hv))
    rw [hu', hb] at hu
    exact Prod.ext hu.symm (Prod.ext hj (q.eq_symm_apply.mpr (Prod.ext hq hs)))
  · intro he
    obtain ⟨hv, hj, hs⟩ := (by simpa only [Prod.mk.injEq] using he)
    have eqn := q.eq_symm_apply.mp hs
    have hb : block = p.2 := (U.recover_eq ..).mpr ⟨hj, congrArg Prod.fst eqn⟩
    have ok : hosts L v block := ⟨p.1, by rw [hb]; exact hv.symm⟩
    rw [ite_eq_left ok, Option.map_some, hb, eqn, hv, show Setup.parent A t dest = U.post.host p.1 from pl.owner_parent ..]

include pl in
theorem Placed.moves {x y : Wire} {Z : Border F U.T x y U.x U.y} {s : (Out).format.obj}
    {r : T.format.obj} (q : T.Encloses r U.G Z) (p : (Out).Encodes s (U.graph R fit))
    (h : q.core.post.host = U.post.host) (h' : p.post.host = L.host) :
    (relocation T M L).Moves q p (resetSlot T U q.slot) where
  positive := resetSlot_pos T U q.slot q.positive
  iff := by
    rintro ⟨v, j, s⟩ i
    rw [q.frozen, q.core.block, p.block, h, h']
    exact pl.back T M q.slot i v j s

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # Active and vacant output records of a reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring BatchDescent.Trail
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {A : Template F} {u a Δ D Y w : ℕ} {B' c : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup A.scheme A.scheme.h u a Δ D Y w B'} {R : Rotor F Y w}
  {fit : U.Fits R c} {fit' : V.Fits R c} {e cap mx dx : ℕ} {b : Book A.scheme u e cap}
  (M : Template.Meter) (L : U.Layout R fit b mx dx) (g : (Child.Graph mx dx).obj)
  (parent : B mx → B A.scheme.m)
local notation "E" => (A.resetTarget b M mx dx a)

def emitted : (Tile.whole A E).obj := (printed M L g, (L.move parent).commands)

def vacant : (Tile.output A E).obj :=
  (((Post.record dx e b.d (.addr cap)).serial Post.vacant, 0), fun _ _ => point A.scheme none)

theorem emitted_vacant {v : B mx} (hv : v ∉ Set.range L.host) (i : B a) :
    Tile.part A E (emitted M L g parent) v i = vacant M := by
  have he : (v, i, 0) ∉ Set.range L.vertex := by
    rintro ⟨t, ht⟩
    exact hv ⟨t.2, congrArg Prod.fst ht⟩
  have hp (j : B 0) (t : B e) : ((v, i, j), t) ∉ Set.range L.span := by
    rintro ⟨x, hx⟩
    exact hv ⟨(whereAt _ _ x).2, congrArg (fun p => p.1.1) hx⟩
  apply Prod.ext
  · apply Prod.ext
    · exact congrArg (Post.record dx e b.d (.addr cap)).serial
        (L.record_vacant (b.size _ _) (b.data L) _ he)
    · change counters M L v i = 0
      unfold counters
      exact Function.extend_apply' _ _ _ hv
  · funext j t
    exact congrArg (point A.scheme) (L.read_idle parent _ (hp j t))

theorem emitted_at (blk : L.block = (cellIndex a).toEmbedding) (v : U.At R fit) :
    Tile.part A E (emitted M L g parent) (L.host v.2) (L.block v.1) =
      (((b.output L g.1 (L.host v.2)).2 (L.block v.1), M.read (U.graph R fit) v.swap),
        localPointers L parent v) := by
  refine Prod.ext (Prod.ext rfl ?_) rfl
  change (E).counter (printed M L g) (L.host v.2) (L.block v.1) = _
  rw [blk]
  exact counter_at M L g v.2 v.1

variable (L' : V.Layout R fit' b mx dx) (g' : (Child.Graph mx dx).obj)

theorem volume_eq (H : b.Ready L g.1) (H' : b.Ready L' g'.1)
    (v : U.At R fit) (z : V.At R fit')
    (eq : (b.output L g.1 (L.host v.2)).2 (L.block v.1) = (b.output L' g'.1 (L'.host z.2)).2 (L'.block z.1)) :
    (U.graph R fit).tetherLoad v.swap + degree (U.graph R fit).pair v.swap * u =
      (V.graph R fit').tetherLoad z.swap + degree (V.graph R fit').pair z.swap * u := by
  have he : H.posting.atBlock v.swap = H'.posting.atBlock z.swap := congrArg (b.scheme mx dx a).decode eq
  exact congrArg₂ (·+·)
    ((H.posting.exterior_volume v.swap).symm.trans
      ((congrArg (fun r => r.volume false) he).trans (H'.posting.exterior_volume z.swap)))
    ((H.posting.internal_volume v.swap).symm.trans
      ((congrArg (fun r => r.volume true) he).trans (H'.posting.internal_volume z.swap)))

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # The attachment query issued by a reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup

open Packing Coloring
open scoped Classical
variable {F : Type} [Field F] [Fintype F] {A : Template F} {u a Δ D Y w : ℕ} {W c : ℝ}
  [NeZero Y] [NeZero w] (T : Attachment A) {U : Setup A.scheme A.scheme.h u a Δ D Y w W}
  {R : Rotor F Y w} {fit : U.Fits R c} {e cap t d : ℕ} {b : Book A.scheme u e cap}
  (M : Template.Meter) (L : U.Layout R fit b (A.scheme.m + t) d)
  (g : (Child.Graph (A.scheme.m + t) d).obj) (old : T.format.obj)

local notation "Out" => A.resetTarget b M (A.scheme.m + t) d a

def query : Attachment.Query T Out (A.scheme.h - a + T.k) 0 where
  R := relocation T M L
  M := L.move (parent A t)
  old := old
  fresh := printed M L g
  active j _ := decide (j ∈ Set.range L.host)

theorem query_active (p : (Out).Encodes (printed M L g) (U.graph R fit))
    (hp : p.post.host = L.host) : Attachment.Relocation.WriteActive p (query T M L g old).active := by
  intro i j
  change decide (i ∈ Set.range L.host) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨v, rfl⟩
    let q : (U.graph R fit).diagram.V := ((cellIndex a).symm j, v)
    refine ⟨q, ?_⟩
    rw [p.post.vertex_eq, hp, p.block]
    change (L.host v, cellIndex a ((cellIndex a).symm j), _) = _
    rw [Equiv.apply_symm_apply]
  · rintro ⟨q, hq⟩
    rw [p.post.vertex_eq, hp] at hq
    exact ⟨_, congrArg Prod.fst hq⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# Relative neighbor addresses of a reset host

Each occupied column names the adjacent host by a parent hop and
a hardware suffix. Unused columns return to the current host.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Coloring Packing Finset
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {u h a Δ D Y w : ℕ} {W cost : ℝ}
  [NeZero Y] [NeZero w] (U : Setup S h u a Δ D Y w W) (R : Rotor F Y w)
  (fit : U.Fits R cost) (full : Bool)
local notation "t" => (Child.extra R Δ (h - a))
local notation "d" => (Child.width D Y full)
local notation "V" => HostNet.V (U.graph R fit)
local notation "col" => (Child.Suffix S.d t d)
local notation "adj" => (U.neighbors R fit full)
local notation "code" => (Child.code R Δ (h - a))
local notation "split" => (U.parts R fit)
local notation "hop" => (BatchDescent.Trail.hop S.d)
local notation "idx" => (U.index R fit full)

def vacantSuffix (z : B t) : (col).obj := ((false, false), fun _ => ((false, false), hop none, z))

def liveSuffix (v : V) : (col).obj :=
  ((true, decide ((U.graph R fit).frozen v)), fun j =>
    if hj : ∃ x ∈ adj v, idx v x = j then
      let x := hj.choose
      ((true, decide (x ∈ (U.graph R fit).C v)), hop (U.chart.label (split v).1 (split x).1), code (split x).2)
    else ((false, false), hop none, code (split v).2))

def desc : B (S.m + t) → (col).obj :=
  Function.extend (U.host R fit) (U.liveSuffix R fit full)
    (fun i => vacantSuffix (S := S) (D := D) R full (Match.rowIndex _ _ i).2)

theorem desc_live (v : V) : U.desc R fit full (U.host R fit v) = U.liveSuffix R fit full v :=
  (U.host R fit).injective.extend_apply _ _ v

theorem desc_vacant (i : B (S.m + t)) (hi : i ∉ Set.range (U.host R fit)) :
    U.desc R fit full i = vacantSuffix (S := S) (D := D) R full (Match.rowIndex _ _ i).2 :=
  Function.extend_apply' _ _ _ hi

theorem suffix_used (P : U.Reading full) (v z : V) (he : z ∈ adj v) :
    (U.liveSuffix R fit full v).2 (idx v z) =
      ((true, decide (z ∈ (U.graph R fit).C v)), hop (U.chart.label (split v).1 (split z).1), code (split z).2) := by
  have h : ∃ x ∈ adj v, idx v x = idx v z := ⟨z, he, rfl⟩
  have eq : h.choose = z := U.index_inj R fit full P v
    (mem_insert_of_mem h.choose_spec.1) (mem_insert_of_mem he) h.choose_spec.2
  simp only [liveSuffix, dite_eq_left h, eq]

theorem suffix_spare (v : V) (j : B d) (he : ∀ z ∈ adj v, idx v z ≠ j) :
    (U.liveSuffix R fit full v).2 j = ((false, false), hop none, code (split v).2) := by
  have hn : ¬∃ x ∈ adj v, idx v x = j := by rintro ⟨x, hx, hh⟩; exact he x hx hh
  simp only [liveSuffix, dite_eq_right hn]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # The emitted child header describes the reset graph exactly -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring Finset
open scoped Classical

variable {F : Type} [Field F] {A : Template F} {u a Δ D Y w k : ℕ} {W cost : ℝ}
  [NeZero Y] [NeZero w] (U : Setup A.scheme A.scheme.h u a Δ D Y w W)
  (R : Rotor F Y w) (fit : U.Fits R cost) (b : Board A U k)

local notation "t" => (Child.extra R Δ (A.scheme.h - a))
local notation "d" => (Child.width D Y A.full)
local notation "host" => (U.host R fit)
local notation "parts" => (U.parts R fit)

local notation "idx" => (U.index R fit A.full)
local notation "profile" => (U.desc R fit A.full)

theorem describes : Child.Describes A.full (U.graph R fit) host idx
      (Child.build _ _ _ _ (A.nav b.tape.1, profile)) := by
  let src : (Child.Input A.scheme.m A.scheme.d t d).obj := (A.nav b.tape.1, profile)
  apply Child.describes_of_columns
  · intro i
    change (profile i).1.1 = true ↔ _
    by_cases hi : i ∈ Set.range host
    · obtain ⟨j, rfl⟩ := hi
      rw [desc_live]
      exact ⟨fun _ => ⟨j, rfl⟩, fun _ => rfl⟩
    · rw [desc_vacant _ _ _ _ _ hi]
      exact ⟨fun e => Bool.noConfusion e, fun he => (hi he).elim⟩
  · intro i
    change (profile (host i)).1.2 = true ↔ _
    rw [desc_live]
    exact decide_eq_true_iff
  · intro i hi j
    apply Child.build_stay src i j
    change ((profile i).2 j).2 = _
    rw [desc_vacant _ _ _ _ _ hi]
    rfl
  · intro i j he
    have hd := U.suffix_used R fit A.full b.read i j he
    rw [← desc_live] at hd
    refine ⟨?_, congrArg Prod.fst hd⟩
    have hx := Child.build_hop src (host i) (idx i j) _ _ (congrArg Prod.snd hd)
    rw [host_parts] at hx
    have hn := b.parent_hop _ _ (U.parent_mem R fit A.full he)
    refine hx.trans ?_
    change (Match.rowIndex _ t).symm ((U.chart.label (parts i).1 (parts j).1).elim _ (A.nav b.tape.1 _), _) = _
    rw [hn]
    rfl
  · intro i j he
    have hd := U.suffix_spare R fit A.full i j he
    rw [← desc_live] at hd
    refine ⟨Child.build_stay src (host i) j ?_, congrArg Prod.fst hd⟩
    rw [host_parts]
    exact congrArg Prod.snd hd

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # Matching the relative addresses in two reset headers -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup.Preview
open Coloring Packing Finset
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {u h a Δ D Y w : ℕ} {W cost : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup S h u a Δ D Y w W} {full : Bool} {n k : ℕ}
  {P : U.Reading full} {Q : V.Reading full} {T : Relation U V}
  (p : Preview P Q T n) (R : Rotor F Y w) (fu : U.Fits R cost) (fv : V.Fits R cost)
  {x x' : (U.graph R fu).V} {y y' : (V.graph R fv).V} (hk : k + 4 ≤ n)
  (hr : T k (U.parts R fu x).1 (V.parts R fv y).1)
  (he : (U.parts R fu x).2 = (V.parts R fv y).2)

include p hk hr he
private theorem used_eq (i : B (Child.width D Y full))
    (hx : ∃ v ∈ U.neighbors R fu full x, U.index R fu full x v = i) :
    (U.liveSuffix R fu full x).2 i = (V.liveSuffix R fv full y).2 i := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨z, hz, ht, hv'⟩ := p.adjacent R fu fv full id hk hr he hv
  have hw := p.widen (by omega : k + 1 ≤ n) ht
  have hi := p.idx_match R fu fv hk hr he hw hv'
  have hc : v ∈ (U.graph R fu).C x ↔ z ∈ (V.graph R fv).C y :=
    p.neighbors_iff R fu fv hk hr he hw hv' false (by simp)
  rw [U.suffix_used R fu full P x v hv, hi, V.suffix_used R fv full Q y z hz]
  simp only [hc, p.labels (by omega : k < n) hr hw, hv']

theorem suffix_eq (hf : (U.graph R fu).frozen x ↔ (V.graph R fv).frozen y) :
    U.liveSuffix R fu full x = V.liveSuffix R fv full y := by
  apply Prod.ext
  · simp only [liveSuffix, hf]
  funext i
  by_cases hx : ∃ v ∈ U.neighbors R fu full x, U.index R fu full x v = i
  · exact p.used_eq R fu fv hk hr he i hx
  by_cases hy : ∃ v ∈ V.neighbors R fv full y, V.index R fv full y v = i
  · exact (p.symm.used_eq R fv fu hk hr he.symm i hy).symm
  push Not at hx hy
  rw [U.suffix_spare R fu full x i hx, V.suffix_spare R fv full y i hy, he]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup.Preview
end

/-! # Equal samples determine the same local reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Board
open Coloring Packing
open scoped Classical
variable {F : Type} [Field F] {A : Template F} {u a Δ D Y w k n : ℕ} {W : ℝ}
  {U V : Setup A.scheme A.scheme.h u a Δ D Y w W}
  (b : Board A U k) (c : Board A V k) (v : U.G.V) (z : V.G.V) (σ : Cell a)

def path : U.Relation V := fun n i j =>
  ∃ p : List (B A.scheme.d), p.length ≤ n ∧ node v p = i ∧ node z p = j

theorem start : path v z 0 v z := ⟨[], le_rfl, rfl, rfl⟩

structure Sample (n : ℕ) : Prop where
  mixer : b.tape.2.1 = c.tape.2.1
  mask : Tile.mask A n b.tape.1 (U.post.host v) = Tile.mask A n c.tape.1 (V.post.host z)
  rows : (Window.reads n (Tile.packet A a k U.groups b.tape) (U.post.host v)).2 (cellIndex a σ) =
    (Window.reads n (Tile.packet A a k V.groups c.tape) (V.post.host z)).2 (cellIndex a σ)

variable {b c v z σ}

theorem sample {t : ℕ} (i j : B t)
    (he : Tile.look A a k U.groups n t b.tape ((Match.rowIndex _ t).symm (U.post.host v, i)) (cellIndex a σ) =
      Tile.look A a k V.groups n t c.tape ((Match.rowIndex _ t).symm (V.post.host z, j)) (cellIndex a σ)) :
    Sample b c v z σ n := by
  simp only [Tile.look, Equiv.apply_symm_apply, Prod.mk.injEq] at he
  exact ⟨he.2.1.1, he.2.2.1, he.2.2.2⟩

namespace Sample
variable (e : Sample b c v z σ n) {i i' : U.G.V} {j j' : V.G.V}
include e

theorem mix : U.Z.π = V.Z.π := by rw [b.mix, c.mix, e.mixer]

theorem same (h : path v z n i j) (h' : path v z n i' j') : i = i' ↔ j = j' := by
  obtain ⟨p, hp, rfl, rfl⟩ := h
  obtain ⟨q, hq, rfl, rfl⟩ := h'
  obtain ⟨r, hr⟩ := Assembly.Child.visit_slot p hp
  obtain ⟨s, hs⟩ := Assembly.Child.visit_slot q hq
  have eq := congrFun (congrFun e.mask r) s
  simp only [Tile.mask, hr, hs, ← b.at_node, ← c.at_node, U.post.host.injective.eq_iff,
    V.post.host.injective.eq_iff, decide_eq_decide] at eq
  exact eq

theorem row (h : path v z n i j) : b.localRow i σ = c.localRow j σ := by
  obtain ⟨p, hp, rfl, rfl⟩ := h
  obtain ⟨r, hr⟩ := Assembly.Child.visit_slot p hp
  have eq := congrFun e.rows r
  change ((Tile.packet A a k U.groups b.tape) (Neighborhood.walks n (A.nav b.tape.1) _ r)).2 _ =
    ((Tile.packet A a k V.groups c.tape) (Neighborhood.walks n (A.nav c.tape.1) _ r)).2 _ at eq
  rw [hr, hr, ← b.at_node, ← c.at_node] at eq
  exact eq

theorem record (h : path v z n i j) (x : Cell A.scheme.h) (hx : U.Z.group x = σ) :
    U.tag i x = V.tag j x ∧ A.counter b.tape.1 (U.post.host i) (cellIndex _ x) =
      A.counter c.tape.1 (V.post.host j) (cellIndex _ x) := by
  let r := cellIndex _ (splitCell a U.groups (U.Z.π x)).2
  have hp : Mixing.original A.scheme.h a U.groups b.tape.2.1 (cellIndex a σ) r = x :=
    hx ▸ b.original x
  have hq : Mixing.original A.scheme.h a V.groups c.tape.2.1 (cellIndex a σ) r = x := by
    rw [← e.mixer]; exact hp
  have he := congrFun (congrArg (fun w => w.2.2) (e.row h)) r
  simp only [localRow, Tile.packet, hp, hq, Prod.mk.injEq] at he
  rw [b.tag, c.tag]
  exact he

theorem look : Setup.Look b.read c.read σ (path v z) n := by
  refine ⟨?_, e.same, ?_, b.margin.trans c.margin.symm, e.mix, ?_, ?_, ?_, ?_, ?_⟩
  · rintro l m i j hm ⟨p, hp, rfl, rfl⟩
    exact ⟨p, hp.trans hm, rfl, rfl⟩
  · rintro l i j ⟨p, hp, rfl, rfl⟩ q
    exact ⟨q::p, Nat.succ_le_succ hp, rfl, rfl⟩
  · intro i j h
    rw [b.flags, c.flags]
    exact congrArg (fun w => w.2.1) (e.row h)
  · intro i j h; funext s
    rw [b.counts, c.counts]
    exact congrArg (fun w => (w.1.2 s).val) (e.row h)
  · intro i j h
    rw [b.depth, c.depth]
    exact congrArg (fun w => w.1.1.val) (e.row h)
  · exact fun h x hx => (e.record h x hx).1
  · intro i j h x hx
    rw [b.load, c.load, (e.record h x hx).2]

end Sample
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Board
end

/-! # Deciding occupancy and the relative address of a child -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Board
open Packing Coloring Setup
open scoped Classical
variable {F : Type} [Field F] [Fintype F] {A : Template F} {u a Δ D Y w k n : ℕ} {W cost : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup A.scheme A.scheme.h u a Δ D Y w W}
  {b : Board A U k} {c : Board A V k}
  {R : Rotor F Y w} {fit : U.Fits R cost} {fit' : V.Fits R cost}
  {e cap t d : ℕ} {B' : Book A.scheme u e cap}
  {L : U.Layout R fit B' (A.scheme.m + t) d} {L' : V.Layout R fit' B' (A.scheme.m + t) d}
  {locate : Coord R A.scheme.h a Δ ↪ B t}

theorem matched (hL : Placed A L locate) (hL' : Placed A L' locate)
    {v z : B (A.scheme.m + t)} {i j : B a}
    (he : Tile.look A a k U.groups n t b.tape v i = Tile.look A a k V.groups n t c.tape z j) :
    (v ∉ Set.range L.host ∧ z ∉ Set.range L'.host) ∨
    ∃ σ s q loc, i = cellIndex _ σ ∧ j = cellIndex _ σ ∧
      v = L.host (U.station R fit σ s loc).2 ∧ z = L'.host (V.station R fit' σ q loc).2 ∧
      Sample b c s q σ n := by
  obtain ⟨⟨v, r⟩, rfl⟩ := (Match.rowIndex A.scheme.m t).symm.surjective v
  obtain ⟨⟨z, r'⟩, rfl⟩ := (Match.rowIndex A.scheme.m t).symm.surjective z
  have h := he
  simp only [Tile.look, Equiv.apply_symm_apply, Prod.mk.injEq] at h
  obtain ⟨⟨live, rfl⟩, ⟨_, rfl⟩, _⟩ := h
  have eqv : v ∈ Set.range U.post.host ↔ z ∈ Set.range V.post.host := by rw [← b.live, ← c.live, live]
  by_cases hv : v ∈ Set.range U.post.host ∧ r ∈ Set.range locate
  · obtain ⟨q, rfl⟩ := eqv.mp hv.1
    obtain ⟨⟨s, rfl⟩, ⟨loc, rfl⟩⟩ := hv
    obtain ⟨σ, rfl⟩ := (cellIndex a).surjective i
    exact .inr ⟨σ, s, q, loc, rfl, rfl, (hL.host ..).symm, (hL'.host ..).symm, sample _ _ he⟩
  · left
    rw [hL.live, hL'.live, ← eqv]
    exact ⟨hv, hv⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Board
end

/-! # The frozen-seat pointers depend only on the local sample -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Setup Coloring Packing
open scoped Classical
variable {F : Type} [Field F] [Fintype F] {A : Template F} {u a Δ D Y w k n : ℕ} {W cost : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup A.scheme A.scheme.h u a Δ D Y w W}
  {b : Board A U k} {c : Board A V k}
  {R : Rotor F Y w} {fit : U.Fits R cost} {fit' : V.Fits R cost}
  {e cap t d : ℕ} {B' : Book A.scheme u e cap}
  {L : U.Layout R fit B' (A.scheme.m + t) d} {L' : V.Layout R fit' B' (A.scheme.m + t) d}
  {locate : Coord R A.scheme.h a Δ ↪ B t}

private theorem hosts_at (σ : Cell a) (v : U.G.V) (loc : Coord R A.scheme.h a Δ)
    (x : Cell A.scheme.h) (hx : U.Z.group x = σ) :
    hosts L (L.host (U.station R fit σ v loc).2) x ↔
      (U.result R fit).owner (v, x) = U.station R fit σ v loc := by
  constructor
  · rintro ⟨w, hw⟩
    have he := L.host.injective hw
    have hv := congrArg (U.result R fit).origin he
    rw [(U.result R fit).origin_owner, station_owner] at hv
    change w = v at hv
    subst w
    exact Prod.ext hx he
  · exact fun h => ⟨v, congrArg (fun p => L.host p.2) h⟩

private theorem no_host {v : B (A.scheme.m + t)} (hv : v ∉ Set.range L.host) (x : Cell A.scheme.h) :
    ¬ hosts L v x := fun ⟨_, h⟩ => hv ⟨_, h⟩

variable (T : Attachment A) (M : Template.Meter) (hL : Placed A L locate) (hL' : Placed A L' locate)
  (hn : A.scheme.h - a + 2 < n) (hD : 0 < D) (delayed : A.full = false → A.scheme.h - a ≤ 32 * Nat.clog 2 (2 * D))
  {v z : B (A.scheme.m + t)} {i j : B a}
  (he : Tile.look A a k U.groups n t b.tape v i = Tile.look A a k V.groups n t c.tape z j)

include hL hL' hn hD delayed he in
theorem Board.relocate_eq :
    (relocation T M L).prev v i = (relocation T M L').prev z j := by
  rcases Board.matched hL hL' he with ⟨hv, hz⟩ | ⟨σ, s, q, loc, rfl, rfl, rfl, rfl, e⟩
  · funext k
    simp only [relocation, no_host hv, no_host hz, ite_false]
  · have ha := (e.look.region hn hD delayed).toSurvey.agree (k := 0) (by omega) (Board.start s q)
    have hx (y : B (A.scheme.h - a)) : U.recover (cellIndex a σ) y = V.recover (cellIndex a σ) y := by
      unfold recover
      rw [e.mix]
    funext k
    let y := (Match.rowIndex (A.scheme.h - a) T.k k).1
    let x := U.recover (cellIndex a σ) y
    have hu : U.Z.group x = σ :=
      (cellIndex a).injective ((U.recover_eq (cellIndex a σ) y x).mp rfl).1.symm
    have hv : V.Z.group x = σ := (ha.group x).symm.trans hu
    have eqn : hosts L (L.host (U.station R fit σ s loc).2) x ↔
        hosts L' (L'.host (V.station R fit' σ q loc).2) x := by
      rw [hosts_at _ _ _ _ hu, hosts_at _ _ _ _ hv]
      exact ⟨fun h => ha.owner_here h, fun h => ha.symm.owner_here h⟩
    simp only [relocation, ← hx]
    exact if_congr eqn rfl rfl

include hL hL' hn hD delayed he in
theorem Board.query_eq {g g' : (Child.Graph (A.scheme.m + t) d).obj} (old old' : T.format.obj)
    (hm : Tile.part A (A.resetTarget B' M _ d a) (emitted M L g (parent A t)) v i =
      Tile.part A (A.resetTarget B' M _ d a) (emitted M L' g' (parent A t)) z j) :
    ((query T M L g old).ticketAt v i).2 = ((query T M L' g' old').ticketAt z j).2 := by
  have hl : v ∈ Set.range L.host ↔ z ∈ Set.range L'.host := by
    rcases Board.matched hL hL' he with ⟨hv, hz⟩ | ⟨σ, s, q, loc, _, _, rfl, rfl, _⟩
    · exact iff_of_false hv hz
    · exact iff_of_true ⟨_, rfl⟩ ⟨_, rfl⟩
  have hprev := Board.relocate_eq T M hL hL' hn hD delayed he
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact decide_eq_decide.mpr hl
  · exact congrFun (congrArg Prod.snd hm) 0
  · exact funext fun k => congrArg T.tag (congrFun hprev k)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # Local determination of the charge and history carried through a reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
open Packing
open scoped Classical

variable {F : Type} [Field F] {u a Δ D Y w : ℕ} {W cost : ℝ} [NeZero Y] [NeZero w]

namespace Setup

variable {S : Scheme F} {h : ℕ} {U V : Setup S h u a Δ D Y w W} {R : Rotor F Y w}
  {fit : U.Fits R cost} {fit' : V.Fits R cost} {v : U.G.V} {z : V.G.V}
  {σ : Cell a} {loc : Coord R h a Δ}

private theorem local_sum (x : U.G.V × Cell h → ℝ) :
    push (Prod.swap ∘ (U.result R fit).owner) x (U.station R fit σ v loc).swap =
      ∑ j, if (U.result R fit).owner (v, j) = U.station R fit σ v loc then x (v, j) else 0 := by
  unfold push
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single v]
  · simp
  · intro t ht
    refine Finset.sum_eq_zero fun j _ => ite_eq_right ?_
    intro he
    exact ht (owner_here (Prod.swap_injective he)).2

private theorem Agree.push_eq (g : Agree U V σ v z) (x : U.G.V × Cell h → ℝ)
    (y : V.G.V × Cell h → ℝ) (eq : ∀ j, U.Z.group j = σ → x (v, j) = y (z, j)) :
    push (Prod.swap ∘ (U.result R fit).owner) x (U.station R fit σ v loc).swap =
      push (Prod.swap ∘ (V.result R fit').owner) y (V.station R fit' σ z loc).swap := by
  rw [local_sum, local_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (U.result R fit).owner (v, j) = U.station R fit σ v loc
  · rw [ite_eq_left hj, ite_eq_left (g.owner_here hj)]
    exact eq j (Setup.owner_here hj).1
  · exact (ite_eq_right hj).trans (ite_eq_right (fun h => hj (g.symm.owner_here h))).symm

private theorem after_past :
    ((U.graph R fit).past (U.station R fit σ v loc).swap : ℝ) =
      push (Prod.swap ∘ (U.result R fit).owner)
        (fun x => (U.G.past x + degree U.G.pair x * u : ℕ)) (U.station R fit σ v loc).swap := by
  change (U.G.carried _ _ : ℝ) = _
  simp only [HostNet.carried, push, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]

private theorem after_park :
    push (U.graph R fit).park U.L.charge (U.station R fit σ v loc).swap =
      push (Prod.swap ∘ (U.result R fit).owner) (push U.G.park U.L.charge) (U.station R fit σ v loc).swap :=
  (push_comp U.G.park (Prod.swap ∘ (U.result R fit).owner) U.L.charge _).symm

end Setup

namespace Board

variable {A : Template F} {U V : Setup A.scheme A.scheme.h u a Δ D Y w W}
  {k n : ℕ} {b : Board A U k} {c : Board A V k} {v : U.G.V} {z : V.G.V} {σ : Cell a}

/-- Equal records give the same past, parked charge and internal volume.
Once the new arities match, all three arguments of the meter agree. -/
theorem Sample.meter (e : Sample b c v z σ n) (hn : A.scheme.h - a + 8 ≤ n)
    (hD : 0 < D) (delayed : A.full = false → A.scheme.h - a ≤ 32 * Nat.clog 2 (2 * D))
    (M : Template.Meter) (R : Rotor F Y w) (fit : U.Fits R cost) (fit' : V.Fits R cost)
    (loc : Setup.Coord R A.scheme.h a Δ)
    (har : let p := (U.station R fit σ v loc).swap
           let q := (V.station R fit' σ z loc).swap
           (U.graph R fit).tetherLoad p + degree (U.graph R fit).pair p * u =
             (V.graph R fit').tetherLoad q + degree (V.graph R fit').pair q * u) :
    M.read (U.graph R fit) (U.station R fit σ v loc).swap =
      M.read (V.graph R fit') (V.station R fit' σ z loc).swap := by
  have region := e.look.region (show A.scheme.h - a + 2 < n by omega) hD delayed
  have g := region.toSurvey.agree (by omega) (start v z)
  have records := e.record (e.look.widen (Nat.zero_le n) (start v z))
  unfold Template.Meter.read
  dsimp only at har
  rw [har]
  refine congrArg₂ (M.encode _) ?_ ?_
  · rw [Setup.after_park, Setup.after_park]
    apply g.push_eq
    intro j hj
    rw [b.park, c.park, (records j hj).2]
  · apply Nat.cast_injective (R := ℝ)
    rw [Setup.after_past, Setup.after_past]
    apply g.push_eq
    intro j hj
    have hc := records j hj
    have htag : U.post.atBlock (v, j) = V.post.atBlock (z, j) := congrArg A.scheme.decode hc.1
    simp only [← U.post.internal_volume, ← V.post.internal_volume, htag, b.past, c.past, hc.2]

end Board
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # The full record at an occupied child is locally determined -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Board
open Packing Coloring Setup
open scoped Classical
variable {F : Type} [Field F] [Fintype F] {A : Template F} {u a Δ D Y w k n : ℕ} {W cost : ℝ}
  [NeZero Y] [NeZero w] {U V : Setup A.scheme A.scheme.h u a Δ D Y w W}
  {b : Board A U k} {c : Board A V k} {v : U.G.V} {z : V.G.V} {σ : Cell a}
  (p : Sample b c v z σ n) (hn : A.scheme.h - a + 8 ≤ n)
  (hD : 0 < D) (delayed : A.full = false → A.scheme.h - a ≤ 32 * Nat.clog 2 (2 * D))
  {R : Rotor F Y w} {fit : U.Fits R cost} {fit' : V.Fits R cost}
  {e cap m d : ℕ} {B' : Book A.scheme u e cap}
  {L : U.Layout R fit B' m d} {L' : V.Layout R fit' B' m d}
  (ha : Ranked L) (hb : Ranked L') (hi : IndexAgrees L L' (path v z) σ v z)
include p hn hD delayed ha hb hi

theorem Sample.corresponds : Corresponds L L' (path v z) σ v z (n - 1) := by
  refine ⟨p.look.region (by omega) hD delayed, by omega, start _ _, ?_, ?_, ha, hb, hi⟩
  · exact fun _ _ hr => p.look.tag (p.look.widen (by omega) hr)
  · ext x
    rw [b.block, c.block]

variable (hu : ∀ t, U.G.diagram.arity t = 0 → ∀ x, Transcript.sample (U.G.diagram.table t) x = 1)
  (hv : ∀ t, V.G.diagram.arity t = 0 → ∀ x, Transcript.sample (V.G.diagram.table t) x = 1)
  (loc : Coord R A.scheme.h a Δ)
local notation "x" => U.station R fit σ v loc
local notation "y" => V.station R fit' σ z loc
include hu hv

theorem Sample.payload : B'.data L x = B'.data L' y := by
  have h := p.corresponds hn hD delayed ha hb hi
  apply congrArg (canonical B'.ord u cap)
  funext w
  exact h.region.eval (k := 0) (by omega) h.root h.at_root hu hv (L.seat x) (L'.seat y) w w
    (fun i j he t => congrArg (fun s => w s t) (h.seat he))

variable (M : Template.Meter) {g g' : (Child.Graph m d).obj}
  (hs : B'.Ready L g.1) (ht : B'.Ready L' g'.1)
  (blk : L.block = (cellIndex a).toEmbedding) (blk' : L'.block = (cellIndex a).toEmbedding)
  (parent : B m → B A.scheme.m)
local notation "E" => A.resetTarget B' M m d a
include hs ht blk blk'

theorem Sample.cell :
    Tile.part A E (emitted M L g parent) (L.host (x).2) (cellIndex a σ) =
      Tile.part A E (emitted M L' g' parent) (L'.host (y).2) (cellIndex a σ) := by
  have h := p.corresponds hn hD delayed ha hb hi
  have payload := p.payload hn hD delayed ha hb hi hu hv loc
  have tag := h.tag loc g.1 g'.1 payload
  have arity := volume_eq L g L' g' hs ht x y tag
  have meter := p.meter hn hD delayed M R fit fit' loc arity
  have left := emitted_at M L g parent blk x
  have right := emitted_at M L' g' parent blk' y
  have he := left.trans ((Prod.ext (Prod.ext tag meter) (h.pointers parent loc)).trans right.symm)
  rw [blk, blk'] at he
  exact he

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Board
end
