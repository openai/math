import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Factor
import OAI.LinearAlgebra.MatrixExponent.Assembly.FreezeInput.Retain
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Frame

/-! # Uniqueness of the moved span corresponding to a given old span -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing BatchDescent
open scoped Classical

variable {F T : Type} [Field F] {x y a b : Wire} {D Y : Template F} {A : Attachment D} {k m : ℕ}
  {u v : ℕ} {L : Fringe x y T} {G : HostNet F L D.scheme.h u}
  {H : HostNet F L Y.scheme.h v} {Z : Border F T a b x y} {r : A.format.obj} {s : Y.format.obj}

namespace Scheme.Posting
variable {S : Scheme F} {w : S.format.obj} (p : S.Posting w G)

theorem end_zero (j : G.diagram.End) : (p.toSeating.ends j).1.1.2.2 = 0 := by
  obtain ⟨⟨v, i⟩, rfl⟩ := G.diagram.portEquiv.surjective j
  rw [p.toSeating.ends_at]
  exact congrArg (fun x => x.2.2) (p.vertex_eq v)

theorem boundary_zero (j : slots x ⊕ slots y) : (p.toPresentation.boundary j).val.1.1.2.2 = 0 := by
  cases j <;> exact p.end_zero _

end Scheme.Posting

namespace Attachment.Relocation.Moves
variable [Fintype T] {R : A.Relocation Y k} {q : A.Encloses r G Z} {p : Y.Encodes s H} {slot : T → B k}
  (h : R.Moves q p slot) {M : Trail.Move D.scheme Y.scheme m}
  (move : M.Agrees q.core.post.toPresentation p.post.toPresentation)

local notation "U" => A.transport Y k
local notation "Sp" => Scheme.Span (scheme U)
local notation "src" => q.core.post.toPresentation.boundary
local notation "dst" => p.post.toPresentation.boundary

include h move in
private theorem previous_cases {j : Sp} {w : A.scheme.Span} (he : R.previous r M j = some w) :
    (∃ i, j = (U).fromCore (dst i).val.1 ∧ w = A.fromCore (src i).val.1) ∨
    (∃ t l, j = (frozen p slot t, A.outer Y l) ∧ w = (q.pres.vertex (.inr t), l)) := by
  rcases j with ⟨⟨v, c, d⟩, z⟩
  by_cases hd : d = 0
  · subst d
    simp only [previous, ↓reduceIte] at he
    by_cases hz : z ∈ Set.range (A.inner Y)
    · obtain ⟨l, rfl⟩ := hz
      rw [(A.inner Y).injective.extend_apply] at he
      let x : Y.scheme.Span := ((v, c, 0), l)
      have hx : (M.read x).isSome := by
        by_contra! hn
        have he' : (M.previous x).map A.fromCore = some w := he
        cases hm : M.read x <;> simp [Trail.Move.previous, hm] at he' hn
      obtain ⟨i, hi⟩ := move.active _ hx
      change (M.previous x).map A.fromCore = some w at he
      rw [← hi, (move.mapped i).1] at he
      exact .inl ⟨i, congrArg (U).fromCore hi.symm, (Option.some.inj he).symm⟩
    · rw [Function.extend_apply' _ _ _ hz] at he
      cases he
  · simp only [previous, ite_eq_right hd] at he
    by_cases hz : z ∈ Set.range (A.outer Y)
    · obtain ⟨l, rfl⟩ := hz
      rw [(A.outer Y).injective.extend_apply] at he
      obtain ⟨i, hi, hw⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨t, rfl⟩ := R.active q _ _ hi
      exact .inr ⟨t, l, Prod.ext ((R.kept_iff q p slot h _ t).mp hi) rfl, hw.symm⟩
    · rw [Function.extend_apply' _ _ _ hz] at he
      cases he

private theorem separate (t : T) (l : B A.e) (x : D.scheme.Span) :
    (q.pres.vertex (.inr t), l) ≠ A.fromCore x := by
  rw [q.frozen]
  exact fun he => q.positive t (congrArg (fun y => y.1.2.2) he)

include h move in
theorem previous_inner (i : slots x ⊕ slots y) (j : Sp) :
    R.previous r M j = some (A.fromCore (src i).val.1) ↔ j = (U).fromCore (dst i).val.1 := by
  constructor
  · intro he
    rcases h.previous_cases move he with ⟨u, rfl, hu⟩ | ⟨t, l, _, ht⟩
    · have hs : (src i).val.1 = (src u).val.1 := by
        have h₁ := congrArg (fun t => t.1.1) hu
        have h₂ := congrArg (fun t => t.1.2.1) hu
        have h₃ := (q.core.post.boundary_zero i).trans (q.core.post.boundary_zero u).symm
        exact Prod.ext (Prod.ext h₁ (Prod.ext h₂ h₃)) (A.coreSpan.injective (congrArg Prod.snd hu))
      exact congrArg (U).fromCore (move.same hs).symm
    · exact (separate t l _ ht.symm).elim
  · rintro rfl
    rw [R.previous_core _ _ _ (p.post.boundary_zero i), (move.mapped i).1]
    rfl

include h move in
theorem previous_outer (t : T) (l : B A.e) (j : Sp) :
    R.previous r M j = some (q.pres.vertex (.inr t), l) ↔ j = (frozen p slot t, A.outer Y l) := by
  constructor
  · intro he
    rcases h.previous_cases move he with ⟨i, _, hi⟩ | ⟨w, z, rfl, eqw⟩
    · exact (separate t l _ hi).elim
    · obtain ⟨hv, rfl⟩ := Prod.mk.inj eqw
      rw [Sum.inr.inj (q.pres.vertex.injective hv)]
  · rintro rfl
    rw [R.previous_frozen r M (frozen p slot t) l (h.positive t), h.kept_at]
    rfl

end Attachment.Relocation.Moves
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # Reading the old peer through canonical neighboring stations -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring Packing BatchDescent
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y a b : Wire} {D Y : Template F} {A : Attachment D} {k m : ℕ}
  {u v : ℕ} {L : Fringe x y T} {G : HostNet F L D.scheme.h u}
  {H : HostNet F L Y.scheme.h v} {Z : Border F T a b x y} {r : A.format.obj} {s : Y.format.obj}
  {R : A.Relocation Y k} {q : A.Encloses r G Z} {p : Y.Encodes s H} {slot : T → B k}

namespace Relocation
variable {live : B Y.scheme.m → B Y.scheme.h → Bool} {M : Trail.Move D.scheme Y.scheme m}
local notation "U" => A.transport Y k
local notation "W" => scheme U
local notation "edges" => R.links r s M
local notation "out" => rows U (R.write r s live edges)

theorem peer_pin (j : (W).Pin out) :
    (W).peer out j.1 = (edges j.1).2.map (resolve s j.1.1) := by
  rw [peer_at, ite_eq_left (Nat.zero_lt_of_lt j.2.isLt)]

def Hops (s : Y.format.obj) (j l : (W).Span) : Prop := ∃ i, resolve s j.1 i = l

private theorem hops (full : Y.full = true) (c t : H.V × Cell Y.scheme.h) (ht : t.1 ∈ H.N c.1)
    (eq : c.2 = t.2) {j l : (W).Span}
    (hj : (j.1.1, j.1.2.1) = (p.post.host c.1, p.post.block c.2))
    (hl : (l.1.1, l.1.2.1) = (p.post.host t.1, p.post.block t.2)) : Hops s j l := by
  have hn : t.1 ∈ Y.adj H c.1 := by simpa only [Template.adj, full, ↓reduceIte] using ht
  obtain ⟨n, he, _⟩ := (p.edge _ _).mp hn
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj hj
  obtain ⟨h₃, h₄⟩ := Prod.mk.inj hl
  refine ⟨(n, l.1.2.2, l.2), ?_⟩
  simp only [resolve, h₁, h₂, eq, he, ← h₃, ← h₄, Prod.mk.eta]

namespace Moves
variable (h : R.Moves q p slot) (ok : WriteActive p live)
  (move : M.Agrees q.core.post.toPresentation p.post.toPresentation)

local notation "seated" => h.seating ok edges
local notation "new" => Scheme.Seating.ends seated
local notation "old" => q.pres.toSeating.ends

include move in
theorem old_outer (i : Border.Ends a b x y) (j : (W).Span) :
    R.previous r M j = some (old (Z.outerEnd G.diagram i)).1 ↔ j = (new (Z.outerEnd H.diagram i)).1 := by
  rw [(h.outer_end ok edges i).1]
  have hw := q.outer_end i
  conv_lhs => rhs; arg 1; rw [← Prod.mk.eta (p := (old (Z.outerEnd G.diagram i)).1), hw]
  exact h.previous_outer move _ _ _

include move in
theorem old_inner (i : slots x ⊕ slots y) (j : (W).Span) :
    R.previous r M j = some (old (Z.coreEnd G.diagram (boundaryEnd G.diagram i))).1 ↔
      j = (new (Z.coreEnd H.diagram (boundaryEnd H.diagram i))).1 := by
  rw [(q.core_end _).1, (h.core_end ok edges _).1]
  have hh := h.previous_inner move i j
  cases i <;> exact hh

theorem tether_hops (full : Y.full = true) (i : slots x ⊕ slots y) :
    let c := (new (Z.coreEnd H.diagram (boundaryEnd H.diagram i))).1
    let t := (new (Z.outerEnd H.diagram (Border.other i))).1
    Hops s c t ∧ Hops s t c := by
  intro c t
  let v := H.units.place (portEnd H.diagram i)
  let w := H.park (L.tensor i)
  have hv : (c.1.1, c.1.2.1) = (p.post.host v.1, p.post.block v.2) := by
    have ht (j : H.diagram.End) : (p.post.toSeating.ends j).1.1 = p.post.vertex (H.diagram.station j) := by
      obtain ⟨⟨u, z⟩, rfl⟩ := H.diagram.portEquiv.surjective j
      rw [p.post.toSeating.ends_at, H.diagram.station_port]
      rfl
    unfold c
    rw [(h.core_end ok edges _).1]
    simp only [fromCore, ht, station_boundary, p.post.vertex_eq]
    rfl
  have hw : (t.1.1, t.1.2.1) = (p.post.host w.1, p.post.block w.2) := by
    unfold t
    rw [(h.outer_end ok edges _).1, Z.owner_other, ← q.tether]
    rfl
  obtain ⟨_, he, hn⟩ := H.tether i
  exact ⟨hops full v w hn he hv hw, hops full w v (H.ns _ _ hn) he.symm hw hv⟩

end Moves
end Relocation
end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-! # Internal connections are read directly from the new core -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Relocation.Moves
open Coloring Packing BatchDescent
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y a b : Wire} {D Y : Template F} {A : Attachment D} {k m : ℕ}
  {u v : ℕ} {L : Fringe x y T} {G : HostNet F L D.scheme.h u}
  {H : HostNet F L Y.scheme.h v} {Z : Border F T a b x y} {r : A.format.obj} {s : Y.format.obj}
  {R : A.Relocation Y k} {q : A.Encloses r G Z} {p : Y.Encodes s H} {slot : T → B k}
  (h : R.Moves q p slot) {live : B Y.scheme.m → B Y.scheme.h → Bool}
  (ok : WriteActive p live) {M : Trail.Move D.scheme Y.scheme m}
  (move : M.Agrees q.core.post.toPresentation p.post.toPresentation)

local notation "U" => A.transport Y k
local notation "W" => scheme U
local notation "edges" => R.links r s M
local notation "out" => rows U (R.write r s live edges)
local notation "seated" => h.seating ok edges
local notation "new" => Scheme.Seating.ends seated
local notation "orig" => p.post.toSeating.ends

include move in
private theorem forward {i j : H.diagram.End}
    (hp : Y.scheme.Joins s.1 (orig i) (orig j)) :
    (W).Joins out (new (Z.coreEnd H.diagram i)) (new (Z.coreEnd H.diagram j)) ∧
      (W).direction out (new (Z.coreEnd H.diagram i)).1 = Y.scheme.direction s.1 (orig i).1 := by
  have hn : M.previous (orig i).1 = none := by
    cases he : M.read (orig i).1 with
    | none => rw [Trail.Move.previous, he]; rfl
    | some x =>
      obtain ⟨t, ht⟩ := move.active _ (show (M.read (orig i).1).isSome = true by rw [he]; rfl)
      have hh := (p.post.toPresentation.boundary t).property
      rw [ht, hp.1] at hh
      cases hh
  obtain ⟨hd, he⟩ := R.native r s M _ (p.post.end_zero i) hn
  have hi := h.core_end ok edges i
  have hj := h.core_end ok edges j
  refine ⟨⟨?_, hi.2.trans (hp.2.trans hj.2.symm)⟩, ?_⟩
  · rw [peer_pin, hi.1, hj.1, he, hp.1]
    rfl
  · rw [R.direction_at, hi.1]
    exact hd

include move in
theorem core_bond (j : H.diagram.E) :
    (seated).Bond (.inl (.inr (.inl j))) (.inr (.inr (.inl j))) := by
  have hp := p.post.internal j
  have a := h.forward ok move hp
  have b := h.forward ok move (hp.symm p.post.proper)
  have hd (t : Bool) : Y.scheme.direction s.1 (orig (cond t (.inr (.inr j)) (.inl (.inr j)))).1 = t := by
    obtain ⟨⟨i, l⟩, rfl⟩ := H.units.bits.symm.surjective j
    change Y.scheme.direction s.1 (orig (Scheme.endBit H i t l)).1 = t
    rw [(p.post.ordered i t l).1, p.post.dir]
  exact ⟨a.1, b.1, a.2.trans (hd false), b.2.trans (hd true)⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Relocation.Moves
end

/-!
# A compact code for transported attachment labels

The station mask determines where to read each old selector. Only
occupied frozen seats need space for selectors. The core selector,
station numbers, and link fields remain unchanged.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment

open Coloring Packing
open scoped Classical

variable {k N ℓ : ℕ}

private def seats (s : Finset (B k)) (h : s.card ≤ N) : s ↪ Fin N :=
  s.equivFin.toEmbedding.trans (Fin.castLEEmb h)

private def save (N : ℕ) (s : Finset (B k)) (f : B k → B ℓ) : Fin N → B ℓ :=
  if h : s.card ≤ N then Function.extend (seats s h) (fun i => f i.val) (fun _ => 0) else fun _ => 0

private def loadSeats (s : Finset (B k)) (f : Fin N → B ℓ) (i : B k) : B ℓ :=
  if h : s.card ≤ N ∧ i ∈ s then f (seats s h.1 ⟨i, h.2⟩) else 0

private theorem load_save (s : Finset (B k)) (f : B k → B ℓ) (h : s.card ≤ N)
    (hz : ∀ i ∉ s, f i = 0) (i : B k) : loadSeats s (save N s f) i = f i := by
  by_cases hi : i ∈ s
  · simp only [loadSeats, dite_eq_left (And.intro h hi), save, dite_eq_left h]
    exact (seats s h).injective.extend_apply _ _ _
  · simp [loadSeats, hi, hz i hi]

variable {F : Type} {D : Template F} (A : Attachment D) (Y : Template F) (k N : ℕ)

abbrev shortRecord :=
  Format.pair (.addr Y.scheme.ℓ) (.pair (Fmt.pi (fun _ : Fin N => Format.addr A.ℓ))
    (.vec k (.pair (.pair .bit (.addr A.k)) (.vec (A.spanBits Y) (A.contact Y k)))))

theorem short_width :
    (A.shortRecord Y k N).width = Y.scheme.ℓ + N * A.ℓ +
      2 ^ k * (1 + A.k + 2 ^ (A.spanBits Y) * (2 + Y.scheme.d + k + A.spanBits Y)) := by
  simp only [shortRecord, contact, endpoint, Format.width_pair, Format.width_addr,
    Format.width_vec, Fmt.width_pi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Format.width_bit]
  ring

private def storeRow (r : (A.record Y k).obj) : (A.shortRecord Y k N).obj :=
  (r.1, save N (occupiedSeats fun j => (r.2 j).1.1) (fun j => (r.2 j).1.2.1),
   fun j => (((r.2 j).1.1, (r.2 j).1.2.2), (r.2 j).2))

private def readRow (r : (A.shortRecord Y k N).obj) : (A.record Y k).obj :=
  (r.1, fun j => (((r.2.2 j).1.1, loadSeats (occupiedSeats fun j => (r.2.2 j).1.1) r.2.1 j,
    (r.2.2 j).1.2), (r.2.2 j).2))

def fitsRow (r : (A.record Y k).obj) : Prop :=
  let s := occupiedSeats fun j => (r.2 j).1.1
  s.card ≤ N ∧ ∀ j ∉ s, (r.2 j).1.2.1 = 0

private theorem read_store (r : (A.record Y k).obj) (h : A.fitsRow Y k N r) :
    A.readRow Y k N (A.storeRow Y k N r) = r := by
  refine Prod.ext rfl (funext fun j => Prod.ext (Prod.ext rfl (Prod.ext ?_ rfl)) rfl)
  exact load_save _ _ h.1 h.2 j

def writeShort :=
  (A.shortRecord Y k N).serial ∘ A.storeRow Y k N ∘ (A.record Y k).serial.symm

def readShort :=
  (A.record Y k).serial ∘ A.readRow Y k N ∘ (A.shortRecord Y k N).serial.symm

variable [Field F]

abbrev shrink : Attachment Y := (A.transport Y k).recode (A.shortRecord Y k N).width (A.readShort Y k N)

def shorten (r : (A.transport Y k).format.obj) : (A.shrink Y k N).format.obj :=
  (r.1, fun i j => A.writeShort Y k N (r.2 i j))

def Sparse (r : (A.transport Y k).format.obj) : Prop :=
  ∀ i j, A.fitsRow Y k N ((A.record Y k).serial.symm (r.2 i j))

variable {A Y k N} {r : (A.transport Y k).format.obj}

theorem Sparse.restore (h : A.Sparse Y k N r) :
    r.2 = fun i j => A.readShort Y k N ((A.shorten Y k N r).2 i j) := by
  funext i j
  simp only [shorten, readShort, writeShort, Function.comp_apply, Equiv.symm_apply_apply,
    read_store _ _ _ _ _ (h i j), Equiv.apply_symm_apply]

variable {T : Type} [Fintype T] {x y a b : Wire} {u : ℕ} {L : Fringe x y T}
  {G : HostNet F L Y.scheme.h u} {Z : Border F T a b x y}

def Encloses.shrink (q : (A.transport Y k).Encloses r G Z) (h : A.Sparse Y k N r) :
    (A.shrink Y k N).Encloses (A.shorten Y k N r) G Z := q.recode h.restore

@[simp] theorem Encloses.shrink_core (q : (A.transport Y k).Encloses r G Z) (h : A.Sparse Y k N r) :
    (q.shrink h).core = q.core := q.recode_core h.restore

@[simp] theorem Encloses.shrink_vertex (q : (A.transport Y k).Encloses r G Z) (h : A.Sparse Y k N r) :
    (q.shrink h).pres.vertex = q.pres.vertex := q.recode_vertex h.restore

@[simp] theorem Encloses.shrink_slot (q : (A.transport Y k).Encloses r G Z) (h : A.Sparse Y k N r) :
    (q.shrink h).slot = q.slot := q.recode_slot h.restore

theorem Relocation.sparse (R : A.Relocation Y k) {src : A.format.obj} {s : Y.format.obj}
    {live : B Y.scheme.m → B Y.scheme.h → Bool} {links : A.Links Y k}
    (q : (A.transport Y k).Encloses (R.write src s live links) G Z)
    {δ : ℝ} (hd : 0 < δ) (charge : ∀ t, δ ≤ L.scale * L.charge t)
    (bound : ∀ v i, G.load v i ≤ (N : ℝ) * δ) :
    A.Sparse Y k N (R.write src s live links) := by
  intro i j
  refine ⟨q.slot_count hd charge bound i j, ?_⟩
  simp only [write, Equiv.symm_apply_apply, localRecord]
  intro t ht
  change (R.origin src live (i, j, t)).2.1 = 0
  by_cases hzero : t = 0
  · simp [origin, hzero]
  have hoff : (R.origin src live (i, j, t)).1 ≠ true := by
    intro h
    exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero, h⟩)
  unfold origin at hoff ⊢
  cases he : R.kept src (i, j, t) <;> simp [hzero, he] at hoff ⊢

namespace Data
variable (s : (A.transport Y k).Data a b u) (h : A.Sparse Y k N s.raw)

def shrink : (A.shrink Y k N).Data a b u :=
  ⟨s.T, s.a, s.b, s.L, s.G, s.Z, A.shorten Y k N s.raw, s.q.shrink h⟩

theorem shrink_fits {t : ℕ} (fit : s.Fits t) : (s.shrink h).Fits t :=
  recode_fits h.restore fit

theorem shrink_data {t : ℕ} (fit : s.Fits t) (i : Val a) (j : Val b) :
    (s.shrink h).data (s.shrink_fits h fit) i j = s.data fit i j :=
  s.q.recode_store h.restore fit i j

end Data
end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-! # One common label-compression table for a whole frame -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment

open Coloring

variable {F : Type} [Field F] {D : Template F}
  (A : Attachment D) (Y : Template F) (k N : ℕ)

def shrinkWidth := (A.transport Y k).ℓ + (A.shrink Y k N).ℓ

def shrinkGate :=
  weightTable (A := .addr (A.transport Y k).ℓ) (D := .addr (A.shrink Y k N).ℓ)
    (A.writeShort Y k N) (fun _ => (1 : F))

theorem shrink_arity : wd (A.shrinkGate Y k N).1 + wd (A.shrinkGate Y k N).2.1 = A.shrinkWidth Y k N := by
  simp only [shrinkGate, shrinkWidth, weightTable, lookup, wd_word, Format.width_addr]

def shortenCost :=
  4 * Y.format.width + 2 ^ Y.scheme.m * (2 ^ Y.scheme.h * (1 + A.shrinkWidth Y k N))

def shrinkCost (x y : Wire) (height : ℕ) :=
  A.shortenCost Y k N + 4 * (payload x y height Y.scheme.m).width

variable {A Y k N} {u v : ℕ} {L : Set (Table F)}
  (hu : 3 ≤ u) (hf : A.shrinkWidth Y k N ≤ u) (hl : A.shrinkGate Y k N ∈ L)

include hu hf hl

theorem shorten_net : Map F u L (A.transport Y k).format (A.shrink Y k N).format
    (A.shorten Y k N) (A.shortenCost Y k N) := by
  let X := Format.addr (A.transport Y k).ℓ
  let W := Format.addr (A.shrink Y k N).ℓ
  have he : X.width + W.width = A.shrinkWidth Y k N := by
    rw [Format.width_addr, Format.width_addr]
    rfl
  have row : Map F u L X W (A.writeShort Y k N) (1 + A.shrinkWidth Y k N) := by
    rw [← he, ← add_assoc]
    exact Kernel.lookup (he.le.trans hf) hl
  have codes := Map.vec (t := Y.scheme.m) _ (fun _ => Map.vec (t := Y.scheme.h) _ (fun _ => row))
  exact (Map.circuit hu (Circuit.id F Y.format)).par codes

/-- The payload stays in its original order and the diagram is unchanged. -/
theorem shrink_frames {x y : Wire} {height : ℕ}
    {P : (A.transport Y k).Data x y v → Prop} {Q : (A.shrink Y k N).Data x y v → Prop}
    (hs : ∀ s, P s → A.Sparse Y k N s.raw)
    (hq : ∀ s (h : P s), Q (s.shrink (hs s h))) :
    Transforms F u L ((A.transport Y k).frame x y v height P) ((A.shrink Y k N).frame x y v height Q)
      (A.shrinkCost Y k N x y height) := by
  let X := (A.transport Y k).frame x y v height P
  let W := (A.shrink Y k N).frame x y v height Q
  let send (s : X.state) : W.state :=
    ⟨s.val.shrink (hs s.val s.property.1), hq s.val s.property.1,
      s.val.shrink_fits (hs s.val s.property.1) s.property.2⟩
  have net := (shorten_net hu hf hl).par (Map.circuit hu (Circuit.id F (payload x y height Y.scheme.m)))
  refine Transforms.of_map _ send net (fun _ => rfl) (fun s i j => Prod.ext rfl ?_)
  exact (s.val.shrink_data (hs s.val s.property.1) s.property.2 i j).symm

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-! # Locating the predecessor of a span using only short indices -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring Packing BatchDescent
open scoped Classical

variable {F : Type} {D Y : Template F} (A : Attachment D) {k p : ℕ}

structure Source (p : ℕ) where
  hop : B p
  block : B D.scheme.h
  seat : B A.k
  label : B A.ℓ

abbrev Key (p : ℕ) := A.Source p × B A.e

variable (self : B p) (x : (A.bundle Y k p).obj)

def frozen (j : B k) : Option (A.Source p) :=
  let w := x.1.2.2.2 j
  let z := x.2 (request Y k (.inr j))
  if w.1 = true ∧ A.live z w.2.2 = true ∧ w.2.2 ≠ 0 then some ⟨self, w.2.1, w.2.2, z⟩ else none

def coreKey (j : B Y.scheme.e) : Option (A.Key p) :=
  let w := x.1.2.2.1 j
  let z := x.2 (request Y k (.inl j))
  if w.1 then some (⟨w.2.1, w.2.2.1, 0, z⟩, A.coreSpan w.2.2.2.2) else none

def key (i : B k) (j : B (A.spanBits Y)) : Option (A.Key p) :=
  if i = 0 then Function.extend (A.inner Y) (A.coreKey x) (fun _ => none) j
  else Function.extend (A.outer Y) (fun t => (A.frozen self x i).map (fun s => (s, t))) (fun _ => none) j

def memberAt (i : B k) : A.member.obj :=
  if i = 0 then (x.1.2.1, 0, 0)
  else (A.frozen self x i).elim (false, 0, 0) (fun t => (true, t.label, t.seat))

namespace Query
variable {A} (q : Query A Y k p) (self : B p) (i : B Y.scheme.m) (j : B Y.scheme.h)

def relocate (o : A.Source p) : A.scheme.Vtx := (q.M.nav i o.hop, o.block, o.seat)

def name (w : A.Key p) : A.scheme.Span := (q.relocate i w.1, w.2)

def letter (j : A.scheme.Vtx) := q.old.2 j.1 j.2.1

local notation "X" => q.received self i j

theorem frozen_eq (hs : q.M.nav i self = q.R.parent i) (l : B k) :
    (A.frozen self X l).map (fun w => (q.relocate i w, w.label)) =
      (q.R.kept q.old (i, j, l)).map (fun v => (v, q.letter v)) := by
  have key : (X).1.2.2.2 l = A.tag (q.R.prev i j l) := rfl
  unfold frozen Relocation.kept Relocation.back
  rw [key]
  cases hw : q.R.prev i j l with
  | none => simp [tag]
  | some w =>
    rw [q.answer_slot self i j hs l w hw]
    simp only [tag, true_and, Option.map_some]
    by_cases h : A.live (q.old.2 (q.R.parent i) w.1) w.2 = true ∧ w.2 ≠ 0
    · simp [h.1, h.2, hs, relocate, letter]
      exact ⟨w.1, w.2, ⟨rfl, h⟩, rfl, rfl⟩
    · simp [h]
      exact fun u => not_ne_iff.mp (fun v => h ⟨u, v⟩)

theorem core_eq (l : B Y.scheme.e) :
    (A.coreKey X l).map (fun w => (q.name i w, w.1.label)) =
      ((q.M.previous ((i, j, 0), l)).map A.fromCore).map (fun w => (w, q.letter w.1)) := by
  have key : (X).1.2.2.1 l = Trail.point D.scheme (q.M.read ((i, j, 0), l)) := rfl
  unfold coreKey Trail.Move.previous
  rw [key]
  cases hw : q.M.read ((i, j, 0), l) with
  | none => rfl
  | some w => rw [q.answer_core self i j l w hw]; rfl

variable [Field F] (hs : q.M.nav i self = q.R.parent i)

include hs in
theorem key_eq (t : B k) (l : B (A.spanBits Y)) :
    (A.key self X t l).map (fun w => (q.name i w, w.1.label)) =
      (q.R.previous q.old q.M ((i, j, t), l)).map (fun w => (w, q.letter w.1)) := by
  unfold key Relocation.previous
  by_cases ht : t = 0
  · simp only [ht, ite_true]
    by_cases h : l ∈ Set.range (A.inner Y)
    · obtain ⟨v, rfl⟩ := h
      erw [(A.inner Y).injective.extend_apply, (A.inner Y).injective.extend_apply]
      exact q.core_eq self i j v
    · erw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]; rfl
  · simp only [ht, ite_false]
    by_cases h : l ∈ Set.range (A.outer Y)
    · obtain ⟨v, rfl⟩ := h
      erw [(A.outer Y).injective.extend_apply, (A.outer Y).injective.extend_apply]
      have hh := congrArg (Option.map (fun z : A.scheme.Vtx × B A.ℓ => ((z.1, v), z.2)))
        (q.frozen_eq self i j hs t)
      simp only [Option.map_map] at hh ⊢
      exact hh
    · erw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]; rfl

omit [Field F] in
include hs in
theorem member_eq (t : B k) : A.memberAt self X t = q.R.origin q.old q.active (i, j, t) := by
  unfold memberAt Relocation.origin
  by_cases ht : t = 0
  · rw [ite_eq_left ht, ite_eq_left ht]; rfl
  · rw [ite_eq_right ht, ite_eq_right ht]
    have hh := q.frozen_eq self i j hs t
    cases h : A.frozen self X t <;> cases h' : q.R.kept q.old (i, j, t)
    all_goals simp only [h, h', Option.map_none, Option.map_some, Option.some.injEq] at hh
    · rfl
    · cases hh
    · cases hh
    · exact congrArg (fun z : A.scheme.Vtx × B A.ℓ => (true, z.2, z.1.2.2)) hh

end Query
end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-! # Inspecting endpoint labels without long host names in any block -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring
variable {F : Type} {D Y : Template F} (A : Attachment D) (Y : Template F) (k p : ℕ)

abbrev Review := Inspect.Row D.scheme.d Y.scheme.d p (A.bundle Y k p)

variable {A Y k p}

def Query.review (q : A.Query Y k p) (self : B p) (i : B Y.scheme.m) (j : B Y.scheme.h) : (A.Review Y k p).obj :=
  (Alias.mask ((fun t => D.nav q.old.1 (q.M.nav i t)), (fun t => q.M.nav (Y.nav q.fresh i t))),
    q.received self i j, fun t => q.received self (Y.nav q.fresh i t) j)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-!
# Identifying the remote tether endpoint

A shared Boolean mask compares the old host names. Block, seat
and span comparisons take place entirely on the short records.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Packing Coloring BatchDescent
open scoped Classical

variable {F : Type} [Field F] {D Y : Template F} {A : Attachment D} {k p : ℕ}
    (self : B p) (x : (A.Review Y k p).obj)

abbrev OldEnd (A : Attachment D) := B D.scheme.d × B A.k × B A.e

def detect (w : A.Source p) (dst : A.OldEnd) (t : (A.endpoint Y k).obj) : Bool :=
  match A.key self (x.2.2 t.1) t.2.1 t.2.2 with
  | none => false
  | some u => x.1 w.hop dst.1 t.1 u.1.hop && decide ((u.1.block, u.1.seat, u.2) = (w.block, dst.2))

def contactAt (v : B k) (j : B (A.spanBits Y)) : Bool × Option (A.endpoint Y k).obj :=
  match A.key self x.2.1 v j with
  | none =>
    let r := Y.scheme.decode x.2.1.1.1
    Function.extend (A.inner Y) (fun t =>
      (r.direction 0 t, (r.peer 0 t).map (fun p => (p.1, 0, A.inner Y p.2.2)))) (fun _ => (false, none)) j
  | some w =>
    let r := A.decode w.1.label
    (r.direction w.1.seat w.2, (r.peer w.1.seat w.2).bind (fun dst => Relocation.seek (detect self x w.1 dst)))

def rebuild : (A.record Y k).obj :=
  (x.2.1.1.1, fun j => (A.memberAt self x.2.1 j, fun l => A.point Y k (contactAt self x j l)))

namespace Query
variable (q : Query A Y k p) (self : B p) (hs : ∀ i, q.M.nav i self = q.R.parent i)
    (i : B Y.scheme.m) (j : B Y.scheme.h)

local notation "X" => q.review self i j
local notation "W" => q.received self i j

include hs in
theorem previous_eq (v : B k) (l : B (A.spanBits Y)) :
    q.R.previous q.old q.M ((i, j, v), l) = (A.key self W v l).map (q.name i) := by
  have h := congrArg (Option.map Prod.fst) (q.key_eq self i j (hs i) v l)
  simpa only [Option.map_map, Function.comp_def, Option.map_id'] using h.symm

def remote (w : A.Source p) (dst : A.OldEnd) : A.scheme.Span :=
  ((D.nav q.old.1 (q.M.nav i w.hop) dst.1, w.block, dst.2.1), dst.2.2)

include hs in
theorem detect_eq (w : A.Source p) (dst : A.OldEnd) (v : B k) (t : (A.endpoint Y k).obj) :
    detect self X w dst t =
      decide (q.R.previous q.old q.M (Relocation.resolve q.fresh (i, j, v) t) = some (q.remote i w dst)) := by
  unfold Relocation.resolve
  rw [q.previous_eq self hs]
  unfold detect review
  dsimp only
  cases A.key self (q.received self (Y.nav q.fresh i t.1) j) t.2.1 t.2.2 with
  | none => simp
  | some u =>
    obtain ⟨h, s, l⟩ := dst
    apply Bool.eq_iff_iff.mpr
    simp only [Alias.mask, Bool.and_eq_true, decide_eq_true_eq, Prod.mk.injEq, Option.map_some,
      Option.some.injEq, name, relocate, remote]
    tauto

include hs in
theorem contact_eq (v : B k) (l : B (A.spanBits Y)) :
    contactAt self X v l = q.R.links q.old q.fresh q.M ((i, j, v), l) := by
  unfold contactAt Relocation.links
  have hk := q.key_eq self i j (hs i) v l
  have hr := q.previous_eq self hs i j v l
  rw [hr] at hk ⊢
  change (match A.key self W v l with | none => _ | some t => _) = _
  cases h : A.key self W v l with
  | none => rfl
  | some w =>
    simp only [h, Option.map_some, Option.some.injEq] at hk
    have hv : w.1.label = q.letter (q.name i w).1 := congrArg Prod.snd hk
    let r := A.decode w.1.label
    have hd : A.scheme.direction (A.rows q.old) (q.name i w) = r.direction w.1.seat w.2 :=
      congrArg (fun t => (A.decode t).direction w.1.seat w.2) hv.symm
    have hp : A.scheme.peer (A.rows q.old) (q.name i w) =
        (r.peer w.1.seat w.2).map (q.remote i w.1) :=
      congrArg (fun t => ((A.decode t).peer w.1.seat w.2).map (q.remote i w.1)) hv.symm
    simp only [Option.map_some, hd, hp]
    refine Prod.ext ?_ ?_
    · rfl
    change (r.peer w.1.seat w.2).bind _ = ((r.peer w.1.seat w.2).map _).bind _
    cases r.peer w.1.seat w.2 with
    | none => rfl
    | some dst => exact congrArg Relocation.seek (funext fun t => q.detect_eq self hs i j w.1 dst v t)

include hs in
theorem rebuild_eq :
    rebuild self X = q.R.localRecord q.old q.fresh q.active (q.R.links q.old q.fresh q.M) i j := by
  unfold rebuild Relocation.localRecord
  refine Prod.ext rfl (funext fun v => Prod.ext (q.member_eq self i j (hs i) v) ?_)
  exact funext fun l => congrArg (A.point Y k) (q.contact_eq self hs i j v l)

end Query
end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-! # Tether connections and untouched exterior pins after reattachment -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
open Coloring Packing BatchDescent
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y a b : Wire} {D Y : Template F} {A : Attachment D} {k m : ℕ}
  {u v : ℕ} {L : Fringe x y T} {G : HostNet F L D.scheme.h u}
  {H : HostNet F L Y.scheme.h v} {Z : Border F T a b x y} {r : A.format.obj} {s : Y.format.obj}
  {R : A.Relocation Y k} {q : A.Encloses r G Z} {p : Y.Encodes s H} {slot : T → B k}

private theorem Encloses.bond (q : A.Encloses r G Z) (j : (Z.attach G.diagram).E) :
    q.pres.toSeating.Bond (.inl (.inr j)) (.inr (.inr j)) :=
  ⟨q.pres.internal j, (q.pres.internal j).symm q.pres.proper, q.directed _, q.directed _⟩

private theorem Encloses.tether_bond (q : A.Encloses r G Z) (i : slots x ⊕ slots y) :
    q.pres.toSeating.Bond (Z.coreEnd G.diagram (boundaryEnd G.diagram i)) (Z.outerEnd G.diagram (Border.other i)) := by
  cases i with
  | inl i => exact q.bond (.inr (.inl i))
  | inr i => exact (q.bond (.inr (.inr i))).swap

namespace Relocation.Moves
variable (h : R.Moves q p slot) {live : B Y.scheme.m → B Y.scheme.h → Bool}
  (ok : WriteActive p live) {M : Trail.Move D.scheme Y.scheme m}
  (move : M.Agrees q.core.post.toPresentation p.post.toPresentation)

local notation "U" => A.transport Y k
local notation "W" => scheme U
local notation "edges" => R.links r s M
local notation "out" => rows U (R.write r s live edges)
local notation "seated" => h.seating ok edges
local notation "new" => Scheme.Seating.ends seated
local notation "old" => q.pres.toSeating.ends

private theorem transfer {j l : (Z.attach H.diagram).End} {w t : (Z.attach G.diagram).End}
    (bond : q.pres.toSeating.Bond w t)
    (hj : ∀ z, R.previous r M z = some (old w).1 ↔ z = (new j).1)
    (hl : ∀ z, R.previous r M z = some (old t).1 ↔ z = (new l).1)
    (ej : (new j).2.val = (old w).2.val) (el : (new l).2.val = (old t).2.val)
    (dj : w.isRight = j.isRight) (dl : t.isRight = l.isRight)
    (hop : Hops s (new j).1 (new l).1 ∧ Hops s (new l).1 (new j).1) : (seated).Bond j l := by
  have a := R.linked r s M ((hj _).mpr rfl) bond.1.1 hl hop.1
  have b := R.linked r s M ((hl _).mpr rfl) bond.2.1.1 hj hop.2
  have offset := ej.trans (bond.1.2.trans el.symm)
  exact ⟨⟨(peer_pin _).trans a.2, offset⟩, ⟨(peer_pin _).trans b.2, offset.symm⟩,
    (R.direction_at _ _ _ _ _).trans (a.1.trans (bond.2.2.1.trans dj)),
    (R.direction_at _ _ _ _ _).trans (b.1.trans (bond.2.2.2.trans dl))⟩

include move in
theorem tether_bond (full : Y.full = true) (i : slots x ⊕ slots y) :
    (seated).Bond (Z.coreEnd H.diagram (boundaryEnd H.diagram i)) (Z.outerEnd H.diagram (Border.other i)) := by
  apply h.transfer ok (q.tether_bond i) (h.old_inner ok move i) (h.old_outer ok move (Border.other i)) _
    (h.outer_end ok edges _).2 (by cases i <;> rfl) (by cases i <;> rfl) (h.tether_hops ok full i)
  rw [(h.core_end ok edges _).2, (q.core_end _).2]
  have eq := (move.mapped i).2.2
  cases i <;> exact eq

include move in
theorem outer_free (i : Border.Ends a b x y)
    (hi : A.scheme.peer (A.rows r) (old (Z.outerEnd G.diagram i)).1 = none) :
    (seated).Free (Z.outerEnd H.diagram i) := by
  have he := R.detached r s M ((h.old_outer ok move i _).mpr rfl) hi
  constructor
  · rw [peer_pin, he]
    rfl
  · rw [R.direction_at, he, q.directed]
    rcases i with (i|i)|(i|i) <;> rfl

end Relocation.Moves
end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment
end

/-! # Reattaching the unchanged border after moving the core -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Relocation.Moves
open Coloring Packing BatchDescent
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y a b : Wire} {D Y : Template F} {A : Attachment D} {k m : ℕ}
  {u v : ℕ} {L : Fringe x y T} {G : HostNet F L D.scheme.h u}
  {H : HostNet F L Y.scheme.h v} {Z : Border F T a b x y} {r : A.format.obj} {s : Y.format.obj}
  {R : A.Relocation Y k} {q : A.Encloses r G Z} {p : Y.Encodes s H} {slot : T → B k}
  (h : R.Moves q p slot) {live : B Y.scheme.m → B Y.scheme.h → Bool}
  (ok : WriteActive p live) {M : Trail.Move D.scheme Y.scheme m}
  (move : M.Agrees q.core.post.toPresentation p.post.toPresentation) (full : Y.full = true)

local notation "links" => R.links r s M

include move full in
theorem connected : (h.seating ok links).Connected where
  used j he := by
    rw [R.peer_at] at he
    by_contra! hn
    exact he (ite_eq_right (not_lt.mpr hn))
  bond
    | .inl e => h.core_bond ok move e
    | .inr (.inl i) => h.tether_bond ok move full (.inl i)
    | .inr (.inr i) => (h.tether_bond ok move full (.inr i)).swap
  input i := h.outer_free ok move (.inl (.inl i)) (q.pres.input i)
  output i := h.outer_free ok move (.inr (.inl i)) (q.pres.output i)

/-- The emitted attachment presents exactly the new core and the old
border, with the same exterior bit order and the same parked charges. -/
def enclose : (A.transport Y k).Encloses (R.write r s live links) H Z where
  full := full
  tether := q.tether
  core := p
  pres := (h.connected ok move full).presentation
  directed := (h.connected ok move full).directed
  occupied j := by rw [R.live_at]; exact h.in_range ok j
  slot := slot
  positive := h.positive
  internal _ := rfl
  frozen _ := rfl
  charge := h.charge links
  ordered := h.core_pin ok links

theorem exterior_pin (i : slots a ⊕ slots b) :
    let j := ((h.enclose ok move full).pres.boundary i).val
    let z := (q.pres.boundary i).val
    R.kept r j.1.1 = some z.1.1 ∧ j.1.2 = A.outer Y z.1.2 ∧ j.2.val = z.2.val := by
  have aux (i : Border.Ends a b x y) :
      let j := (h.seating ok links).ends (Z.outerEnd H.diagram i)
      let z := q.pres.toSeating.ends (Z.outerEnd G.diagram i)
      R.kept r j.1.1 = some z.1.1 ∧ j.1.2 = A.outer Y z.1.2 ∧ j.2.val = z.2.val := by
    have ht := h.outer_end ok links i
    refine ⟨?_, congrArg Prod.snd ht.1, ht.2⟩
    rw [ht.1, q.outer_end, h.kept_at]
  cases i with
  | inl i => exact aux (.inl (.inl i))
  | inr i => exact aux (.inr (.inl i))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Relocation.Moves
end

/-!
# Preserving the height of the exterior bit bank

Each exterior bit belongs to a frozen member. All the bits stored
at a new host came from its one parent, so the old height suffices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Relocation
open Coloring Packing BatchDescent
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y a b : Wire} {D Y : Template F} {A : Attachment D} {k m : ℕ}
  {u v : ℕ} {L : Fringe x y T} {G : HostNet F L D.scheme.h u}
  {H : HostNet F L Y.scheme.h v} {Z : Border F T a b x y} {r : A.format.obj} {s : Y.format.obj}
  {R : A.Relocation Y k} {q : A.Encloses r G Z} {p : Y.Encodes s H} {slot : T → B k}
  (h : R.Moves q p slot) {live : B Y.scheme.m → B Y.scheme.h → Bool}
  (ok : WriteActive p live) {M : Trail.Move D.scheme Y.scheme m}
  (move : M.Agrees q.core.post.toPresentation p.post.toPresentation) (full : Y.full = true)

omit [Field F] in
theorem parent_of_kept (j : Place Y k) (w : A.scheme.Vtx) (hw : R.kept r j = some w) :
    R.parent j.1 = w.1 := by
  have hh := (Option.filter_eq_some_iff.mp hw).1
  obtain ⟨t, _, ht⟩ := Option.map_eq_some_iff.mp hh
  exact congrArg Prod.fst ht

namespace Moves
local notation "U" => A.transport Y k
local notation "r'" => R.write r s live (R.links r s M)

include h ok move full in
theorem volume_le (i : B Y.scheme.m) :
    (U).scheme.load ((U).rows r') i ≤ A.scheme.load (A.rows r) (R.parent i) := by
  let p' := (h.enclose ok move full).pres
  let e := p'.boundary.symm.trans q.pres.boundary
  have he (j : (U).scheme.exposed ((U).rows r')) :
      R.parent ((U).scheme.owner _ j) = A.scheme.owner _ (e j) := by
    obtain ⟨x, rfl⟩ := p'.boundary.surjective j
    rw [show e (p'.boundary x) = q.pres.boundary x from congrArg q.pres.boundary (p'.boundary.symm_apply_apply x)]
    exact parent_of_kept _ _ (h.exterior_pin ok move full x).1
  let f (j : (U).scheme.fiber ((U).rows r') i) : A.scheme.fiber (A.rows r) (R.parent i) :=
    ⟨e j.val, (he j.val).symm.trans (congrArg R.parent j.property)⟩
  exact Fintype.card_le_of_injective f (fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h)))

include h ok move full in
theorem fits {V height : ℕ} (fit : A.scheme.Fits (A.rows r) V height) :
    (U).scheme.Fits ((U).rows r') (volume a b Y.scheme.m) height :=
  (h.enclose ok move full).pres.fits le_rfl (fun i => (h.volume_le ok move full i).trans (fit.2 _))

end Moves
end OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Relocation
end
