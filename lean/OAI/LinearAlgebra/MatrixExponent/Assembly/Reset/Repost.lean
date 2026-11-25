import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames
import OAI.LinearAlgebra.MatrixExponent.Packing.HostReset
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Checks
import OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Rate

/-! # Exposed spans after a host reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Packing Coloring
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} (p : S.Posting r G)
  {B' W : ℝ} {Hcap D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D)

abbrev Face := p.toPresentation.BorderSpan ⊕ (q.Survivors × Bool)

def visibleWidth : Face p q → ℕ := Sum.elim p.toPresentation.borderWidth (fun _ => u)

def whereAt : Face p q → Cell a × q.vertex
  | .inl j => q.owner (G.units.place j.val.1)
  | .inr (e, b) => cond b (q.supply e.val).2 (q.supply e.val).1

def faceBits : (Σ j, Fin (visibleWidth p q j)) ≃ (q.contract G.units).End :=
  let swap : (q.Survivors × Bool) × Fin u ≃ (q.Survivors × Fin u) × Bool :=
    ⟨fun j => ((j.1.1, j.2), j.1.2), fun j => ((j.1.1, j.2), j.1.2), fun _ => rfl, fun _ => rfl⟩
  let cut := ((Equiv.sigmaEquivProd _ _).trans swap).trans
    ((q.remaining G.units).prodCongr (Equiv.refl Bool))
  ((Equiv.sumSigmaDistrib _).trans (p.toPresentation.exteriorBits.sumCongr cut)).trans (Subround.endIndex _)

theorem face_location (j : Σ i, Fin (visibleWidth p q i)) :
    (q.contract G.units).station (faceBits p q j) = whereAt p q j.1 := by
  rcases j with ⟨v|⟨e, b⟩, i⟩
  · let z : p.toPresentation.BorderBit := ⟨v, i⟩
    have he (j : slots x ⊕ slots y) :
        (q.contract G.units).station (boundaryEnd _ j) = q.owner (G.units.place (portEnd G.diagram j)) := by
      cases j <;> rfl
    exact (he (p.toPresentation.exteriorBits z)).trans
      (congrArg (q.owner ∘ G.units.place) (p.toPresentation.border_station z))
  · cases b <;> rfl

abbrev Visible (v : Cell a × q.vertex) := {j : Face p q // whereAt p q j = v}

def visibleBits (v : Cell a × q.vertex) :
    (Σ j : Visible p q v, Fin (visibleWidth p q j.val)) ≃ (q.contract G.units).Port v := by
  let E := q.contract G.units
  let e := faceBits p q
  let f (j : Σ t : Visible p q v, Fin (visibleWidth p q t.val)) :
      {t : E.End // E.station t = v} :=
    ⟨e ⟨j.1.val, j.2⟩, (face_location p q _).trans j.1.property⟩
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).trans (E.incident v).symm
  · rintro ⟨⟨j, hj⟩, b⟩ ⟨⟨k, hk⟩, c⟩ he
    have h := e.injective (congrArg Subtype.val he)
    cases h
    rfl
  · rintro ⟨j, hj⟩
    obtain ⟨⟨k, b⟩, rfl⟩ := e.surjective j
    exact ⟨⟨⟨k, (face_location p q _).symm.trans hj⟩, b⟩, rfl⟩

theorem visible_pin (v : Cell a × q.vertex) (j : Σ t : Visible p q v, Fin (visibleWidth p q t.val)) :
    named (q.contract G.units) v (visibleBits p q v j) = faceBits p q ⟨j.1.val, j.2⟩ := by
  let E := q.contract G.units
  change ((E.incident v) ((E.incident v).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # Assigning surviving and exterior spans to new host records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Packing Coloring
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} (p : S.Posting r G)
  {B' W : ℝ} {Hcap D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D)
  (U : Scheme F)

structure Allocation where
  host : q.vertex ↪ B U.m
  block : Cell a ↪ B U.h
  index : q.vertex → q.vertex → B U.d
  seat : ∀ v, Visible p q v ↪ B U.e

namespace Allocation
variable {p q U} (A : Allocation p q U)

def vertex : Cell a × q.vertex ↪ U.Vtx where
  toFun v := (A.host v.2, A.block v.1, 0)
  inj' _ _ he := Prod.ext (A.block.injective (Prod.mk.inj (Prod.mk.inj he).2).1)
    (A.host.injective (Prod.mk.inj he).1)

local notation "atSite" => whereAt p q

def slot (j : Face p q) := A.seat (atSite j) ⟨j, rfl⟩

theorem slot_eq (v : Cell a × q.vertex) (j : Visible p q v) :
    A.slot j.val = A.seat v j := by
  obtain ⟨j, rfl⟩ := j
  rfl

def span (j : Face p q) : U.Span := (A.vertex (atSite j), A.slot j)

theorem span_injective : Function.Injective A.span := by
  intro j k he
  have hk := A.vertex.injective (Prod.mk.inj he).1
  let t : Visible p q (atSite k) := ⟨j, hk⟩
  have h : A.seat _ t = A.seat _ ⟨k, rfl⟩ := (A.slot_eq _ t).symm.trans (Prod.mk.inj he).2
  exact congrArg Subtype.val ((A.seat _).injective h)

structure Lengths (out : U.format.obj) : Prop where
  used : ∀ j, U.width out (A.span j) = visibleWidth p q j
  idle : ∀ t ∉ Set.range A.span, U.width out t = 0

variable {out : U.format.obj} (l : A.Lengths out)

include l in
theorem length_at (v : Cell a × q.vertex) (j : Visible p q v) :
    U.width out (A.vertex v, A.seat v j) = visibleWidth p q j.val := by
  obtain ⟨j, rfl⟩ := j
  exact l.used j

def orderPins (v : Cell a × q.vertex) :
    (Σ j : Visible p q v, Fin (visibleWidth p q j.val)) ≃
      U.LocalPin out (A.vertex v) :=
  Equiv.ofBijective (fun t => ⟨A.seat v t.1, t.2.cast (A.length_at l v t.1).symm⟩) ⟨by
    rintro ⟨j, b⟩ ⟨k, c⟩ he
    have hj : j = k := (A.seat v).injective (congrArg Sigma.fst he)
    subst k
    have hi : b.val = c.val := congrArg (fun p => p.2.val) he
    rw [Fin.ext hi], by
    rintro ⟨j, b⟩
    have hs : (A.vertex v, j) ∈ Set.range A.span := by
      by_contra h
      have := l.idle _ h
      have := b.isLt
      omega
    obtain ⟨k, hk⟩ := hs
    let t : Visible p q v := ⟨k, A.vertex.injective (Prod.mk.inj hk).1⟩
    have he : A.seat v t = j := (A.slot_eq v t).symm.trans (Prod.mk.inj hk).2
    have hl : b.val < visibleWidth p q t.val := by rw [← A.length_at l, he]; exact b.isLt
    refine ⟨⟨t, ⟨b.val, hl⟩⟩, Sigma.ext he ?_⟩
    exact (Fin.heq_ext_iff (congrArg (fun j => U.width out (A.vertex v, j)) he)).mpr rfl⟩

def pin (v : Cell a × q.vertex) :
    (q.contract G.units).Port v ≃ U.LocalPin out (A.vertex v) :=
  (visibleBits p q v).symm.trans (A.orderPins l v)

theorem pin_at (v : Cell a × q.vertex) (j : Visible p q v)
    (k : Fin (visibleWidth p q j.val)) :
    A.pin l v (visibleBits p q v ⟨j, k⟩) =
      ⟨A.seat v j, k.cast (A.length_at l v j).symm⟩ := by
  rw [pin, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

end Allocation
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # Reposting an ordered host after a reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Allocation

open Packing Coloring
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} {p : S.Posting r G}
  {B' W : ℝ} {Hcap D : ℕ}
  {q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D}
  {U : Scheme F} (A : Allocation p q U) {out : U.format.obj} (l : A.Lengths out)

abbrev unitSeat (e : q.Survivors) (t : Bool) := A.slot (.inr (e, t))

abbrev endHost (e : q.Survivors) (t : Bool) := (cond t (q.supply e.val).2 (q.supply e.val).1).2

theorem site_end (e : q.Survivors) (t : Bool) :
    (A.span (.inr (e, t))).1 =
      (A.host (endHost (q := q) e t), A.block (q.supply e.val).1.1, 0) := by
  cases t
  · rfl
  · rw [(q.support e.val).1]
    rfl

/-- Conditions on decoded local patterns. No names of remote hosts
are needed by a station's tensor table. -/
structure Agrees : Prop where
  sample : ∀ v t, U.table out (A.vertex v) t =
    Transcript.sample ((q.contract G.units).table v) (t ∘ A.pin l v)
  vacant : ∀ v ∉ Set.range A.vertex, ∀ t, U.table out v t = 1
  outside : ∀ j, U.peer out (A.span (.inl j)) = none
  idle : ∀ t ∉ Set.range A.span, U.peer out t = none
  dir : ∀ e t, U.direction out (A.span (.inr (e, t))) = t
  link : ∀ e t, let v := A.span (.inr (e, t))
    (U.pattern out v.1).peer v.1.2.2 v.2 =
      some (A.index (endHost (q := q) e t) (endHost (q := q) e (!t)),
        0, A.unitSeat e (!t))
  nav : ∀ (e : q.Survivors) t, let v := endHost (q := q) e t
    let w := endHost (q := q) e (!t)
    (out (A.host v)).1 (A.index v w) = A.host w

variable (H : A.Agrees l)

def seating : U.Seating out (q.contract G.units) where
  vertex := A.vertex
  pin := A.pin l
  cover v := by
    obtain ⟨j, he⟩ : v.1 ∈ Set.range A.span := by
      by_contra h
      have := l.idle _ h
      have := v.2.isLt
      omega
    exact ⟨_, congrArg Prod.fst he⟩
  sample := H.sample
  vacant := H.vacant

theorem end_pin (j : Face p q) (b : Fin (visibleWidth p q j)) :
    let y := faceBits p q ⟨j, b⟩
    (A.seating l H).ends y = ⟨A.span j, b.cast (l.used j).symm⟩ := by
  let v := whereAt p q j
  let r : Visible p q v := ⟨j, rfl⟩
  let o := visibleBits p q v ⟨r, b⟩
  have he := visible_pin p q v ⟨r, b⟩
  change (q.contract G.units).portEquiv ⟨v, o⟩ = faceBits p q ⟨j, b⟩ at he
  dsimp only
  rw [← he, Scheme.Seating.ends_at]
  change U.port out (A.vertex v) (A.pin l v o) = _
  rw [show A.pin l v o = _ from A.pin_at l v r b]
  rfl

include H in
theorem peer_end (e : q.Survivors) (t : Bool) :
    U.peer out (A.span (.inr (e, t))) = some (A.span (.inr (e, !t))) := by
  rw [Scheme.peer, H.link, Option.map_some, A.site_end]
  dsimp only
  rw [H.nav]
  apply congrArg some
  exact Prod.ext (A.site_end e (!t)).symm rfl

include H in
theorem proper : U.Proper out := by
  intro a b h
  by_cases he : a ∈ Set.range A.span
  swap
  · rw [H.idle _ he] at h
    cases h
  obtain ⟨j|⟨e, t⟩, rfl⟩ := he
  · rw [H.outside] at h
    cases h
  rw [A.peer_end l H, Option.some.injEq] at h
  subst b
  rw [A.peer_end l H, Bool.not_not, l.used, l.used, H.dir, H.dir]
  exact ⟨rfl, rfl, by cases t <;> decide⟩

theorem exposed_pin (j : p.toPresentation.BorderBit) :
    let G' := q.contract G.units
    (A.seating l H).ends (boundaryEnd G' (p.toPresentation.exteriorBits j)) =
      ⟨A.span (.inl j.1), j.2.cast (l.used (.inl j.1)).symm⟩ :=
  A.end_pin l H (.inl j.1) j.2

theorem unit_pin (e : q.Survivors) (b : Bool) (j : Fin u) :
    let e' := q.remaining G.units (e, j)
    (A.seating l H).ends (cond b (.inr (.inr e')) (.inl (.inr e'))) =
      ⟨A.span (.inr (e, b)), j.cast (l.used (.inr (e, b))).symm⟩ :=
  A.end_pin l H (.inr (e, b)) j

private theorem exposed_none (j : slots x ⊕ slots y) :
    U.peer out ((A.seating l H).ends (boundaryEnd _ j)).1 = none := by
  obtain ⟨t, rfl⟩ := p.toPresentation.exteriorBits.surjective j
  rw [A.exposed_pin]
  exact H.outside t.1

def presentation : U.Presentation out (q.contract G.units) where
  toSeating := A.seating l H
  proper := A.proper l H
  input t := A.exposed_none l H (.inl t)
  output t := A.exposed_none l H (.inr t)
  internal e := by
    obtain ⟨⟨a, j⟩, rfl⟩ := (q.remaining G.units).surjective e
    have hs := A.unit_pin l H a false j
    have ht := A.unit_pin l H a true j
    dsimp only [cond] at hs ht
    rw [hs, ht]
    exact ⟨A.peer_end l H a false, rfl⟩

private theorem unit_span (e : q.Survivors) (b : Bool) :
    U.spanAt (G.afterReset q) A.host A.block A.unitSeat e b = A.span (.inr (e, b)) := by
  refine Prod.ext ?_ rfl
  cases b
  · exact (A.site_end e false).symm
  · exact (A.site_end e true).symm

def posting : U.Posting out (G.afterReset q) where
  toPresentation := A.presentation l H
  host := A.host
  block := A.block
  stub := A.unitSeat
  index := A.index
  vertex_eq _ := rfl
  ordered e b j := by
    change q.Survivors at e
    let s := (A.seating l H).ends (Scheme.endBit (G.afterReset q) e b j)
    have he : s = ⟨A.span (.inr (e, b)), j.cast (l.used (.inr (e, b))).symm⟩ := A.unit_pin l H e b j
    change s.1 = _ ∧ s.2.val = j.val
    rw [he]
    exact ⟨(A.unit_span e b).symm, rfl⟩
  length e t := (congrArg (U.width out) (A.unit_span e t)).trans (l.used _)
  dir e t := (congrArg (U.direction out) (A.unit_span e t)).trans (H.dir e t)
  link e t := by
    change q.Survivors at e
    rw [unit_span]
    cases t
    · exact H.link e false
    · exact H.link e true

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Allocation
end

/-!
# Internal bundles at a reset

Each old wire contributes two hidden half-wires. Of the new supplies
only loops are hidden. All three kinds have the same unit width.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Packing
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {B' W : ℝ} {Hcap D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D)

abbrev raw := (q.rule.bundle u).reindex G.units.bits
abbrev before := G.diagram.expanded (raw q) ()
abbrev cluster := (before q).partition (Sum.elim (q.assign G.units ()) id)
abbrev Segment := G.E ⊕ G.E ⊕ q.wire

def ends : Segment q → (Cell a × q.vertex) × (Cell a × q.vertex)
  | .inl e => let v := q.owner (G.src e, G.ix e); (v, v)
  | .inr (.inl e) => let v := q.owner (G.dst e, G.ix e); (v, v)
  | .inr (.inr e) => q.supply e

def segmentBits : Segment q × Fin u ≃ (before q).E :=
  (Equiv.sumProdDistrib _ _ _).trans (G.units.bits.symm.sumCongr
    ((Equiv.sumProdDistrib _ _ _).trans (G.units.bits.symm.sumCongr (.refl _))))

theorem endpoints (j : Segment q × Fin u) :
    let e := segmentBits q j
    ((cluster q).owner ((before q).source e), (cluster q).owner ((before q).target e)) =
      ends q j.1 := by
  rcases j with ⟨e|e|e, j⟩
  · let i := G.units.bits.symm (e, j)
    change (q.owner (G.units.place (G.diagram.source i)),
      q.owner (G.src (G.units.bits i).1, G.ix (G.units.bits i).1)) = _
    simp only [G.units.left, i, Equiv.apply_symm_apply, ends]
  · let i := G.units.bits.symm (e, j)
    change (q.owner (G.dst (G.units.bits i).1, G.ix (G.units.bits i).1),
      q.owner (G.units.place (G.diagram.target i))) = _
    simp only [G.units.right, i, Equiv.apply_symm_apply, ends]
  · rfl

abbrev Hidden (v : Cell a × q.vertex) := {j : Segment q // ends q j = (v, v)}

def hiddenBits (v : Cell a × q.vertex) : Hidden q v × Fin u ≃ (cluster q).hidden v := by
  let f (j : Hidden q v × Fin u) := segmentBits q (j.1.val, j.2)
  have he (j : Hidden q v × Fin u) :
      (cluster q).owner ((before q).source (f j)) = v ∧
        (cluster q).owner ((before q).target (f j)) = v :=
    Prod.mk.inj ((endpoints q _).trans j.1.property)
  refine Equiv.ofBijective (fun j => ⟨⟨f j, (he j).1.trans (he j).2.symm⟩, (he j).1⟩) ⟨?_, ?_⟩
  · intro i j h
    have hl := (segmentBits q).injective (congrArg (fun x => x.val.val) h)
    exact Prod.ext (Subtype.ext (Prod.mk.inj hl).1) (Prod.mk.inj hl).2
  · rintro ⟨⟨j, hj⟩, hv⟩
    obtain ⟨⟨k, t⟩, rfl⟩ := (segmentBits q).surjective j
    have ht : ends q k = (v, v) :=
      (endpoints q (k, t)).symm.trans (Prod.ext hv (hj.symm.trans hv))
    exact ⟨(⟨k, ht⟩, t), rfl⟩

def old : G.diagram.End → (before q).End
  | .inl t => .inl (t.map id Sum.inl)
  | .inr t => .inr (t.map id (fun e => .inr (.inl e)))

def left (e : G.diagram.E) : (before q).End := .inr (.inr (.inl e))
def right (e : G.diagram.E) : (before q).End := .inl (.inr (.inr (.inl e)))

def supplyEnd (v : Cell a × q.vertex) (j : q.wire × Fin u) : (before q).End :=
  if (q.supply j.1).1 = v then .inl (.inr (.inr (.inr j))) else .inr (.inr (.inr (.inr j)))

variable (w : Bit (cluster q) → Bool)

abbrev read := w ∘ address (cluster q)

theorem old_factor (v : G.diagram.V) :
    factor (cluster q) (.inl v) w =
      Transcript.sample (G.diagram.table v) (read q w ∘ old q ∘ named G.diagram v) := by
  rw [factor, Diagram.weight_expanded]
  unfold Diagram.Expansion.entry Diagram.weight Transcript.sample
  apply congrArg₂ (G.diagram.table v).2.2 <;> apply congrArg <;> funext t
  · change Sum.elim _ _ (G.diagram.src ⟨v, t⟩) = read q w (old q (.inl (G.diagram.src ⟨v, t⟩)))
    cases G.diagram.src ⟨v, t⟩ <;> rfl
  · change Sum.elim _ _ (G.diagram.dst ⟨v, t⟩) = read q w (old q (.inr (G.diagram.dst ⟨v, t⟩)))
    cases G.diagram.dst ⟨v, t⟩ <;> rfl

theorem new_factor (v : Cell a × q.vertex) :
    factor (cluster q) (.inr v) w =
      ∏ j : Fin u, q.rule.entry () v
        (fun e => read q w (left q (G.units.bits.symm (e, j))))
        (fun e => read q w (right q (G.units.bits.symm (e, j))))
        (fun e => read q w (supplyEnd q v (e, j))) := by
  change _ = (raw q).entry () v (read q w ∘ left q) (read q w ∘ right q)
    (read q w ∘ supplyEnd q v)
  rw [factor, Diagram.weight_expanded]
  unfold Diagram.Expansion.entry
  apply congrArg ((raw q).entry () v (read q w ∘ left q) (read q w ∘ right q))
  funext j
  unfold supplyEnd
  simp only [Function.comp_apply]
  split_ifs <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # Addresses of the visible and hidden spans after a reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Packing
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} (p : S.Posting r G)
  {B' W : ℝ} {Hcap D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D)
  (v : Cell a × q.vertex)

abbrev Port := Visible p q v ⊕ Hidden q v

def width : Port p q v → ℕ := Sum.elim (fun j => visibleWidth p q j.val) (fun _ => u)

def bit : (j : Port p q v) → Fin (width p q v j) → Bit (cluster q)
  | .inl j, b => .inl (faceBits p q ⟨j.val, b⟩)
  | .inr j, b => .inr ⟨v, hiddenBits q v (j, b)⟩

def exterior (x : p.toPresentation.BorderSpan) (he : q.owner (G.units.place x.val.1) = v) :
    Port p q v := .inl ⟨.inl x, he⟩

theorem width_exterior (x : p.toPresentation.BorderSpan) (he) :
    width p q v (exterior p q v x he) = p.toPresentation.borderWidth x := rfl

abbrev demandSite (e : G.E) (t : Bool) := q.owner (Scheme.side G e t, G.ix e)

def demand (e : G.E) (t : Bool) (he : demandSite q e t = v) : Port p q v :=
  .inr ⟨cond t (.inr (.inl e)) (.inl e), by cases t <;> exact Prod.ext he he⟩

theorem width_demand (e : G.E) (t : Bool) (he) :
    width p q v (demand p q v e t he) = u := rfl

abbrev supplySite (e : q.wire) (t : Bool) := cond t (q.supply e).2 (q.supply e).1

def supply (e : q.wire) (t : Bool) (he : supplySite q e t = v) : Port p q v :=
  if h : (q.supply e).1 = (q.supply e).2 then
    .inr ⟨.inr (.inr e), by
      cases t
      · exact Prod.ext he (h.symm.trans he)
      · exact Prod.ext (h.trans he) he⟩
  else .inl ⟨.inr (⟨e, h⟩, t), he⟩

theorem width_supply (e : q.wire) (t : Bool) (he) :
    width p q v (supply p q v e t he) = u := by
  unfold supply
  split <;> rfl

theorem address_exterior (x : p.toPresentation.BorderSpan) (he)
    (j : Fin (p.toPresentation.borderWidth x)) :
    address (cluster q) (old q (boundaryEnd G.diagram (p.toPresentation.exteriorBits ⟨x, j⟩))) =
      bit p q v (exterior p q v x he) j := by
  change _ = (Sum.inl (boundaryEnd (q.contract G.units) (p.toPresentation.exteriorBits ⟨x, j⟩)) : Bit (cluster q))
  cases p.toPresentation.exteriorBits ⟨x, j⟩ <;> rfl

private theorem address_internal (e : Hidden q v) (j : Fin u) (t : Bool) :
    let b := segmentBits q (e.val, j)
    address (cluster q) (cond t (.inr (.inr b)) (.inl (.inr b))) =
      .inr ⟨v, hiddenBits q v (e, j)⟩ := by
  have h : (cluster q).edges.symm (segmentBits q (e.val, j)) = .inr ⟨v, hiddenBits q v (e, j)⟩ :=
    (cluster q).edges.symm_apply_eq.mpr rfl
  cases t <;> simp only [cond, address, h, Sum.map_inr, id_eq]

theorem address_demand_old (e : G.E) (t : Bool) (he) (j : Fin u) :
    address (cluster q) (old q (Scheme.endBit G e t j)) = bit p q v (demand p q v e t he) j := by
  cases t
  · exact address_internal q v ⟨.inl e, Prod.ext he he⟩ j false
  · exact address_internal q v ⟨.inr (.inl e), Prod.ext he he⟩ j true

theorem address_demand_new (e : G.E) (t : Bool) (he) (j : Fin u) :
    let b := G.units.bits.symm (e, j)
    address (cluster q) (cond t (right q b) (left q b)) = bit p q v (demand p q v e t he) j := by
  cases t
  · exact address_internal q v ⟨.inl e, Prod.ext he he⟩ j true
  · exact address_internal q v ⟨.inr (.inl e), Prod.ext he he⟩ j false

theorem bit_congr {x y : Port p q v} (h : x = y)
    {i : Fin (width p q v x)} {j : Fin (width p q v y)} (e : i.val = j.val) :
    bit p q v x i = bit p q v y j := by
  subst y
  rw [Fin.ext e]

theorem address_supply (e : q.wire) (t : Bool) (he : supplySite q e t = v) (j : Fin u) :
    address (cluster q) (supplyEnd q v (e, j)) =
      bit p q v (supply p q v e t he) (j.cast (width_supply p q v e t he).symm) := by
  by_cases h : (q.supply e).1 = (q.supply e).2
  · have hh : q.supply e = (v, v) := by
      cases t
      · exact Prod.ext he (h.symm.trans he)
      · exact Prod.ext (h.trans he) he
    let s : Hidden q v := ⟨.inr (.inr e), hh⟩
    have eq : supply p q v e t he = .inr s := dite_eq_left h
    refine Eq.trans ?_ (bit_congr p q v eq.symm (i := j) rfl)
    unfold supplyEnd
    rw [ite_eq_left (congrArg Prod.fst hh)]
    exact address_internal q v s j false
  · let f : q.Survivors := ⟨e, h⟩
    let s : Visible p q v := ⟨.inr (f, t), he⟩
    have eq : supply p q v e t he = .inl s := dite_eq_right h
    refine Eq.trans ?_ (bit_congr p q v eq.symm (i := j) rfl)
    have hx : (cluster q).edges.symm (.inr (.inr (e, j))) = .inl (q.remaining G.units (f, j)) :=
      (cluster q).edges.symm_apply_eq.mpr rfl
    subst v
    cases t <;> simp only [cond, supplySite, supplyEnd, h, ↓reduceIte, address, hx] <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # Addressing the old tensors in a reset cluster -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Coloring Packing Scheme
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} (p : S.Posting r G)
  {B' W : ℝ} {Hcap D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D)
  (v : Cell a × q.vertex)

abbrev Live := {w : G.diagram.V // 0 < G.diagram.arity w ∧ q.owner (G.units.place w) = v}

/-- Each nonempty argument of a previous tensor reads one full span. -/
structure AtomMap (m : Atom F) (w : (before q).V) where
  slot (j : m.Span) (h : 0 < m.width j) : Port p q v
  size (j) (h) : width p q v (slot j h) = m.width j
  value (b : Bit (cluster q) → Bool) :
    m.weight (fun j t => b (bit p q v (slot j t.pos) (t.cast (size _ _).symm))) =
      factor (cluster q) w b

variable (w : G.diagram.V) (hw : q.owner (G.units.place w) = v)

omit [Fintype T] in
private theorem span_end (j : S.Span) (hj : 0 < S.width r j) (hp : S.peer r j ≠ none) :
    ∃ e t, p.span e t = j := by
  obtain ⟨q, hq⟩ := p.toSeating.ends.surjective ⟨j, ⟨0, hj⟩⟩
  have he : (p.toSeating.ends q).1 = j := congrArg Sigma.fst hq
  rcases q with (t|e)|(t|e)
  · exact (hp (he ▸ p.input t)).elim
  · obtain ⟨⟨e, n⟩, rfl⟩ := G.units.bits.symm.surjective e
    exact ⟨e, false, (p.ordered e false n).1.symm.trans he⟩
  · exact (hp (he ▸ p.output t)).elim
  · obtain ⟨⟨e, n⟩, rfl⟩ := G.units.bits.symm.surjective e
    exact ⟨e, true, (p.ordered e true n).1.symm.trans he⟩

include hw in
private theorem station_location {j : B S.e} {e : G.E} {t : Bool} (he : p.span e t = (p.vertex w, j)) :
    demandSite q e t = v := by
  rw [p.vertex_eq] at he
  have h₁ := p.host.injective (congrArg (fun i : S.Span => i.1.1) he)
  have h₂ := p.block.injective (congrArg (fun i : S.Span => i.1.2.1) he)
  have h : G.units.place w = (side G e t, G.ix e) := Prod.ext h₁.symm h₂.symm
  rw [h] at hw
  exact hw

variable (j : B S.e) (hj : 0 < S.width r (p.vertex w, j))

inductive Origin : Port p q v → Prop
  | outside (f : p.toPresentation.BorderSpan) (hq : f.val = (w, j)) (he) :
    Origin (exterior p q v f he)
  | inside (e : G.E) (t : Bool) (he : p.span e t = (p.vertex w, j)) (hs) :
    Origin (demand p q v e t hs)

include hw hj in
private theorem exists_origin : ∃ f, Origin p q v w j f := by
  by_cases h : S.peer r (p.vertex w, j) = none
  · exact ⟨_, .outside ⟨(w, j), hj, h⟩ rfl hw⟩
  · obtain ⟨e, t, he⟩ := span_end p _ hj h
    exact ⟨_, .inside e t he (station_location p q v w hw he)⟩

def stationPort : Port p q v := (exists_origin p q v w hw j hj).choose

theorem station_origin : Origin p q v w j (stationPort p q v w hw j hj) :=
  (exists_origin p q v w hw j hj).choose_spec

theorem origin_width {s : Port p q v} (hs : Origin p q v w j s) :
    width p q v s = S.width r (p.vertex w, j) := by
  cases hs with
  | outside f hq he =>
    erw [width_exterior p q v f he, Presentation.borderWidth, hq]
  | inside e t he hs =>
    erw [width_demand p q v e t hs, ← he]
    exact (p.length e t).symm

theorem origin_address {s : Port p q v} (hs : Origin p q v w j s)
    (b : Fin (S.width r (p.vertex w, j))) :
    address (cluster q) (old q
      (p.toSeating.ends.symm ⟨(p.vertex w, j), b⟩)) =
      bit p q v s
        (b.cast (origin_width p q v w j hs).symm) := by
  cases hs with
  | outside f hq he =>
    rcases f with ⟨⟨u, l⟩, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
    let f : p.toPresentation.BorderSpan := ⟨(u, l), h⟩
    have eq := p.toPresentation.border_pin (⟨f, b⟩ : p.toPresentation.BorderBit)
    have hh : p.toSeating.ends.symm ⟨(p.vertex u, l), b⟩ =
        boundaryEnd _ (p.toPresentation.exteriorBits ⟨f, b⟩) := p.toSeating.ends.symm_apply_eq.mpr eq.symm
    rw [hh]
    exact address_exterior p q v f he b
  | inside e t he hm =>
    let c := b.cast ((congrArg (S.width r) he.symm).trans (p.length e t))
    have hh : p.toSeating.ends (endBit G e t c) = ⟨(p.vertex w, j), b⟩ := by
      have he' := (p.ordered e t c).1.trans he
      exact Sigma.ext he' ((Fin.heq_ext_iff (congrArg (S.width r) he')).mpr (p.ordered e t c).2)
    rw [p.toSeating.ends.symm_apply_eq.mpr hh.symm]
    exact address_demand_old p q v e t hm c

abbrev oldLabel := ((r (p.vertex w).1).2 (p.vertex w).2.1, (p.vertex w).2.2)

def oldMap : AtomMap p q v (History.original S (oldLabel p w)) (.inl w) where
  slot j h := stationPort p q v w hw j h
  size j h := origin_width p q v w j (station_origin p q v w hw j h)
  value b := by
    erw [old_factor q b w]
    change S.table r (p.vertex w) (fun u => b (bit p q v
      (stationPort p q v w hw u.1 u.2.pos) (u.2.cast
        (origin_width p q v w u.1 (station_origin p q v w hw u.1 u.2.pos)).symm))) = _
    rw [p.sample]
    apply congrArg
    funext k
    let u := p.pin w k
    have ht := origin_address p q v w u.1 (station_origin p q v w hw u.1 u.2.pos) u.2
    have he : p.toSeating.ends.symm ⟨(p.vertex w, u.1), u.2⟩ = named G.diagram w k :=
      p.toSeating.ends.symm_apply_eq.mpr (p.toSeating.ends_at w k).symm
    rw [he] at ht
    exact congrArg b ht.symm

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # The contracted station as a local sum of products -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Packing Coloring
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} (p : S.Posting r G)
  {B' W : ℝ} {Hcap D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D)
  (v : Cell a × q.vertex)

abbrev Exposed := Σ j : Visible p q v, Fin (visibleWidth p q j.val)
abbrev Inner := Hidden q v × Fin u
abbrev Tape := (j : Port p q v) → Fin (width p q v j) → Bool

def localEval {e : ℕ} (seat : Visible p q v ↪ B e) (x : B e → ℕ → Bool) : F :=
  Transcript.sample ((q.contract G.units).table v)
    (fun j => let y := (visibleBits p q v).symm j; x (seat y.1) y.2.val)

def tape {e : ℕ} (seat : Visible p q v ↪ B e) (x : B e → ℕ → Bool)
    (z : Inner q v → Bool) : Tape p q v
  | .inl j, b => x (seat j) b.val
  | .inr j, b => z (j, b)

def previous (f : Tape p q v) (i : Live q v) : F :=
  let m := oldMap p q v i.val i.property.2
  (History.original S (oldLabel p i.val)).weight
    (fun j t => f (m.slot j t.pos) (t.cast (m.size _ _).symm))

def inBits (f : Tape p q v) (t : Bool) (j : Fin u) (i : G.E) : Bool :=
  if h : demandSite q i t = v then f (demand p q v i t h) j else false

def outBits (f : Tape p q v) (j : Fin u) (i : q.wire) : Bool :=
  if h : supplySite q i false = v then
    f (supply p q v i false h) (j.cast (width_supply p q v i false h).symm)
  else if h : supplySite q i true = v then
    f (supply p q v i true h) (j.cast (width_supply p q v i true h).symm)
  else false

def created (f : Tape p q v) : F :=
  ∏ j : Fin u, q.rule.entry () v (inBits p q v f false j) (inBits p q v f true j) (outBits p q v f j)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # The contracted station as a local sum of products -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Packing Coloring
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} (p : S.Posting r G)
  {B' W : ℝ} {Hcap D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D)
  (v : Cell a × q.vertex)

private theorem created_eq (w : Bit (cluster q) → Bool) :
    created p q v (fun i t => w (bit p q v i t)) = factor (cluster q) (.inr v) w := by
  rw [new_factor]
  apply Finset.prod_congr rfl
  intro j _
  apply q.rule.local'
  · intro i hi
    change demandSite q i false = v at hi
    rw [inBits, dite_eq_left hi]
    exact congrArg w (address_demand_new p q v i false hi j).symm
  · intro i hi
    change demandSite q i true = v at hi
    rw [inBits, dite_eq_left hi]
    exact congrArg w (address_demand_new p q v i true hi j).symm
  · intro i hi
    by_cases hs : supplySite q i false = v
    · rw [outBits, dite_eq_left hs]
      exact congrArg w (address_supply p q v i false hs j).symm
    have ht : supplySite q i true = v := hi.resolve_left hs
    rw [outBits, dite_eq_right hs, dite_eq_left ht]
    exact congrArg w (address_supply p q v i true ht j).symm

private def coord : (i : Port p q v) → Fin (width p q v i) → Exposed p q v ⊕ Inner q v
  | .inl j, b => .inl ⟨j, b⟩
  | .inr j, b => .inr (j, b)

private def history : History F (Exposed p q v) where
  A := Live q v ⊕ Unit
  E := Inner q v
  I _ := Exposed p q v ⊕ Inner q v
  value i b :=
    let f := fun j t => b (coord p q v j t)
    Sum.elim (previous p q v f) (fun _ => created p q v f) i
  read _ := id

private def atom : Live q v ⊕ Unit ↪ {t // (cluster q).owner t = v} where
  toFun := Sum.elim (fun i => ⟨.inl i.val, i.property.2⟩) (fun _ => ⟨.inr v, rfl⟩)
  inj' := by
    rintro (i|⟨⟩) (j|⟨⟩) e
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj (congrArg Subtype.val e)))
    · cases congrArg Subtype.val e
    · cases congrArg Subtype.val e
    · rfl

variable (hn : ∀ w, G.diagram.arity w = 0 → ∀ z, Transcript.sample (G.diagram.table w) z = 1)

set_option maxHeartbeats 1800000
local instance : Fintype ((before q).Between (Sum.elim (q.assign G.units ()) id)) :=
  (q.contract G.units).fe

private def exposed : (cluster q).collapse.Port v ≃ Exposed p q v := (visibleBits p q v).symm

private def traces : Traces (cluster q) (history p q v) v (exposed p q v) where
  atom := atom q v
  hidden := hiddenBits q v
  entry i w := by
    have he : (fun j t => w (embed (cluster q) (history p q v) v
        (exposed p q v) (hiddenBits q v) (coord p q v j t))) =
        (fun j t => w (bit p q v j t)) := by
      funext j t
      cases j with
      | inl j => exact congrArg (w ∘ Sum.inl) (visible_pin p q v ⟨j, t⟩)
      | inr j => rfl
    change Sum.elim (previous p q v _) (fun _ => created p q v _) i = _
    erw [he]
    cases i with
    | inl i => exact (oldMap p q v i.val i.property.2).value w
    | inr i => exact created_eq p q v w
  idle := by
    rintro ⟨i|j, h⟩ hi w
    · have hz : G.diagram.arity i = 0 := Nat.eq_zero_of_not_pos
        (fun hp => hi ⟨.inl ⟨i, hp, h⟩, rfl⟩)
      exact (old_factor q w i).trans (hn i hz _)
    · change j = v at h
      subst j
      exact (hi ⟨.inr (), rfl⟩).elim

include hn in
theorem eval_formula {e : ℕ} (seat : Visible p q v ↪ B e) (x : B e → ℕ → Bool) :
    localEval p q v seat x = ∑ z : Inner q v → Bool,
      (∏ i : Live q v, previous p q v (tape p q v seat x z) i) * created p q v (tape p q v seat x z) := by
  let a (j : Exposed p q v) := x (seat j.1) j.2.val
  refine ((traces p q v hn).correct a).symm.trans ?_
  unfold History.eval
  dsimp only [history]
  refine Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) ?_
  intro z _
  have he : (fun j t => Sum.elim a z (coord p q v j t)) = tape p q v seat x z := by
    funext j t
    cases j <;> rfl
  change (∏ i : Live q v ⊕ Unit, Sum.elim (previous p q v _) (fun _ => created p q v _) i) = _
  erw [he, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique]

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # Scalar withdrawal and composition of restoration budgets -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Measure
open Coloring BatchDescent.Phase

variable (i : Measure) (a b : Wire)

def budget (j : ℕ) := 2 ^ i.m * i.long ^ j + 2 ^ (i.m + i.h) * i.short ^ j + (wd a + wd b) * i.outer ^ j

theorem add (k l : ℕ) : i.budget a b k + i.budget a b l ≤ i.budget a b (max k l + 1) := by
  unfold budget
  rw [add_add_add_comm, add_add_add_comm (2 ^ i.m * i.long ^ k), ← mul_add, ← mul_add, ← mul_add]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (Poly.pow_sum i.long_two ..))
    (Nat.mul_le_mul_left _ (Poly.pow_sum i.short_two ..))) (Nat.mul_le_mul_left _ (Poly.pow_sum i.two ..))

def sweep :=
  let k := (script i.A.scheme).width
  2 ^ (i.m + i.l) * (4 * (8 * (i.m + i.l)) + 2 ^ i.h * (1 + k + k)) +
    4 * 2 ^ (i.m + i.l) * (2 + 8 * 2 + 2 ^ i.h * k) + 4 * ((i.h + i.snd + 1) * (2 * (2 ^ (i.m + i.l) + wd a + wd b)))

theorem sweep_estimate (u : ℕ) (Q : Rounds.Layer i.F a b)
    (hq : Q.template = result i.A i.N i.r i.s u)
    (hv : Q.volume = 2 ^ (i.m + i.l) + wd a + wd b) (ht : Q.height = i.h + i.snd) :
    Q.encoding.sweepCost ≤ i.sweep a b := by
  have hw := Fmt.width_payload Q.template.scheme.m Q.volume Q.height
  have hd (D : Template i.F) : D.header.width = 2 + 2 ^ D.scheme.d * 2 + 2 ^ D.scheme.h * D.count := by
    simp only [Template.header, Group.Flags, Format.width_vec, Format.width_pair, Format.width_addr]
    rw [Format.width_bit]; ring
  have own : Q.encoding.sweepCost =
      2 ^ Q.template.scheme.m * (4 * (2 ^ Q.template.scheme.d * Q.template.scheme.m)+
        2 ^ Q.template.scheme.h * (1 + Q.template.scheme.ℓ + Q.template.scheme.ℓ)) +
      4 * 2 ^ Q.template.scheme.m * (2 + 2 ^ Q.template.scheme.d * 2 + 2 ^ Q.template.scheme.h * Q.template.count)+
      4 * (Fmt.payload Q.template.scheme.m Q.volume Q.height).width := by
    unfold Encoding.sweepCost updateCost
    rw [Format.width_addr]
    have hc : Q.encoding.extra.width = 2 ^ Q.template.scheme.m * Q.template.header.width :=
      Format.width_vec _ _
    rw [hc, hd, mul_assoc 4]
  rw [own]
  refine (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hw) _).trans_eq ?_
  rw [hq, hv, ht]
  rfl

theorem sweep_bound : ∃ K : ℕ, ∀ (i : Measure) a b, i.sweep a b ≤ i.budget a b K := by
  have cap : Fast (fun i => i.h + i.snd + 1) := small_num fun i => by unfold outer; omega
  have ha := (constant 8).mul cap
  have hb := (constant 32).slow.mul (hosts.add hardware.slow)
  have hc := ((hb.add (constant 72).slow).add (Fast.slow ha)).mul copies.slow
  have hd := ((constant 1).add ((constant 6).mul script_size)).mul copies
  have ho : Poly outer (fun i => 8 * (i.h + i.snd + 1)) :=
    (Poly.const two 8).mul (Poly.of_le two fun i => by unfold outer; omega)
  obtain ⟨l, hl⟩ := hc.bound
  obtain ⟨s, hs⟩ := hd.bound
  obtain ⟨o, hz⟩ := ho.bound
  refine ⟨l + s + o, fun i a b => ?_⟩
  have u := i.long_two
  have v := i.short_two
  have w := i.two
  have hx := (hl i).trans (Nat.pow_le_pow_right (by omega) (show l ≤ l + s + o by omega))
  have hy := (hs i).trans (Nat.pow_le_pow_right (by omega) (show s ≤ l + s + o by omega))
  have hw := (hz i).trans (Nat.pow_le_pow_right (by omega) (show o ≤ l + s + o by omega))
  refine le_trans ?_ (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hx) (Nat.mul_le_mul_left _ hy))
    (Nat.mul_le_mul_left _ hw))
  apply le_of_eq
  simp only [sweep, pow_add]
  ring

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Measure
end
