import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementDecoder
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementAssembly

/-! # Labelling a forward tree replacement

Each occurrence chooses its record and list index. The occurrence identifier
is recoverable from this tag since distinct old patches have distinct patch
identifiers. Ports inherit their numbers from the chosen trees and each paired
stub retains its saved direction. These data give the local decoder tests on
the assembled graph and recover the original occurrences and boundary pairing.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace PortGraph.ReplacementTemplate

universe u
variable {O J : Type u} {T : J → ReplacementTemplate.{u,u,u}}
  [∀ j, Fintype (T j).Role] [∀ j, Fintype (T j).Wire]

/-- The open combinatorial piece associated to a tree template. -/
def piece (t : ReplacementTemplate.{u,u,u}) [Fintype t.Role] [Fintype t.Wire] : OpenPiece t.Stub where
  Vertex := t.Role
  Edge := t.Wire
  graph := t.graph
  attach := t.attach

namespace Forward

variable (tag : O ↪ J) (C : StubPairing (fun i => (T (tag i)).Stub))

abbrev pieces (i : O) := piece (T (tag i))

abbrev graph := C.assemble (pieces (T := T) tag)

/-- The forward decoration retains the list index inside the tag, while
erasing the separate occurrence coordinate. -/
def label (v : StubPairing.Vertex (pieces (T := T) tag)) : Σ j, (T j).Role :=
  ⟨tag v.1,v.2⟩

/-- Retain the template tag on an occurrence-indexed name. -/
def liftTag (F : J → Type u) : (Σ i, F (tag i)) ↪ (Σ j, F j) :=
  tag.sigmaMap (fun _ => Function.Embedding.refl _)

/-- The tree dart or old stub named by an assembled dart. -/
def namedEnd : C.Edge (pieces (T := T) tag) × Bool → End T
  | (.inl e,b) => .inr (liftTag tag _ (C.ends (e,b)))
  | (.inr q,b) => .inl (liftTag tag _ q,b)

private theorem namedEnd_inj : Function.Injective (namedEnd tag C) := by
  rintro ⟨(e | d), b⟩ ⟨(f | a), c⟩ h
  · have h' := C.ends.injective ((liftTag tag _).injective (Sum.inr.inj h))
    cases h'
    rfl
  · simp [namedEnd] at h
  · simp [namedEnd] at h
  · have hd : d = a := (liftTag tag _).injective (congrArg Prod.fst (Sum.inl.inj h))
    have hb : b = c := congrArg Prod.snd (Sum.inl.inj h)
    cases hd
    cases hb
    rfl

theorem namedEnd_owner (q : C.Edge (pieces (T := T) tag) × Bool) :
    owner T (namedEnd tag C q) = label tag ((graph tag C).vertex q.1 q.2) := by
  rcases q with ⟨(e | ⟨i,d⟩), b⟩ <;> cases b <;> rfl

/-- The map to template ends from the ports at an assembled vertex. -/
def portRole (v : StubPairing.Vertex (pieces (T := T) tag)) :
    (graph tag C).Port v ↪ RolePort T (label tag v) where
  toFun p := ⟨namedEnd tag C p.val,
    (namedEnd_owner tag C p.val).trans (congrArg (label tag) p.property)⟩
  inj' _ _ h := Subtype.ext (namedEnd_inj tag C (congrArg Subtype.val h))

private theorem portRole_surj (v : StubPairing.Vertex (pieces (T := T) tag)) :
    Function.Surjective (portRole tag C v) := by
  obtain ⟨i,w⟩ := v
  rintro ⟨(⟨⟨j,d⟩,b⟩ | ⟨j,s⟩), h⟩
  · change (⟨j, (T j).graph.vertex d b⟩ : Σ j, (T j).Role) = ⟨tag i,w⟩ at h
    obtain rfl : j = tag i := congrArg Sigma.fst h
    have hw : (T (tag i)).graph.vertex d b = w := (Sigma.mk.inj_iff.mp h).2.eq
    exact ⟨⟨(.inr ⟨i,d⟩,b), (C.vertex_internal (pieces (T := T) tag) i d b).trans (congrArg (Sigma.mk i) hw)⟩, rfl⟩
  · change (⟨j, (T j).attach s⟩ : Σ j, (T j).Role) = ⟨tag i,w⟩ at h
    obtain rfl : j = tag i := congrArg Sigma.fst h
    have hw : (T (tag i)).attach s = w := (Sigma.mk.inj_iff.mp h).2.eq
    let q := C.ends.symm ⟨i,s⟩
    have hq : C.ends (q.1,q.2) = ⟨i,s⟩ := C.ends.apply_symm_apply _
    have hport : (graph tag C).vertex (.inl q.1) q.2 = ⟨i,w⟩ := by
      rw [StubPairing.vertex_exterior]
      unfold StubPairing.outside
      rw [hq]
      exact congrArg (Sigma.mk i) hw
    refine ⟨⟨(.inl q.1,q.2),hport⟩, Subtype.ext ?_⟩
    change Sum.inr (liftTag tag (fun j => (T j).Stub) (C.ends (q.1,q.2))) = _
    rw [hq]
    rfl

variable (slot : Numbering T)

/-- The numbered slots on the assembled vertices read the slots of the
underlying numbered tree role. -/
def numbering : (graph tag C).FourPortNumbering :=
  fun v => (portRole tag C v).trans (slot _)

variable (orient : ∀ (e : C.Wire) (b : Bool),
  (T (tag (C.ends (e,b)).1)).direction (C.ends (e,b)).2 = b)

include orient in
private theorem namedEnd_side (q : C.Edge (pieces (T := T) tag) × Bool) :
    side T (namedEnd tag C q) = q.2 := by
  rcases q with ⟨(e | ⟨i,d⟩), b⟩
  · exact orient e b
  · rfl

include orient in
/-- Every actual slot with its direction, and every prescribed slot, pass
the fixed-tree vertex test. -/
theorem vertexTests (v) : VertexTest T (numbering tag C slot) slot (label tag) v := by
  intro i b
  constructor
  · rintro ⟨p,ha,hb⟩
    exact ⟨portRole tag C v p, ha, (namedEnd_side tag C orient p.val).trans hb⟩
  · rintro ⟨s,ha,hb⟩
    obtain ⟨p,rfl⟩ := portRole_surj tag C v s
    exact ⟨p, ha, (namedEnd_side tag C orient p.val).symm.trans hb⟩

/-- Reading the forward decoration as the decoder does recovers the named
end actually used to define the wiring. -/
theorem readEnd_eq (q : C.Edge (pieces (T := T) tag) × Bool) :
    readEnd (vertexTests tag C slot orient) q.1 q.2 = namedEnd tag C q := by
  let p : (graph tag C).Port ((graph tag C).vertex q.1 q.2) := ⟨q,rfl⟩
  exact congrArg Subtype.val ((slot _).injective
    (readPort_spec (vertexTests tag C slot orient) p).1)

variable {I : Type*} (patchId : J → I) (old : (Σ j, (T j).Stub) → (Σ j, (T j).Stub) → Prop)
  (distinct : Function.Injective (patchId ∘ tag))
  (old_pass : ∀ e : C.Wire, old (liftTag tag _ (C.ends (e,false))) (liftTag tag _ (C.ends (e,true))))

include distinct old_pass in
/-- On an internal wire both endpoints read the same record, index and wire.
On an exterior wire the saved old pair passes the boundary tests. -/
theorem edgeTests (e : C.Edge (pieces (T := T) tag)) :
    PairTest patchId old (readEnd (vertexTests tag C slot orient) e false)
      (readEnd (vertexTests tag C slot orient) e true) := by
  rw [readEnd_eq tag C slot orient (e,false), readEnd_eq tag C slot orient (e,true)]
  cases e with
  | inl e => exact ⟨fun h => C.cross e (distinct h), old_pass e⟩
  | inr a => exact ⟨rfl,rfl,rfl⟩

/-- The decoder indices recover the occurrences by taking the actual vertex
carrying the designated root role of that tree. -/
def occurrences : O ≃ Copies (label (T := T) tag) where
  toFun i := ⟨tag i, ⟨i, (T (tag i)).root⟩, rfl⟩
  invFun c := c.2.val.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨j,⟨i,w⟩,h⟩
    change (⟨tag i,w⟩ : Σ j, (T j).Role) = ⟨j,(T j).root⟩ at h
    obtain rfl : j = tag i := (congrArg Sigma.fst h).symm
    obtain rfl : w = (T (tag i)).root := (Sigma.mk.inj_iff.mp h).2.eq
    rfl

private def copyTags : Copies (label (T := T) tag) ↪ J :=
  ⟨Sigma.fst, by
    intro c d h
    obtain ⟨i,rfl⟩ := (occurrences (T := T) tag).surjective c
    obtain ⟨k,rfl⟩ := (occurrences (T := T) tag).surjective d
    exact congrArg (occurrences (T := T) tag) (tag.injective h)⟩

local notation "validV" => vertexTests tag C slot orient
local notation "validE" => edgeTests tag C slot orient patchId old distinct old_pass

/-- The decoded vertex coordinate is its original occurrence and its original
role, including for a one-vertex tree. -/
theorem vertex_roundTrip (v : StubPairing.Vertex (pieces (T := T) tag)) :
    vertexEquiv validV validE v = ⟨occurrences tag v.1, v.2⟩ :=
  (liftTag (copyTags tag) (fun j => (T j).Role)).injective (vertexEquiv_role validV validE v)

/-- The classified outside wires are the very wires of the given pairing. -/
def exterior : C.Wire ≃ OutsideEdge validV :=
  Equiv.ofBijective (fun e => ⟨.inl e, _, readEnd_eq tag C slot orient (.inl e,false)⟩) <| by
    constructor
    · intro e f h
      exact Sum.inl.inj (congrArg Subtype.val h)
    · rintro ⟨(e | a),hs⟩
      · exact ⟨e,rfl⟩
      · obtain ⟨s,h⟩ := hs
        rw [readEnd_eq tag C slot orient (.inr a,false)] at h
        contradiction

/-- The classified internal wires recover the original occurrence and its
internal wire. -/
def interior : ((i : O) × (T (tag i)).Wire) ≃ InsideEdge validV :=
  Equiv.ofBijective (fun d => ⟨.inr d, _, readEnd_eq tag C slot orient (.inr d,false)⟩) <| by
    constructor
    · intro a d h
      exact Sum.inr.inj (congrArg Subtype.val h)
    · rintro ⟨(e | a),hs⟩
      · obtain ⟨d,h⟩ := hs
        rw [readEnd_eq tag C slot orient (.inl e,false)] at h
        contradiction
      · exact ⟨a,rfl⟩

/-- Decoding a paired endpoint preserves its original old stub, occurrence,
patch record and chosen list index. Thus the boundary pairings agree under
the explicit occurrence and exterior-wire equivalences. -/
theorem ends_roundTrip (e : C.Wire) (b : Bool) :
    endsEquiv validV validE (exterior tag C slot orient e,b) =
      ⟨occurrences tag (C.ends (e,b)).1, (C.ends (e,b)).2⟩ := by
  apply (liftTag (copyTags tag) (fun j => (T j).Stub)).injective
  apply Sum.inr.inj (α := (Σ j, (T j).Wire) × Bool)
  exact (readEnd_stub validV validE (exterior tag C slot orient e) b).symm.trans
    (readEnd_eq tag C slot orient (.inl e,b))

/-- Decoding an internal wire retains its identity within the occurrence. -/
theorem wire_roundTrip (a : (i : O) × (T (tag i)).Wire) :
    wireEquiv validV validE (interior tag C slot orient a) = ⟨occurrences tag a.1,a.2⟩ := by
  apply (liftTag (copyTags tag) (fun j => (T j).Wire)).injective
  have h := (readEnd_wire validV validE (interior tag C slot orient a) false).symm.trans
    (readEnd_eq tag C slot orient (.inr a,false))
  exact congrArg Prod.fst (Sum.inl.inj h)

end Forward
end PortGraph.ReplacementTemplate

end

end SpectralBooks
end LinearAlgebra
end OAI
