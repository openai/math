import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortPatchSubstitution
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortPinning

/-!
# Assembling patches by their named boundary ports

The cut wires and their attachment to the *named stubs* survive replacement.
The vertex at a stub can change. A single boundary pairing therefore specifies
both the old and new closed graphs, even in configurations with parallel wires
or loops inside a patch. Each cut wire has exactly one tail and one head.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PortGraph

universe u

/-- The incidence data of a finite patch, with one attachment vertex per
named stub. -/
structure OpenPiece (S : Type u) where
  Vertex : Type u
  Edge : Type u
  graph : PortGraph Vertex Edge
  attach : S → Vertex
  [vertexFintype : Fintype Vertex]
  [edgeFintype : Fintype Edge]

attribute [instance] OpenPiece.vertexFintype OpenPiece.edgeFintype

/-- A pairing of the stubs of the different occurrences. The equivalence
keeps both ports of every exterior edge and precludes dangling stubs. -/
structure StubPairing {J : Type u} (S : J → Type u) where
  Wire : Type u
  [wireFintype : Fintype Wire]
  ends : Wire × Bool ≃ Σ j, S j
  cross : ∀ e, (ends (e,false)).1 ≠ (ends (e,true)).1

attribute [instance] StubPairing.wireFintype

namespace StubPairing

variable {J : Type u} {S : J → Type u} (C : StubPairing S) (P : ∀ j, OpenPiece (S j))

/-- One copy of every piece vertex. -/
abbrev Vertex := Σ j, (P j).Vertex

/-- Retain the single set of exterior wires and allocate disjoint copies
of the wires internal to each occurrence. -/
abbrev Edge := C.Wire ⊕ Σ j, (P j).Edge

/-- The landing site of either end of a cut wire. -/
def outside (e : C.Wire) (b : Bool) : Vertex P :=
  ⟨(C.ends (e,b)).1, (P _).attach (C.ends (e,b)).2⟩

/-- Gluing along the pairing gives an oriented multigraph. -/
def assemble : PortGraph (Vertex P) (C.Edge P) where
  tail
    | .inl e => C.outside P e false
    | .inr ⟨j,e⟩ => ⟨j, (P j).graph.tail e⟩
  head
    | .inl e => C.outside P e true
    | .inr ⟨j,e⟩ => ⟨j, (P j).graph.head e⟩

@[simp] theorem vertex_exterior (e : C.Wire) (b : Bool) :
    (C.assemble P).vertex (.inl e) b = C.outside P e b := by cases b <;> rfl

@[simp] theorem vertex_internal (j : J) (e : (P j).Edge) (b : Bool) :
    (C.assemble P).vertex (.inr ⟨j,e⟩) b = ⟨j, (P j).graph.vertex e b⟩ := by cases b <;> rfl

/-- The cut wires of the assembled graph are exactly the original paired
wires. In particular deleting the internal wires does not identify any
parallel cut edges. -/
def exteriorEquiv : C.Wire ≃ (C.assemble P).CrossEdge Sigma.fst where
  toFun e := ⟨.inl e, C.cross e⟩
  invFun e := match e with
    | ⟨.inl e,_⟩ => e
    | ⟨.inr ⟨_,_⟩, h⟩ => False.elim (h rfl)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨e,h⟩
    rcases e with e | ⟨j,e⟩
    · rfl
    · exact False.elim (h rfl)

/-- The internal wires of an assembled occurrence recover its local wire
set, with loops retained. -/
def internalEquiv (j : J) : (P j).Edge ≃ (C.assemble P).PatchInternal Sigma.fst j where
  toFun e := ⟨.inr ⟨j,e⟩, rfl, rfl⟩
  invFun
    | ⟨.inl e,ht,hh⟩ => False.elim (C.cross e (ht.trans hh.symm))
    | ⟨.inr ⟨k,e⟩,ht,_⟩ => (show k = j from ht) ▸ e
  left_inv _ := rfl
  right_inv := by
    rintro ⟨e,ht,hh⟩
    rcases e with e | ⟨k,e⟩
    · exact False.elim (C.cross e (ht.trans hh.symm))
    · change k = j at ht
      subst k
      rfl

/-- Relabel a global dart by its occurrence and its local internal dart
or stub. -/
def dartEquiv : C.Edge P × Bool ≃ Σ j, (((P j).Edge × Bool) ⊕ S j) where
  toFun
    | (.inl e,b) => ⟨(C.ends (e,b)).1,.inr (C.ends (e,b)).2⟩
    | (.inr ⟨j,e⟩,b) => ⟨j,.inl (e,b)⟩
  invFun
    | ⟨_,.inr s⟩ => let q := C.ends.symm ⟨_,s⟩; (.inl q.1,q.2)
    | ⟨j,.inl (e,b)⟩ => (.inr ⟨j,e⟩,b)
  left_inv := by
    rintro ⟨e,b⟩
    rcases e with e | ⟨j,e⟩
    · simp
    · rfl
  right_inv := by
    rintro ⟨j,(⟨e,b⟩ | s)⟩
    · rfl
    · change (fun d : Σ j, S j => (⟨d.1, Sum.inr d.2⟩ : Σ j, (((P j).Edge × Bool) ⊕ S j)))
        (C.ends (C.ends.symm ⟨j,s⟩)) = _
      rw [Equiv.apply_symm_apply]

/-- The local vertex of an internal dart or named stub. -/
def owner (j : J) : ((P j).Edge × Bool) ⊕ S j → (P j).Vertex
  | .inl (e,b) => (P j).graph.vertex e b
  | .inr s => (P j).attach s

theorem dartEquiv_owner (q : C.Edge P × Bool) :
    (C.assemble P).vertex q.1 q.2 =
      ⟨(C.dartEquiv P q).1, owner P _ (C.dartEquiv P q).2⟩ := by
  rcases q with ⟨(e | ⟨j,e⟩),b⟩ <;> cases b <;> rfl

private def localFiber {D V : J → Type u} (f : (j : J) → D j → V j) (j : J) (v : V j) :
    {q : Σ j, D j // (⟨q.1,f q.1 q.2⟩ : Σ j, V j) = ⟨j,v⟩} ≃ {d : D j // f j d = v} where
  toFun := by
    rintro ⟨⟨k,d⟩,h⟩
    obtain rfl : k = j := congrArg Sigma.fst h
    exact ⟨d, (Sigma.mk.inj_iff.mp h).2.eq⟩
  invFun d := ⟨⟨j,d.1⟩, congrArg (Sigma.mk j) d.2⟩
  left_inv := by
    rintro ⟨⟨k,d⟩,h⟩
    obtain rfl : k = j := congrArg Sigma.fst h
    rfl
  right_inv _ := rfl

/-- At an assembled vertex the local ports consist exactly of the internal
ports and the stubs attached at that vertex. -/
def portEquiv (j : J) (v : (P j).Vertex) :
    (C.assemble P).Port ⟨j,v⟩ ≃ (P j).graph.Port v ⊕ {s : S j // (P j).attach s = v} :=
  ((C.dartEquiv P).subtypeEquiv (fun q => by rw [C.dartEquiv_owner P q])).trans
    ((localFiber (owner P) j v).trans Equiv.subtypeSum)

end StubPairing
end PortGraph

end SpectralBooks
end LinearAlgebra
end OAI
