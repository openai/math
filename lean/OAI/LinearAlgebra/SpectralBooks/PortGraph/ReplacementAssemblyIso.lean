import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementAssembly
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RootedMap

/-! # Relabelling occurrences in a paired assembly

Bijections of occurrences, their internal vertices and wires, and the exterior
wires induce a single bijection of the assembled graphs whenever they carry
the stub pairings to one another.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
namespace PortGraph.StubPairing

universe u
variable {J L : Type u} {S : J → Type u} {D : L → Type u}
  {C : StubPairing S} {C' : StubPairing D} {P : ∀ j, OpenPiece (S j)} {Q : ∀ j, OpenPiece (D j)}

/-- Incidence-preserving coordinate changes on all constituent sets,
including the actual pairing of named, oriented boundary stubs. -/
structure AssemblyIso (C : StubPairing S) (C' : StubPairing D)
    (P : ∀ j, OpenPiece (S j)) (Q : ∀ j, OpenPiece (D j)) where
  occ : J ≃ L
  vertex : ∀ j, (P j).Vertex ≃ (Q (occ j)).Vertex
  wire : ∀ j, (P j).Edge ≃ (Q (occ j)).Edge
  stub : ∀ j, S j ≃ D (occ j)
  outsideWire : C.Wire ≃ C'.Wire
  incidence : ∀ j e b, vertex j ((P j).graph.vertex e b) = (Q (occ j)).graph.vertex (wire j e) b
  attach : ∀ j s, vertex j ((P j).attach s) = (Q (occ j)).attach (stub j s)
  ends : ∀ e b, (Equiv.sigmaCongr occ stub) (C.ends (e,b)) = C'.ends (outsideWire e,b)

namespace AssemblyIso
variable (f : AssemblyIso C C' P Q)

def vertices : Vertex P ≃ Vertex Q := Equiv.sigmaCongr f.occ f.vertex

def edges : C.Edge P ≃ C'.Edge Q := f.outsideWire.sumCongr (Equiv.sigmaCongr f.occ f.wire)

theorem map_incidence (e : C.Edge P) (b : Bool) :
    f.vertices ((C.assemble P).vertex e b) = (C'.assemble Q).vertex (f.edges e) b := by
  rcases e with e | ⟨j,e⟩
  · change _ = (C'.assemble Q).vertex (.inl (f.outsideWire e)) b
    rw [vertex_exterior, vertex_exterior]
    let land (u : Σ j, D j) : Vertex Q := ⟨u.1,(Q u.1).attach u.2⟩
    exact (congrArg (Sigma.mk (f.occ (C.ends (e,b)).1)) (f.attach _ _)).trans
      (congrArg land (f.ends e b))
  · change _ = (C'.assemble Q).vertex (.inr ⟨f.occ j,f.wire j e⟩) b
    rw [vertex_internal,vertex_internal]
    exact congrArg (Sigma.mk _) (f.incidence j e b)

variable [Fintype J] [Fintype L] [DecidableEq (Vertex P)] [DecidableEq (Vertex Q)]

/-- A relabelling of all the assembly data preserves the rooted map as soon
as the marked root and the port numbers of corresponding ends agree. -/
def rootedIso (M : RootedMap (Vertex P) (C.Edge P)) (H : RootedMap (Vertex Q) (C'.Edge Q))
    (src : M.graph = C.assemble P) (dst : H.graph = C'.assemble Q)
    (root : f.vertices M.root = H.root)
    (number : ∀ e b, M.portNumber e b = H.portNumber (f.edges e) b) : M.Iso H :=
  ⟨f.vertices,f.edges,fun e b => by rw [src,dst]; exact f.map_incidence e b,root,number⟩

omit [Fintype J] [Fintype L] [DecidableEq (Vertex P)] [DecidableEq (Vertex Q)] in
/-- A label with a component depending on its record and index transports
with its actual local vertex. -/
theorem labels_eq {B : Type*} (z : ∀ j, (P j).Vertex → B) (w : ∀ j, (Q j).Vertex → B)
    (h : ∀ j v, z j v = w (f.occ j) (f.vertex j v)) (v : Vertex P) :
    z v.1 v.2 = w (f.vertices v).1 (f.vertices v).2 := h _ _

end AssemblyIso
end PortGraph.StubPairing

end

end SpectralBooks
end LinearAlgebra
end OAI
