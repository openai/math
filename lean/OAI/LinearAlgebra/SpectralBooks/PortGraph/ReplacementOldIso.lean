import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementAssemblyIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementPairRecovery

/-! # Reindexing an assembly of old records

An occurrence bijection carrying the saved records and paired boundary stubs
induces an isomorphism of the expanded numbered maps. The local vertex
coordinates, labels, and numbered ports are preserved.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace PortGraph.PatchRecord

variable {A J L : Type} {K : ℕ}

def castVertex {U V : PatchRecord K A} (h : U = V) : U.shape.Vertex ≃ V.shape.Vertex :=
  Equiv.cast (congrArg (fun X : PatchRecord K A => X.shape.Vertex) h)

def castWire {U V : PatchRecord K A} (h : U = V) : U.shape.Wire ≃ V.shape.Wire :=
  Equiv.cast (congrArg (fun X : PatchRecord K A => X.shape.Wire) h)

/-- Reindexing data for occurrences and for the surviving exterior wires. -/
structure Reindexing (R : J → PatchRecord K A) (S : L → PatchRecord K A)
    (P : StubPairing (fun j => (R j).shape.Stub)) (Q : StubPairing (fun i => (S i).shape.Stub)) where
  occ : J ≃ L
  saved : ∀ j, R j = S (occ j)
  wire : P.Wire ≃ Q.Wire
  ends : ∀ e b, Equiv.sigmaCongr occ (fun j => castStub (saved j)) (P.ends (e,b)) = Q.ends (wire e,b)

namespace Reindexing

variable {R : J → PatchRecord K A} {S : L → PatchRecord K A}
  {P : StubPairing (fun j => (R j).shape.Stub)} {Q : StubPairing (fun i => (S i).shape.Stub)}
  (d : Reindexing R S P Q)

private theorem cast_incidence {U V : PatchRecord K A} (h : U = V) (e : U.shape.Wire) (b : Bool) :
    castVertex h (U.toPiece.graph.vertex e b) = V.toPiece.graph.vertex (castWire h e) b := by
  subst V
  rfl

private theorem cast_attach {U V : PatchRecord K A} (h : U = V) (s : U.shape.Stub) :
    castVertex h (U.toPiece.attach s) = V.toPiece.attach (castStub h s) := by subst V; rfl

/-- The occurrence change of coordinates on all vertices, wires and stubs. -/
def assembly : StubPairing.AssemblyIso P Q (pieces R) (pieces S) where
  occ := d.occ
  vertex j := castVertex (d.saved j)
  wire j := castWire (d.saved j)
  stub j := castStub (d.saved j)
  outsideWire := d.wire
  incidence j := cast_incidence (d.saved j)
  attach j := cast_attach (d.saved j)
  ends := d.ends

theorem vertex_index (v : vertices R) : (d.assembly.vertices v).2.val = v.2.val := by
  have aux {U V : PatchRecord K A} (h : U = V) (i : U.shape.Vertex) : (castVertex h i).val = i.val := by
    subst V
    rfl
  exact aux (d.saved v.1) v.2

theorem labels (v : vertices R) : PatchRecord.labels R v = PatchRecord.labels S (d.assembly.vertices v) := by
  have aux {U V : PatchRecord K A} (h : U = V) (i : U.shape.Vertex) : U.label i = V.label (castVertex h i) := by
    subst V
    rfl
  exact aux (d.saved v.1) v.2

theorem vertex_type (v : vertices R) :
    (R v.1).shape.typeAt v.2 = (S (d.assembly.vertices v).1).shape.typeAt (d.assembly.vertices v).2 := by
  have aux {U V : PatchRecord K A} (h : U = V) (i : U.shape.Vertex) :
      U.shape.typeAt i = V.shape.typeAt (castVertex h i) := by subst V; rfl
  exact aux (d.saved v.1) v.2

theorem port_slot (e : P.Edge (pieces R)) (b : Bool) :
    (namedDarts R P (e,b)).2.val = (namedDarts S Q (d.assembly.edges e,b)).2.val := by
  rcases e with e | ⟨j,e⟩
  · have slot {U V : PatchRecord K A} (h : U = V) (s : U.shape.Stub) :
        s.val.2.val = (castStub h s).val.2.val := by subst V; rfl
    let number (t : Σ i, (S i).shape.Stub) := t.2.val.2.val
    exact (slot (d.saved _) (P.ends (e,b)).2).trans (congrArg number (d.ends e b))
  · have slot {U V : PatchRecord K A} (h : U = V) (x : U.shape.Wire) :
        (U.shape.read (.inl (x,b))).2.val = (V.shape.read (.inl (castWire h x,b))).2.val := by subst V; rfl
    exact slot (d.saved j) e

variable [Fintype J] [Fintype L] (r : vertices R) (s : vertices S)
  (conn : (graph R P).ConnectedFrom r) (conn' : (graph S Q).ConnectedFrom s)

/-- Agreement between saved and actual types identifies the two marked roots. -/
theorem root_of_types
    (types : ∀ v, (asMap R P r conn).typeAt v = (R v.1).shape.typeAt v.2)
    (types' : ∀ v, (asMap S Q s conn').typeAt v = (S v.1).shape.typeAt v.2) :
    d.assembly.vertices r = s := by
  have h := congrArg MapType.root (((types r).trans (d.vertex_type r)).trans (types' _).symm)
  change decide (r = r) = decide (d.assembly.vertices r = s) at h
  simpa using h.symm

/-- A change of occurrence names and exterior wire names yields an actual
rooted, oriented, port-number-preserving isomorphism of the old maps. -/
def iso (root : d.assembly.vertices r = s) :
    (asMap R P r conn).Iso (asMap S Q s conn') :=
  d.assembly.rootedIso _ _ rfl rfl root fun e b =>
    ((asMap_portNumber R P r conn e b).trans (d.port_slot e b)).trans
      (asMap_portNumber S Q s conn' _ b).symm

end Reindexing
end PortGraph.PatchRecord

end

end SpectralBooks
end LinearAlgebra
end OAI
