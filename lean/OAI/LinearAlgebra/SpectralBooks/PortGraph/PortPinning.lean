import OAI.LinearAlgebra.SpectralBooks.PortNetwork
import Mathlib.Logic.Relation

/-!
# Pinning a connected rooted port graph by local names

If the vertex and edge names form a local bijection onto a connected graph,
every name has the same fiber size. Having exactly one preimage of the root
forces a global isomorphism. Distinct port numbers at a vertex make this
root-preserving naming unique, including edge names in a multigraph.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PortGraph

variable {V E W D : Type*} {G : PortGraph V E} {H : PortGraph W D}

/-- One can move across a wire in either direction. -/
def Adj (G : PortGraph V E) (x y : V) : Prop :=
  ∃ e : E, ∃ b : Bool, G.vertex e b = x ∧ G.vertex e (!b) = y

/-- All vertices are reachable from the distinguished root. -/
def ConnectedFrom (G : PortGraph V E) (root : V) : Prop :=
  ∀ v, Relation.ReflTransGen G.Adj root v

/-- A consistent naming is a local bijection on incident ports, preserving
incoming and outgoing directions. -/
structure Covering (G : PortGraph V E) (H : PortGraph W D) where
  vertexName : V → W
  edgeName : E → D
  incidence : ∀ e b, vertexName (G.vertex e b) = H.vertex (edgeName e) b
  lift : ∀ (d : D) (b : Bool) (v : V), vertexName v = H.vertex d b →
    ∃! e : E, G.vertex e b = v ∧ edgeName e = d

namespace Covering

private theorem unique_next (f : Covering G H) {x y : W}
    (hx : ∃! v, f.vertexName v = x) (hxy : H.Adj x y) : ∃! v, f.vertexName v = y := by
  obtain ⟨d,b,rfl,rfl⟩ := hxy
  obtain ⟨v,hv,hu⟩ := hx
  obtain ⟨e,he,heu⟩ := f.lift d b v hv
  refine ⟨G.vertex e (!b), (f.incidence _ _).trans (by rw [he.2]), ?_⟩
  intro u huf
  obtain ⟨e',he',_⟩ := f.lift d (!b) u huf
  have htail : G.vertex e' b = v := hu _ ((f.incidence _ _).trans (by rw [he'.2]))
  have ee : e' = e := heu _ ⟨htail, he'.2⟩
  exact he'.1.symm.trans (congrArg (fun t => G.vertex t (!b)) ee)

/-- With a single root preimage the fiber of each other vertex is a singleton. -/
theorem unique_vertex (f : Covering G H) {r : W} (connected : H.ConnectedFrom r)
    (root : ∃! v, f.vertexName v = r) (x : W) : ∃! v, f.vertexName v = x := by
  induction connected x with
  | refl => exact root
  | tail _ hxy ih => exact unique_next f ih hxy

/-- The local tests uniquely identify both endpoints and wires of the pinned graph. -/
theorem bijective_names (f : Covering G H) {r : W} (connected : H.ConnectedFrom r)
    (root : ∃! v, f.vertexName v = r) :
    Function.Bijective f.vertexName ∧ Function.Bijective f.edgeName := by
  have verts := f.unique_vertex connected root
  have edges (d : D) : ∃! e, f.edgeName e = d := by
    obtain ⟨v,hv,hu⟩ := verts (H.tail d)
    obtain ⟨e,he,heu⟩ := f.lift d false v hv
    refine ⟨e, he.2, fun e' he' => heu _ ⟨hu _ ((f.incidence _ false).trans (by rw [he']; rfl)), he'⟩⟩
  exact ⟨(Function.bijective_iff_existsUnique _).mpr verts, (Function.bijective_iff_existsUnique _).mpr edges⟩

/-- Number the two kinds of ports at each vertex. Two consistent namings
agree at the root, and each port then determines the unique next edge and
vertex name. -/
theorem names_unique (f g : Covering G H) (label : D → Bool → ℕ)
    (local_inj : ∀ e d b, H.vertex e b = H.vertex d b → label e b = label d b → e = d)
    (sameLabels : ∀ e b, label (f.edgeName e) b = label (g.edgeName e) b)
    {r : V} (connected : G.ConnectedFrom r) (root : f.vertexName r = g.vertexName r) :
    f.vertexName = g.vertexName ∧ f.edgeName = g.edgeName := by
  have atEdge (e : E) (b : Bool) (h : f.vertexName (G.vertex e b) = g.vertexName (G.vertex e b)) :
      f.edgeName e = g.edgeName e :=
    local_inj _ _ _ ((f.incidence _ _).symm.trans (h.trans (g.incidence _ _))) (sameLabels _ _)
  have v (x : V) : f.vertexName x = g.vertexName x := by
    induction connected x with
    | refl => exact root
    | tail _ hxy ih =>
      obtain ⟨e,b,rfl,rfl⟩ := hxy
      rw [f.incidence, g.incidence, atEdge e b ih]
  exact ⟨funext v, funext fun e => atEdge e false (v _)⟩

end Covering
end PortGraph

end SpectralBooks
end LinearAlgebra
end OAI
