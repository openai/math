import OAI.LinearAlgebra.SpectralBooks.PortGraph.MapType
import OAI.LinearAlgebra.SpectralBooks.PlanarCertSize.PlanarCertificateSize
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarNamingCertificates
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarNumberedRotation
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPortEuler

/-! # The finite set of rooted, numbered spherical maps

A map includes the edge directions and the consecutive numbers of all ports.
A drawing supplies no extra data. The root and port numbers make the
isomorphism between any two named presentations unique.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph

variable {V E W D X Y : Type*}

/-- A connected, rooted, oriented multigraph with at most four numbered ports
at each vertex. The root supplies a vertex even when the graph has no edges. -/
structure RootedMap (V E : Type*) [Fintype V] [Fintype E] [DecidableEq V] where
  graph : PortGraph V E
  root : V
  num : graph.Numbering
  degree : ∀ v, Fintype.card (graph.Port v) ≤ 4
  connected : graph.ConnectedFrom root

namespace RootedMap

variable [Fintype V] [Fintype E] [DecidableEq V]
variable [Fintype W] [Fintype D] [DecidableEq W]
variable [Fintype X] [Fintype Y] [DecidableEq X]
variable (M : RootedMap V E) (H : RootedMap W D)

/-- The genus of the rotation determined by the numbering is zero. -/
def Spherical [DecidableEq E] : Prop := M.num.rotation.picture.GenusZero

/-- The root flag and port directions read in order of the port numbers. -/
def typeAt (v : V) : MapType where
  degree := ⟨_, Nat.lt_succ_of_le (M.degree v)⟩
  root := decide (v = M.root)
  direction i := ((M.num v).symm i).val.2

/-- Number of the given end of an oriented edge at its incident vertex. -/
def portNumber (e : E) (b : Bool) : ℕ := (M.num _ ⟨(e,b),rfl⟩).val

theorem portNumber_injective {e d : E} {b : Bool}
    (hv : M.graph.vertex e b = M.graph.vertex d b)
    (hn : M.portNumber e b = M.portNumber d b) : e = d := by
  have h := port_eq_of_number_eq' ⟨(e,b),rfl⟩ ⟨(d,b),rfl⟩ hv hn
  exact congrArg Prod.fst h
where
  port_eq_of_number_eq' {v w : V} (p : M.graph.Port v) (q : M.graph.Port w)
      (h : v = w) (hs : (M.num v p).val = (M.num w q).val) : p.val = q.val := by
    subst w
    exact congrArg Subtype.val ((M.num v).injective (Fin.ext hs))

/-- A named presentation satisfies the graph-level Euler test exactly when it
is spherical, including the convention at an isolated root. -/
theorem spherical_iff_euler [DecidableEq E] [LinearOrder (E × Bool)]
    {record : E × Bool → (E × Bool) × ℕ}
    (h : PlanarFace.Valid M.num.rotation.picture.face record) :
    M.Spherical ↔ (Fintype.card V : ℤ) - Fintype.card E + PlanarFace.faceCount record = 2 :=
  (M.num.rotation.certifiedEuler_iff_genusZero
    (PlanarPatch.underlying_connected_of_connectedFrom _ _ M.connected) h).symm

/-- A map isomorphism preserves the root, orientation, and each port number. -/
@[ext] structure Iso where
  vertex : V ≃ W
  edge : E ≃ D
  incidence : ∀ e b, vertex (M.graph.vertex e b) = H.graph.vertex (edge e) b
  root : vertex M.root = H.root
  number : ∀ e b, M.portNumber e b = H.portNumber (edge e) b

namespace Iso

variable {M H} {T : RootedMap X Y}

def refl (M : RootedMap V E) : Iso M M :=
  ⟨Equiv.refl _, Equiv.refl _, fun _ _ => rfl, rfl, fun _ _ => rfl⟩

def symm (f : Iso M H) : Iso H M where
  vertex := f.vertex.symm
  edge := f.edge.symm
  incidence e b := by
    apply f.vertex.injective
    simpa using (f.incidence (f.edge.symm e) b).symm
  root := f.vertex.symm_apply_eq.mpr f.root.symm
  number e b := by simpa using (f.number (f.edge.symm e) b).symm

def trans (f : Iso M H) (g : Iso H T) : Iso M T where
  vertex := f.vertex.trans g.vertex
  edge := f.edge.trans g.edge
  incidence e b := (congrArg g.vertex (f.incidence e b)).trans (g.incidence _ _)
  root := (congrArg g.vertex f.root).trans g.root
  number e b := (f.number e b).trans (g.number _ _)

/-- The isomorphism supplies the incidence-by-incidence covering used in
the pinning argument. -/
def covering (f : Iso M H) : Covering M.graph H.graph where
  vertexName := f.vertex
  edgeName := f.edge
  incidence := f.incidence
  lift d b v hv := by
    refine ⟨f.edge.symm d, ⟨f.vertex.injective ?_, f.edge.apply_symm_apply _⟩, ?_⟩
    · simpa [f.incidence] using hv.symm
    · exact fun e he => f.edge.eq_symm_apply.mpr he.2

/-- Pinning identifies even parallel edges and the separate ports of loops. -/
instance : Subsingleton (Iso M H) where
  allEq f g := by
    obtain ⟨hv,he⟩ := f.covering.names_unique g.covering H.portNumber
      (fun _ _ _ => H.portNumber_injective) (fun e b => (f.number e b).symm.trans (g.number e b))
      M.connected (f.root.trans g.root.symm)
    exact Iso.ext (Equiv.ext (congrFun hv)) (Equiv.ext (congrFun he))

/-- A consistent covering preserving the numbered ports, with exactly one
preimage of the root, identifies the two maps. -/
def ofCovering (f : Covering M.graph H.graph) (root : f.vertexName M.root = H.root)
    (pinned : ∃! v, f.vertexName v = H.root)
    (number : ∀ e b, M.portNumber e b = H.portNumber (f.edgeName e) b) :
    Iso M H :=
  let h := f.bijective_names H.connected pinned
  ⟨Equiv.ofBijective _ h.1, Equiv.ofBijective _ h.2, f.incidence, root, number⟩

end Iso

private instance : Finite (PortGraph V E) :=
  Finite.of_injective (fun G : PortGraph V E => (G.tail, G.head)) (by
    rintro ⟨_,_⟩ ⟨_,_⟩ h
    simpa using h)

instance : Finite (RootedMap V E) :=
  Finite.of_injective (fun M : RootedMap V E => (⟨M.graph, (M.root, M.num)⟩ :
    Σ G : PortGraph V E, V × G.Numbering)) (by
      rintro ⟨G,r,n,d,c⟩ ⟨G',r',n',d',c'⟩ h
      cases h
      rfl)

end RootedMap

/-- A representative with finite integer vertex and edge names. Both
cardinalities are bounded because each edge uses two ports. -/
structure MapRep (N : ℕ) where
  vertexCount : Fin (N+1)
  edgeCount : Fin (2*N+1)
  map : RootedMap (Fin vertexCount.val) (Fin edgeCount.val)
  spherical : map.Spherical

namespace MapRep

variable {N : ℕ}

instance : Finite (MapRep N) :=
  Finite.of_injective (fun M : MapRep N => (⟨M.vertexCount, M.edgeCount, M.map⟩ :
    Σ n : Fin (N+1), Σ e : Fin (2*N+1), RootedMap (Fin n.val) (Fin e.val))) (by
      rintro ⟨v,e,m,h⟩ ⟨v',e',m',h'⟩ h
      cases h
      rfl)

def isoSetoid (N : ℕ) : Setoid (MapRep N) where
  r M H := Nonempty (RootedMap.Iso M.map H.map)
  iseqv := ⟨fun M => ⟨.refl M.map⟩, fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

end MapRep

/-- The manuscript's finite set `𝓜_N` of spherical maps up to isomorphism. -/
abbrev MapClass (N : ℕ) := Quotient (MapRep.isoSetoid N)

namespace MapClass

variable {N : ℕ}

noncomputable instance : Fintype (MapClass N) := Fintype.ofFinite _

/-- Equality of map classes is equivalent to an incidence-, numbering-, and
root-preserving isomorphism of their representatives. -/
theorem eq_iff_iso (M H : MapRep N) :
    (Quotient.mk (MapRep.isoSetoid N) M = Quotient.mk _ H) ↔ Nonempty (RootedMap.Iso M.map H.map) :=
  Quotient.eq

end MapClass
end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
