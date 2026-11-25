import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortPatchContraction

/-!
# Simultaneous substitution of open tensor networks

A replacement keeps one stub for each original cut edge at each end. Its
internal wires have their own alphabets. Splicing attaches the cut edges at
the prescribed local vertices and retains every internal wire. This applies
in particular to a trivalent tree with boundary stubs.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical
noncomputable section

namespace PortGraph

universe u v w

/-- A finite tensor network with named open stubs. A local entry reads the
internal ports and the open stubs attached at that vertex. -/
structure OpenNetwork (S : Type*) (D : S → Type u) (K : Type*) where
  Vertex : Type v
  Wire : Type w
  graph : PortGraph Vertex Wire
  Index : Wire → Type u
  attach : S → Vertex
  table : (v : Vertex) → graph.State Index v → ((s : {s : S // attach s = v}) → D s.val) → K
  [vertexFintype : Fintype Vertex]
  [wireFintype : Fintype Wire]
  [indexFintype : ∀ e, Fintype (Index e)]

attribute [instance] OpenNetwork.vertexFintype OpenNetwork.wireFintype OpenNetwork.indexFintype

/-- Sum the internal assignments, holding the stub assignment fixed. -/
def OpenNetwork.eval {S K : Type*} {D : S → Type*} [CommSemiring K]
    (T : OpenNetwork S D K) (s : (b : S) → D b) : K :=
  ∑ y : (e : T.Wire) → T.Index e, ∏ v, T.table v (T.graph.atVertex y v) (fun b => s b.val)

variable {V E J K : Type*} (G : PortGraph V E) (p : V → J) {A : E → Type u}

/-- One finite open network for each patch, with the original cut wires as
its boundary and the corresponding original index types on those wires. -/
abbrev PatchNetworks (A : E → Type u) (K : Type*) :=
  (j : J) → OpenNetwork.{u,v,v} (G.PatchBoundary p j) (fun b => A b.1.1) K

variable (T : G.PatchNetworks p A K)

/-- Keep the cut wires, add each new internal wire in its own patch, and
attach each end of each cut wire at its prescribed replacement vertex. -/
def splice : PortGraph ((j : J) × (T j).Vertex)
    (G.CrossEdge p ⊕ ((j : J) × (T j).Wire)) where
  tail
    | .inl e => ⟨p (G.tail e.1), (T _).attach ⟨e, Or.inl rfl⟩⟩
    | .inr ⟨j, e⟩ => ⟨j, (T j).graph.tail e⟩
  head
    | .inl e => ⟨p (G.head e.1), (T _).attach ⟨e, Or.inr rfl⟩⟩
    | .inr ⟨j, e⟩ => ⟨j, (T j).graph.head e⟩

/-- The old alphabet on cut wires and each replacement's alphabet on its
own internal wires. -/
def spliceIndex : G.CrossEdge p ⊕ ((j : J) × (T j).Wire) → Type u
  | .inl e => A e.1
  | .inr ⟨j, e⟩ => (T j).Index e

instance [∀ e, Fintype (A e)] (e) : Fintype (G.spliceIndex p T e) := by
  cases e with
  | inl e => exact inferInstanceAs (Fintype (A e.1))
  | inr e => exact (T e.1).indexFintype e.2

private def spliceInternalPort {j : J} {v : (T j).Vertex} (b : (T j).graph.Port v) :
    (G.splice p T).Port ⟨j, v⟩ :=
  ⟨(.inr ⟨j, b.1.1⟩, b.1.2), by
    obtain ⟨⟨e,i⟩, he⟩ := b
    cases i <;> exact congrArg (Sigma.mk j) he⟩

private def spliceBoundaryPort {j : J} {v : (T j).Vertex}
    (b : {s : G.PatchBoundary p j // (T j).attach s = v}) : (G.splice p T).Port ⟨j, v⟩ :=
  ⟨(.inl b.1.1, if p (G.tail b.1.1.1) = j then false else true), by
    obtain ⟨⟨e, he⟩, rfl⟩ := b
    dsimp only
    split_ifs with h
    · subst j
      rfl
    · obtain ht | rfl := he
      · exact (h ht).elim
      · rfl⟩

/-- Read a table of the spliced graph by indexing the internal ports and
the external ports landing at this vertex. -/
def spliceTable (v : (j : J) × (T j).Vertex) :
    (G.splice p T).State (G.spliceIndex p T) v → K :=
  fun z => (T v.1).table v.2 (fun b => z (G.spliceInternalPort p T b))
    (fun b => z (G.spliceBoundaryPort p T b))

variable [Fintype J] [Fintype E] [∀ e, Fintype (A e)] [CommSemiring K]

/-- Gluing the open network on each patch has exactly the contraction of the
explicit spliced port graph. -/
theorem contraction_splice :
    (G.splice p T).contraction (G.spliceTable p T) =
      ∑ x : (e : G.CrossEdge p) → A e.1, ∏ j, (T j).eval (fun b => x b.1) := by
  unfold contraction OpenNetwork.eval
  simp_rw [Fintype.prod_sum]
  rw [← Fintype.sum_prod_type']
  let : DecidableEq (G.CrossEdge p ⊕ ((j : J) × (T j).Wire)) := Classical.decEq _
  apply Fintype.sum_equiv ((Equiv.sumPiEquivProdPi (G.spliceIndex p T)).trans
    ((Equiv.refl _).prodCongr (Equiv.piCurry (fun j e => (T j).Index e))))
  intro z
  rw [Fintype.prod_sigma]
  rfl

/-- Simultaneous local replacement by a finite sum of open networks yields a
sum of contractions of genuine spliced port graphs. -/
theorem contraction_eq_sum_splices [Fintype V] (U : (v : V) → G.State A v → K)
    (R : J → Type*) [∀ j, Fintype (R j)]
    (N : (j : J) → R j → OpenNetwork (G.PatchBoundary p j) (fun b => A b.1.1) K)
    (h : ∀ j s, G.patchContraction p U j s = ∑ r, (N j r).eval s) :
    G.contraction U = ∑ r : (j : J) → R j,
      (G.splice p (fun j => N j (r j))).contraction (G.spliceTable p (fun j => N j (r j))) := by
  simp_rw [G.contraction_splice p]
  exact G.contraction_eq_sum_patchReplacements p U R (fun j r => (N j r).eval) h

end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
