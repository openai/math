import OAI.Hierarchy.DescentGraphPairing

namespace OAI
/-! # Limiting whole-item replacement to actual core cables -/

namespace Hierarchy.DescentPacking
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)

def coreGraph (core : Finset N.Edge) : Network D P bits where
  Site := N.Site
  Edge := core
  finiteSite := N.finiteSite
  finiteEdge := inferInstance
  src e := N.src e.1
  dst e := N.dst e.1
  width e := N.width e.1
  attach := N.attach
  position := N.position
  in_ball := N.in_ball

/-- A surviving core edge retains its original full-graph tape ID. -/
def coreId (core : Finset N.Edge) : (coreGraph N core).Edge ↪ ℕ :=
  (Function.Embedding.subtype _).trans (originalId N.Edge)

@[simp] theorem coreId_apply (core : Finset N.Edge) (e : (coreGraph N core).Edge) :
    coreId N core e=originalId N.Edge e.val := rfl

variable {V C : Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

omit [Fintype V] in
/-- The core lookup is the rank in the original edge tape after filtering out
exterior edges and testing the two group fields. -/
theorem core_rank (core : Finset N.Edge) (dest : N.Edge → V) (e : (coreGraph N core).Edge) :
    ((graphAtom (coreGraph N core) (fun f => dest f.val) (coreId N core) e).2.2).val =
      (core.filter fun f => N.src f=N.src e.val ∧ dest f=dest e.val ∧
        originalId N.Edge f < originalId N.Edge e.val).card := by
  rw [graphAtom_rank]
  apply Finset.card_bij (fun f _ => f.val)
  · intro f hf
    exact Finset.mem_filter.mpr ⟨f.property,(Finset.mem_filter.mp hf).2⟩
  · intro a _ b _ eqn
    exact Subtype.ext eqn
  · intro b hb
    obtain ⟨mem,good⟩ := Finset.mem_filter.mp hb
    exact ⟨⟨b,mem⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,good⟩,rfl⟩

/-- The finite descriptor can point into the whole old graph, but every selected
edge belongs to the actual core. In particular any exterior tether stays in
the unmodified product of the subround. -/
def pairedCore (core : Finset N.Edge) (dest : N.Edge → V) (group : N.Site → C) (B : ℕ)
    (thin thick : C → List N.Site) (lo : ∀c,(thin c).Nodup) (hi : ∀c,(thick c).Nodup)
    (disjoint : ∀c,(thin c).Disjoint (thick c))
    (thinAt : ∀c u,u∈thin c → group u=c) (thickAt : ∀c u,u∈thick c → group u=c) :
    ((Σ c,Matched (edgeTraffic (coreGraph N core) (fun e => dest e.val)) B (thin c) (thick c))×Fin 2) ↪ N.Edge :=
  (pairedEdges (coreGraph N core) (fun e => dest e.val) group B thin thick lo hi disjoint thinAt thickAt (coreId N core)).trans
    (Function.Embedding.subtype _)

omit [Fintype C] [DecidableEq C] in
theorem pairedCore_mem (core : Finset N.Edge) (dest : N.Edge → V) (group : N.Site → C) (B : ℕ)
    (thin thick : C → List N.Site) (lo : ∀c,(thin c).Nodup) (hi : ∀c,(thick c).Nodup)
    (disjoint : ∀c,(thin c).Disjoint (thick c))
    (thinAt : ∀c u,u∈thin c → group u=c) (thickAt : ∀c u,u∈thick c → group u=c) (i) :
    pairedCore N core dest group B thin thick lo hi disjoint thinAt thickAt i∈core :=
  (pairedEdges (coreGraph N core) (fun e => dest e.val) group B thin thick lo hi disjoint thinAt thickAt (coreId N core) i).property

end
end Hierarchy.DescentPacking

end OAI
