import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementAssembly
import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabels

/-! # Recovering the canonical old patches after expansion

Labels in a copied old record give all its vertices one patch identifier.
Different records might initially advertise the same identifier. On the
assembled graph, every boundary edge changes identifier. A walk inside a
certified identifier class must therefore stay in one occurrence.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace PortGraph.StubPairing

universe u
variable {J : Type u} {S : J → Type u} (C : StubPairing S) (P : ∀ j, OpenPiece (S j))
  {I : Type*} (patchId : J → I)
  (crossId : ∀ e, patchId (C.ends (e,false)).1 ≠ patchId (C.ends (e,true)).1)

include crossId in
private theorem same_occurrence_on_edge {x y : Vertex P}
    (h : (PlanarPatch.underlying (C.assemble P).tail (C.assemble P).head).Adj x y)
    (hid : patchId x.1 = patchId y.1) : x.1 = y.1 := by
  obtain ⟨_, e, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := h
  · rcases e with e | ⟨j,d⟩
    · exact (crossId e hid).elim
    · rfl
  · rcases e with e | ⟨j,d⟩
    · exact (crossId e hid.symm).elim
    · rfl

variable [Fintype J]

/-- The certified class containing a given old vertex. -/
def idFiber (report : Vertex P → I) (v : Vertex P) : Finset (Vertex P) :=
  Finset.univ.filter fun w => report w = report v

/-- The vertex set of the old occurrence inserted from a single record. -/
def occurrenceBlock (j : J) : Finset (Vertex P) := Finset.univ.filter fun x => x.1 = j

variable (report : Vertex P → I) (saved : ∀ v, report v = patchId v.1)
  (connected : ∀ v, PlanarPatch.Connected (C.assemble P).tail (C.assemble P).head (idFiber P report v))

include saved crossId connected in
/-- Connectedness of an identifier class and the unequal-identifier check
on exterior edges force two vertices of that class into the same occurrence. -/
theorem same_occurrence_iff (v w : Vertex P) : report v = report w ↔ v.1 = w.1 := by
  constructor
  · intro h
    let B := idFiber P report v
    let G := (PlanarPatch.underlying (C.assemble P).tail (C.assemble P).head).induce (B : Set (Vertex P))
    have mem (x : B) : report x.val = report v := (Finset.mem_filter.mp x.property).2
    have localEq {a b : B} (edge : G.Adj a b) : a.val.1 = b.val.1 := by
      apply same_occurrence_on_edge C P patchId crossId edge
      exact ((saved a.val).symm.trans (mem a)).trans ((mem b).symm.trans (saved b.val))
    let a : B := ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    let b : B := ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.symm⟩⟩
    have walk : G.Reachable a b := (connected v).preconnected a b
    rw [SimpleGraph.reachable_eq_reflTransGen] at walk
    have same {x y : B} (p : Relation.ReflTransGen G.Adj x y) : x.val.1 = y.val.1 := by
      induction p with
      | refl => rfl
      | tail _ e ih => exact ih.trans (localEq e)
    exact same walk
  · intro h
    rw [saved, saved, h]

include saved crossId connected in
/-- An actual vertex in each old record lets us conclude global injectivity
of the occurrence identifiers. -/
theorem patchId_injective (nonempty : ∀ j, Nonempty (P j).Vertex) : Function.Injective patchId := by
  intro i j h
  let v : Vertex P := ⟨i,(nonempty i).some⟩
  let w : Vertex P := ⟨j,(nonempty j).some⟩
  exact (same_occurrence_iff C P patchId crossId report saved connected v w).mp
    ((saved v).trans (h.trans (saved w).symm))

include saved crossId connected in
/-- Every certified patch fibre equals the full advertised occurrence. -/
theorem idFiber_eq_occurrenceBlock (v : Vertex P) :
    idFiber P report v = occurrenceBlock P v.1 := by
  ext w
  simp [idFiber, occurrenceBlock, same_occurrence_iff C P patchId crossId report saved connected]

include saved crossId connected in
/-- If the certified fibres belong to the canonical partition, its entire
family is exactly the advertised old occurrences. -/
theorem blocks_eq_occurrences [DecidableEq (Vertex P)] (nonempty : ∀ j, Nonempty (P j).Vertex)
    (blocks : Finset (Finset (Vertex P)))
    (disjoint : (↑blocks : Set (Finset (Vertex P))).PairwiseDisjoint id)
    (inhabited : ∀ B ∈ blocks, B.Nonempty) (fibres : ∀ v, idFiber P report v ∈ blocks) :
    blocks = Finset.univ.image (occurrenceBlock P) := by
  have occurs (i : J) : occurrenceBlock P i ∈ blocks := by
    let v : Vertex P := ⟨i,(nonempty i).some⟩
    exact (idFiber_eq_occurrenceBlock C P patchId crossId report saved connected v) ▸ fibres v
  ext B
  constructor
  · intro hB
    obtain ⟨v,hv⟩ := inhabited B hB
    have hv' : v ∈ occurrenceBlock P v.1 := by simp [occurrenceBlock]
    refine Finset.mem_image.mpr ⟨v.1, Finset.mem_univ _, ?_⟩
    by_contra hne
    exact Finset.disjoint_left.mp (disjoint (occurs v.1) hB hne) hv' hv
  · intro h
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
    exact occurs j

section Certificate
open PlanarPatch

variable [DecidableEq (Vertex P)] [DecidableEq (C.Edge P)]

/-- Applying the canonical old certificate to the expanded graph identifies
each occurrence injectively and recovers precisely its canonical vertex block.
The old patch records only have to agree locally on their identifier. -/
theorem certificate_recovers_occurrences (M : RootedMap (Vertex P) (C.Edge P))
    (assembled : M.graph = C.assemble P) {N K : ℕ} {ε : ℝ}
    {c : RootedMap.Certificate (Vertex P) (C.Edge P)} (pass : M.CertificateChecks N K ε c)
    (candidates : M.HasCandidates K ε) (name : J → ℕ)
    (boundary : ∀ e, name (C.ends (e,false)).1 ≠ name (C.ends (e,true)).1)
    (agree : ∀ v : Vertex P, (c.patch v).2 = name v.1) (nonempty : ∀ j, Nonempty (P j).Vertex) :
    Function.Injective name ∧
      canonicalBlocks ⟨c.name,pass.tree.name_injective⟩ M.graph.tail M.graph.head K ε Finset.univ N =
        Finset.univ.image (occurrenceBlock P) := by
  let n := fun v : Vertex P => (c.patch v).2
  have hf (v : Vertex P) : idFiber P n v = RootedMap.patchFiber n v := by
    ext x
    simp [idFiber, RootedMap.patchFiber]
  have hconn (v : Vertex P) : Connected (C.assemble P).tail (C.assemble P).head (idFiber P n v) := by
    rw [← assembled, hf]
    exact ((pass.partition M candidates).1 v).1
  refine ⟨patchId_injective C P name boundary n agree hconn nonempty, ?_⟩
  let key : Vertex P ↪ ℕ := ⟨c.name,pass.tree.name_injective⟩
  have cap : (Finset.univ : Finset (Vertex P)).card ≤ N := by simpa using (pass.member M).1
  obtain ⟨_, hd, hb, _⟩ := (canonical_peeling key M.graph.tail M.graph.head K ε Finset.univ
    (fun R _ => candidates R) cap).partition
  apply blocks_eq_occurrences C P name boundary n agree hconn nonempty _ hd (fun B h => (hb B h).1)
  intro v
  rw [hf]
  exact pass.patchFiber_mem M candidates v

/-- For the actual finite alphabet, the old vertex and edge tests alone
supply the decoded certificate, its spherical-map membership, and the
canonical partition asserted above. -/
theorem passing_recovers_occurrences (M : RootedMap (Vertex P) (C.Edge P))
    (assembled : M.graph = C.assemble P) {N K : ℕ} {ε : ℝ} (hN : 1 ≤ N)
    (labels : Vertex P → MapLabels.Label N K) (pass : (MapLabels.tests N K ε).Pass M labels)
    (candidates : M.HasCandidates K ε) (name : J → ℕ)
    (boundary : ∀ e, name (C.ends (e,false)).1 ≠ name (C.ends (e,true)).1)
    (agree : ∀ v : Vertex P, MapLabels.patchName (labels v) = name v.1)
    (nonempty : ∀ j, Nonempty (P j).Vertex) :
    (Fintype.card (Vertex P) ≤ N ∧ M.Spherical) ∧ Function.Injective name ∧
      canonicalBlocks ⟨fun v => MapLabels.vertexName (labels v),
        (MapLabels.pass_partition M hN labels pass candidates).1⟩
        M.graph.tail M.graph.head K ε Finset.univ N = Finset.univ.image (occurrenceBlock P) := by
  refine ⟨MapLabels.pass_member M hN labels pass,?_⟩
  obtain ⟨c,h,rfl⟩ := (MapLabels.pass_iff_encode M hN labels).mp pass
  exact certificate_recovers_occurrences C P M assembled h candidates name boundary agree nonempty

end Certificate
end PortGraph.StubPairing

end

end SpectralBooks
end LinearAlgebra
end OAI
