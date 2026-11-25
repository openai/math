import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementReconstruction
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementOldMap

/-! # Root and connectivity of the expanded old map

The unique mark on the smaller map identifies a single decoded tree occurrence.
In that copy, the saved old root flags identify one vertex. Connectivity of the
smaller map projects to the decoded occurrence graph and lifts through the
connected old records.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace PortGraph

namespace StubPairing

/-- Change only the local names of the boundary stubs. This allows the decoder
and the old record to present the very same stubs by equivalent finite types. -/
def renameStubs {C : Type} {S D : C → Type} (p : StubPairing S) (stub : ∀ c, S c ≃ D c) :
    StubPairing D where
  Wire := p.Wire
  ends := p.ends.trans (Equiv.sigmaCongrRight stub)
  cross := p.cross

end StubPairing

namespace ReplacementTemplate

variable {V E J I : Type} {T : J → ReplacementTemplate.{0,0,0}} {H : PortGraph V E}
    {num : H.FourPortNumbering} {slot : Numbering T} {z : V → Σ j, (T j).Role}
    {patchId : J → I} {oldEdge : (Σ j, (T j).Stub) → (Σ j, (T j).Stub) → Prop}
    (hv : ∀ v, VertexTest T num slot z v)
    (he : ∀ e, PairTest patchId oldEdge (readEnd hv e false) (readEnd hv e true))

section Connectivity
variable [Fintype E] [∀ j, Fintype (T j).Role] [∀ j, Fintype (T j).Wire]

/-- The accepted smaller map connects all decoded occurrences. -/
theorem decoded_occurrences_connected (r : V) (hconn : H.ConnectedFrom r) :
    (decodedPairing hv he).occurrenceGraph.ConnectedFrom (vertexEquiv hv he r).1 := by
  apply (decodedPairing hv he).occurrence_connected (treePiece (T := T) (z := z)) _
    (fun c => ⟨(T c.1).root⟩)
  intro y
  obtain ⟨v,rfl⟩ := (vertexEquiv hv he).surjective y
  apply Relation.ReflTransGen.lift (vertexEquiv hv he) _ _ _ (hconn v)
  rintro a b ⟨e,k,rfl,rfl⟩
  exact ⟨decodedEdge hv he e,k,(decoded_incidence hv he e k).symm,(decoded_incidence hv he e (!k)).symm⟩

end Connectivity

variable {A : Type} {K : ℕ} (record : J → PatchRecord K A)

/-- At every copy of a record containing an old root, precisely its designated
tree role carries the new root flag. A record without an old root marks no role. -/
def recordMark (chosen : ∀ j, (T j).Role) (a : Σ j, (T j).Role) : Prop :=
  (∃ i, ((record a.1).shape.typeAt i).root = true) ∧ a.2 = chosen a.1

abbrev oldRecords (c : Copies (T := T) z) := record c.1

/-- The boundary pairing for expansion, with the original stub names. -/
def recordPairing [Fintype E] (stub : ∀ j, (T j).Stub ≃ (record j).shape.Stub) :
    StubPairing (fun c : Copies (T := T) z => (oldRecords record c).shape.Stub) :=
  (decodedPairing hv he).renameStubs (fun c => stub c.1)

private theorem connectedFrom_of_underlying {W D : Type*} (G : PortGraph W D)
    (h : (PlanarPatch.underlying G.tail G.head).Connected) (w : W) : G.ConnectedFrom w := by
  intro u
  have walk := (SimpleGraph.reachable_iff_reflTransGen w u).mp (h.preconnected w u)
  induction walk with
  | refl => exact .refl
  | tail _ hadj ih =>
    obtain ⟨_, e, ⟨ht,hh⟩ | ⟨hh,ht⟩⟩ := hadj
    · exact ih.tail ⟨e,false,ht,hh⟩
    · exact ih.tail ⟨e,true,ht,hh⟩

variable (chosen : ∀ j, (T j).Role) (r : V)
  (checked : ∀ v, recordMark record chosen (z v) ↔ v = r)

include checked in
private theorem marked_iff_at_decoded (x : (c : Copies (T := T) z) × (T c.1).Role) :
    recordMark record chosen ⟨x.1.1,x.2⟩ ↔ x = vertexEquiv hv he r := by
  obtain ⟨v,rfl⟩ := (vertexEquiv hv he).surjective x
  rw [vertexEquiv_role, checked, (vertexEquiv hv he).injective.eq_iff]

variable {L : Type*} {readName : A → ℕ} {id : A → L}
    {vertex : MapType → A → Prop} {edge : Fin 4 → Fin 4 → A → A → Prop}
    (valid : ∀ c : Copies (T := T) z, (record c.1).Valid readName id vertex edge)

include checked valid in
/-- The old root is recovered from the type test of the smaller root and the
at-most-one-root test on each old record. Its occurrence is the occurrence
of the smaller root, a fact used when lifting paths. -/
theorem exists_old_root :
    ∃ old : StubPairing.Vertex (fun c : Copies (T := T) z => (record c.1).toPiece),
      old.1 = (vertexEquiv hv he r).1 ∧
      ∀ v : StubPairing.Vertex (fun c : Copies (T := T) z => (record c.1).toPiece),
        ((record v.1.1).shape.typeAt v.2).root = true ↔ v = old := by
  let a := vertexEquiv hv he r
  have mark := (marked_iff_at_decoded hv he record chosen r checked a).mpr rfl
  obtain ⟨i, hi⟩ := mark.1
  refine ⟨⟨a.1,i⟩,rfl,?_⟩
  rintro ⟨c,k⟩
  refine ⟨fun hk => ?_, fun h => ?_⟩
  · have marked : recordMark record chosen ⟨c.1,chosen c.1⟩ := ⟨⟨k,hk⟩,rfl⟩
    have equal := (marked_iff_at_decoded hv he record chosen r checked ⟨c,chosen c.1⟩).mp marked
    obtain rfl : c = a.1 := congrArg Sigma.fst equal
    exact congrArg (Sigma.mk a.1) ((valid a.1).uniqueRoot k i hk hi)
  · exact h.symm ▸ hi

private local instance (priority := high) : DecidableEq (Copies (T := T) z) := Classical.decEq _

variable (stub : ∀ j, (T j).Stub ≃ (record j).shape.Stub)

variable [Fintype E] [∀ j, Fintype (T j).Role] [∀ j, Fintype (T j).Wire]

include checked valid in
/-- The decoded old graph has exactly one choice of root consistent with all
of the saved root flags, and all its vertices are connected to that root.
These are the two hypotheses consumed by `PatchRecord.asMap` and its type
and certificate checks. -/
theorem unique_old_root_connected (hconn : H.ConnectedFrom r) :
    ∃! old : StubPairing.Vertex (fun c : Copies (T := T) z => (record c.1).toPiece),
      ((recordPairing hv he record stub).assemble (fun c => (record c.1).toPiece)).ConnectedFrom old ∧
      ∀ v : StubPairing.Vertex (fun c : Copies (T := T) z => (record c.1).toPiece),
        ((record v.1.1).shape.typeAt v.2).root = decide (v = old) := by
  obtain ⟨⟨c,i⟩,hc,flag⟩ := exists_old_root hv he record chosen r checked valid
  let C := recordPairing hv he record stub
  change c = (vertexEquiv hv he r).1 at hc
  have hocc : C.occurrenceGraph.ConnectedFrom c := by
    rw [hc]
    exact decoded_occurrences_connected hv he r hconn
  have pieces (c : Copies (T := T) z) : ∃ v, (record c.1).toPiece.graph.ConnectedFrom v :=
    ⟨⟨0,(record c.1).shape.positive⟩,connectedFrom_of_underlying _ (valid c).connected _⟩
  refine ⟨⟨c,i⟩, ⟨C.assemble_connected _ i hocc pieces, fun v => ?_⟩, ?_⟩
  · exact Bool.eq_iff_iff.mpr ((flag v).trans decide_eq_true_iff.symm)
  · intro old hold
    apply (flag old).mp
    simp [hold.2 old]

/-- Replace the tree template stub name by the corresponding old recorded name. -/
def recordedStub (s : Σ j, (T j).Stub) : Σ j, (record j).shape.Stub :=
  ⟨s.1,stub s.1 s.2⟩

include checked in
/-- Expanding an accepted smaller map yields a rooted old map passing the saved
map-label verifier. The hypotheses relating the catalogue stubs to the old
ones are local direction and old edge tests. -/
theorem exists_passing_old_map [Fintype (Copies (T := T) z)]
    (hconn : H.ConnectedFrom r) (tests : MapLabelTests A)
    (oldValid : ∀ c : Copies (T := T) z, (record c.1).Valid readName id tests.vertex tests.edge)
    (directed : ∀ j (s : (T j).Stub), (stub j s).val.side = (T j).direction s)
    (oldCheck : ∀ a b, oldEdge a b →
      PatchRecord.stubTest record tests (recordedStub record stub a) (recordedStub record stub b)) :
    let R := oldRecords (z := z) record
    let C := recordPairing hv he record stub
    ∃ (old : PatchRecord.vertices R) (conn : (PatchRecord.graph R C).ConnectedFrom old),
      tests.Pass (PatchRecord.asMap R C old conn) (PatchRecord.labels R) ∧
        ∀ v, (PatchRecord.asMap R C old conn).typeAt v = (R v.1).shape.typeAt v.2 := by
  let R := oldRecords (z := z) record
  let C := recordPairing hv he record stub
  obtain ⟨old, ⟨conn, hr⟩, _⟩ :=
    unique_old_root_connected hv he record chosen r checked oldValid stub hconn
  have orient (e : C.Wire) (b : Bool) : (C.ends (e,b)).2.val.side = b := by
    let s := endsEquiv hv he (e,b)
    exact (directed s.1.1 s.2).trans (stub_direction hv he e b)
  refine ⟨old,conn,PatchRecord.asMap_pass R C orient old conn hr tests readName id oldValid ?_,
    PatchRecord.asMap_typeAt R C orient old conn hr⟩
  intro e
  exact oldCheck _ _ (all_external_old_tests hv he e)

end ReplacementTemplate
end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
