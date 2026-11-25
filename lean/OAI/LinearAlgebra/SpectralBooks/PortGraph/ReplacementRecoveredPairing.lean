import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementPairIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRecoverChoices

/-! # Exterior wires of the recovered certified map -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.ReplacementChoices.System.Recovered

open PatchRecord
variable {N K : ℕ} {ε : ℝ} {J : Type} [Fintype J] {C : System N K ε}
  {R : J → Checked N K ε} (P : StubPairing (fun j => (R j).val.shape.Stub))
  (r : vertices (fun j => (R j).val)) (hc : (graph (fun j => (R j).val) P).ConnectedFrom r)
  {H : MapRep N} (f : (asMap (fun j => (R j).val) P r hc).Iso H.map)
  (d : C.Recovered R H f.vertex)

/-- The partition of the target presentation as used in the cut pairing. -/
private abbrev partition (C : System N K ε) (H : MapRep N) :
    Partition (Fin H.vertexCount.val) (C.Occ H) K :=
  ⟨C.part H,C.block H,C.mem_block H,C.nonempty H,C.bounded H⟩

/-- The expansion's outside wires become exactly the cut wires in the finite
old representative, in the same orientation. -/
def exterior : P.Wire ≃ H.map.graph.CrossEdge (C.part H) :=
  (P.exteriorEquiv (pieces (fun j => (R j).val))).trans
    (Partition.cutEquiv (occurrencePartition (fun j => (R j).val)) (partition C H)
      _ _ f d.occ d.part)

private theorem castFields {A : Type} {R S : PatchRecord K A} (eq : R = S) (s : R.shape.Stub) :
    S.label (castStub eq s).val.1 = R.label s.val.1 ∧
    (castStub eq s).val.2.val = s.val.2.val := by subst S; exact ⟨rfl,rfl⟩

include f d in
/-- Read the transported saved stub on the global dart set of the old
representative. Its incident vertex name and local number agree with the
original assembled dart. -/
theorem stub_dart (j : J) (s : (R j).val.shape.Stub) :
    (partition C H).oldDart H.map (C.label H) (C.name H) (d.occ j)
        (castStub (congrArg Subtype.val (d.checked j).symm) s).val =
      (f.edge.prodCongr (Equiv.refl Bool)) (ambient (fun j => (R j).val) P j s.val) := by
  let u := castStub (congrArg Subtype.val (d.checked j).symm) s
  let v := (partition C H).vertexAt (C.name H) (d.occ j) u.val.1
  let q := ambient (fun j => (R j).val) P j s.val
  have h := castFields (congrArg Subtype.val (d.checked j).symm) s
  have hz : C.label H v = (R j).val.label s.val.1 := h.1
  have ho : v = f.vertex ⟨j,s.val.1⟩ := (C.name H).injective
    ((congrArg MapLabels.vertexName hz).trans (d.name ⟨j,s.val.1⟩))
  apply dart_ext H.map
  · exact (actual_owner H.map _ u.val).trans (ho.trans ((congrArg f.vertex
      (ambient_owner (fun j => (R j).val) P j s.val).symm).trans (f.incidence q.1 q.2)))
  · have hs : (asMap (fun j => (R j).val) P r hc).portNumber q.1 q.2 = s.val.2.val :=
      (asMap_portNumber (fun j => (R j).val) P r hc _ _).trans (congrArg (fun w => w.2.val)
        ((namedDarts (fun j => (R j).val) P).apply_symm_apply ⟨⟨j,s.val.1⟩,s.val.2⟩))
    exact (actual_slot H.map _ u.val).trans (h.2.trans (hs.symm.trans (f.number q.1 q.2)))

/-- The actual compiler pairing of the recovered certified representative,
at both ends of each cut wire. -/
theorem pairing (e : P.Wire) (b : Bool) :
    Equiv.sigmaCongr d.occ (fun j => castStub (congrArg Subtype.val (d.checked j).symm))
        (P.ends (e,b)) =
      ((partition C H).pairing H.map (C.label H) (C.name H)).ends (exterior P r hc f d e,b) := by
  apply ((partition C H).cutDarts H.map (C.label H) (C.name H)).eq_symm_apply.mpr
  let a := P.ends (e,b)
  let u := castStub (congrArg Subtype.val (d.checked a.1).symm) a.2
  have hd := stub_dart P r hc f d a.1 a.2
  have hs := ambient_stub (fun j => (R j).val) P a.1 a.2
  change ambient (fun j => (R j).val) P a.1 a.2.val = (Sum.inl (P.ends.symm a).1,(P.ends.symm a).2) at hs
  rw [show P.ends.symm a = (e,b) from P.ends.symm_apply_apply _] at hs
  have h := ((partition C H).cutDarts_read H.map (C.label H) (C.name H) (d.occ a.1) u).trans
    (hd.trans (congrArg (f.edge.prodCongr (Equiv.refl Bool)) hs))
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (congrArg (fun q : Fin H.edgeCount.val × Bool => q.2) h)

end PortGraph.ReplacementChoices.System.Recovered

end

end SpectralBooks
end LinearAlgebra
end OAI
