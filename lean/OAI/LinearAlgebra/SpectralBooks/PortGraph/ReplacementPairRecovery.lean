import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRecordRecovery
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementExtraction
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementOldRoot

/-! # Re-extraction preserves the exterior wire pairing

For an expansion indexed by its decoded occurrences, each cut end remains
the same sorted old slot, and re-extraction keeps the same two ends of every
exterior wire. This verifies equality of the pairing used by a second forward
replacement, after transporting stubs along the literal record equalities.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.PatchRecord

variable {A J : Type} {K : ℕ} (R : J → PatchRecord K A) [Fintype J]
  (C : StubPairing (fun j => (R j).shape.Stub))

/-- Every expanded occurrence is exactly one recovered old block. -/
def occurrencePartition : Partition (vertices R) J K where
  part := Sigma.fst
  block := occurrence R
  mem_block := mem_occurrence R
  nonempty := occurrence_nonempty R
  bounded := occurrence_small R

variable (r : vertices R) (hc : (graph R C).ConnectedFrom r) (name : vertices R ↪ ℕ)

/-- Renaming a stub by a literal equality of canonical records. -/
def castStub {U T : PatchRecord K A} (h : U = T) : U.shape.Stub ≃ T.shape.Stub :=
  Equiv.cast (congrArg (fun X : PatchRecord K A => X.shape.Stub) h)

private theorem castStub_label {U T : PatchRecord K A} (h : U = T) (s : U.shape.Stub) :
    T.label (castStub h s).val.1 = U.label s.val.1 := by subst T; rfl

private theorem castStub_slot {U T : PatchRecord K A} (h : U = T) (s : U.shape.Stub) :
    (castStub h s).val.2.val = s.val.2.val := by subst T; rfl

variable (saved : ∀ j, R j = (occurrencePartition R).record (asMap R C r hc) (labels R) name j) (readName : A → ℕ) (names : ∀ v, readName (labels R v) = name v)

include saved names in
theorem cast_stub_dart (j : J) (s : (R j).shape.Stub) :
    (occurrencePartition R).oldDart (asMap R C r hc) (labels R) name j (castStub (saved j) s).val = ambient R C j s.val := by
  let u := castStub (saved j) s
  let v := (occurrencePartition R).vertexAt name j u.val.1
  have hl : labels R v = (R j).label s.val.1 := castStub_label (saved j) s
  have ho : v = ⟨j,s.val.1⟩ := name.injective ((names v).symm.trans
    ((congrArg readName hl).trans (names ⟨j,s.val.1⟩)))
  apply dart_ext (asMap R C r hc)
  · exact (actual_owner (asMap R C r hc) ((occurrencePartition R).vertexAt name j) u.val).trans (ho.trans (ambient_owner R C j s.val).symm)
  · have hs : (asMap R C r hc).portNumber (ambient R C j s.val).1 (ambient R C j s.val).2 = s.val.2.val :=
      (asMap_portNumber R C r hc _ _).trans (congrArg (fun q => q.2.val)
        ((namedDarts R C).apply_symm_apply ⟨⟨j,s.val.1⟩,s.val.2⟩))
    exact (actual_slot (asMap R C r hc) ((occurrencePartition R).vertexAt name j) u.val).trans ((castStub_slot (saved j) s).trans hs.symm)

include saved names in
/-- Both oriented endpoints of a surviving cut edge remain its original
occurrence and old stub, without changing the list position carried separately
by that occurrence. -/
theorem pairing_recovered (e : C.Wire) (b : Bool) :
    (Equiv.sigmaCongrRight (fun j => castStub (saved j))) (C.ends (e,b)) =
      ((occurrencePartition R).pairing (asMap R C r hc) (labels R) name).ends (C.exteriorEquiv (pieces R) e,b) := by
  apply ((occurrencePartition R).cutDarts (asMap R C r hc) (labels R) name).eq_symm_apply.mpr
  let a := C.ends (e,b)
  let u := castStub (saved a.1) a.2
  have hd := cast_stub_dart R C r hc name saved readName names a.1 a.2
  have hs := ambient_stub R C a.1 a.2
  change ambient R C a.1 a.2.val = (Sum.inl (C.ends.symm a).1,(C.ends.symm a).2) at hs
  rw [show C.ends.symm a = (e,b) from C.ends.symm_apply_apply _] at hs
  have h := ((occurrencePartition R).cutDarts_read (asMap R C r hc) (labels R) name a.1 u).trans (hd.trans hs)
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (congrArg (fun q : C.Edge (pieces R) × Bool => q.2) h)

end PortGraph.PatchRecord

end

end SpectralBooks
end LinearAlgebra
end OAI
