import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementList
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementCoefficient
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRecoverChoices
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementUniform

/-! # Shared template catalogue, root flags and table entries of one round -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators
namespace PortGraph

open UniformDecorations ReplacementTemplate

/-- Lists of numbered replacement terms attached to connected, bounded record shapes.
The indexing retains every summand even when its entries coincide with another one. -/
structure ShapeCatalogue (F : Type) [Field F] (K w c : ℕ) where
  length (R : PatchShape K) (hc : R.InternallyConnected) : ℕ
  term (R : PatchShape K) (hc : R.InternallyConnected) :
    Fin (length R hc) → R.RecordTerm hc w F
  length_le (R : PatchShape K) (hc : R.InternallyConnected) : length R hc ≤ 2^(w+c)
  sum_value (R : PatchShape K) (hc : R.InternallyConnected) (x : R.Stub → Bits w) :
    R.oldValue (PatchShape.RecordTerm.worldTable F w) x = ∑ i, (term R hc i).value x

namespace ShapeCatalogue

/-- The constant in the list-length bound is uniform over the old width and record. -/
theorem nonempty_of_noPlane {F : Type} [Field F]
    (h : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2))))
    {K : ℕ} (hK : 0 < K) :
    ∃ c : ℕ, ∀ w, Nonempty (ShapeCatalogue F K w c) := by
  obtain ⟨c,run⟩ := PatchShape.recordCatalogue h K hK
  refine ⟨c,fun w => ?_⟩
  choose L u bound value using fun R hconn => run R hconn w
  exact ⟨⟨L,u,bound,value⟩⟩

open ReplacementChoices
variable {F : Type} [Field F] {K w c N : ℕ} {ε : ℝ} (C : ShapeCatalogue F K w c)

abbrev Index (r : Checked N K ε) := Fin (C.length r.val.shape r.property.connected)
abbrev Tag (N : ℕ) (ε : ℝ) := (r : Checked N K ε) × C.Index r

abbrev selected (j : C.Tag N ε) := C.term j.1.val.shape j.1.property.connected j.2
abbrev templates (j : C.Tag N ε) := (C.selected j).template

def roleSlot (a : RoleLabel (C.templates (N:=N) (ε:=ε))) :=
  (localPortEquiv C.templates a).toEmbedding.trans ((C.selected a.1).slot a.2)

/-- Only the copy of a template's root role can carry the old patch's root flag. -/
def marked (a : RoleLabel (C.templates (N:=N) (ε:=ε))) : Prop :=
  a.2 = (C.templates a.1).root ∧ ∃ v, (a.1.1.val.shape.typeAt v).root = true

/-- The old record predicates have already been checked in the dependent tag type.
External pairs test the original numbered stubs and their complete certificates. -/
def rules (N : ℕ) (ε : ℝ) : LocalRules (I:=ℕ) (C.templates (N:=N) (ε:=ε)) where
  slot := C.roleSlot
  patchId j := j.1.patchId
  oldEdge := PatchRecord.stubTest (fun j : C.Tag N ε => j.1.val) (MapLabels.tests N K ε)
  recordOK _ := True
  marked := C.marked

/-- Read the named ternary or direct table on the ports of one catalogue role. -/
def coefficient (a : RoleLabel (C.templates (N:=N) (ε:=ε))) (x : RolePort C.templates a → Bits (8*w)) :
    MvPolynomial (Address w) F :=
  let e := (localPortEquiv C.templates a).symm
  (C.selected a.1).localTable a.2 (fun p => x (e (.inl p))) (fun s => x (e (.inr s)))

theorem coefficient_hasFormula (a : RoleLabel (C.templates (N:=N) (ε:=ε))) (x) :
    PlanarPatch.HasFormula (2^(PatchShape.entryExponent K*(w+1))) (C.coefficient a x) :=
  (C.selected a.1).localTable_hasFormula ..

/-- For the whole common alphabet, summing over the selected numbered terms
gives the old record's tensor extended by zero outside its original stub width. -/
theorem sum_openValue (r : Checked N K ε) (x : r.val.shape.Stub → Bits (8*w)) :
    padStubs (r.val.shape.oldValue (PatchShape.RecordTerm.worldTable F w)) x =
      ∑ i : C.Index r, let t := C.selected ⟨r,i⟩
        t.piece.graph.openValue t.piece.attach t.localTable x := by
  simp only [PatchShape.RecordTerm.openValue_all]
  unfold padStubs
  split
  · exact C.sum_value _ _ _
  · simp

end ShapeCatalogue
end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
