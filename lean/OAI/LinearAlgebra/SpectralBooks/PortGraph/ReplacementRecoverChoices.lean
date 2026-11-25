import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoiceFamily
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRecordRecovery
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementPatchIds
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RootedMapRelabel

/-! # Recovering the choices of a certified representative

After the saved records have been expanded, the old verifier gives each
vertex its canonical label. Each copy of a record then indexes exactly one
canonical patch, and the sorted checked record at that patch recovers every
saved field. The chosen replacement term can thus be read on the ordinary
finite representative of the expanded map.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace PortGraph.ReplacementChoices

open MapLabels

namespace Checked

variable {N K : ℕ} {ε : ℝ} (R : Checked N K ε)

/-- The common identifier in the record, read at its first vertex. -/
def patchId : ℕ := patchName (R.val.label ⟨0, R.val.shape.positive⟩)

theorem patchName_eq (i : R.val.shape.Vertex) : patchName (R.val.label i) = R.patchId :=
  R.property.commonPatch _ _

end Checked

namespace System

universe u
variable {N K : ℕ} {ε : ℝ} (C : System N K ε) {J : Type}
  (R : J → Checked N K ε)

private abbrev records (j : J) := (R j).val

/-- Precise occurrence, label and record equalities for the recovered
representative, expressed on the original vertices before relabelling. -/
structure Recovered (H : MapRep N) (fV : PatchRecord.vertices (records R) → Fin H.vertexCount.val) where
  occ : J ≃ C.Occ H
  part : ∀ v, C.part H (fV v) = occ v.1
  checked : ∀ j, C.checked H (occ j) = R j
  label : ∀ v, PatchRecord.labels (records R) v = C.label H (fV v)

namespace Recovered

variable {C R} {H : MapRep N} {fV} (d : C.Recovered R H fV)

include d in
theorem name (v) : vertexName (PatchRecord.labels (records R) v) = C.name H (fV v) :=
  congrArg vertexName (d.label v)

/-- Install the actual saved term at every occurrence of the recovered map. -/
def choices (Term : Checked N K ε → Type u) (t : ∀ j, Term (R j)) : (C.family Term).Label H :=
  fun k => cast (congrArg Term (by rw [← d.checked, d.occ.apply_symm_apply])) (t (d.occ.symm k))

theorem choices_sigma (Term : Checked N K ε → Type u) (t : ∀ j, Term (R j)) (j : J) :
    (⟨C.checked H (d.occ j), d.choices Term t (d.occ j)⟩ : Σ Q, Term Q) = ⟨R j,t j⟩ := by
  apply Sigma.ext (d.checked j)
  exact (cast_heq _ _).trans (by rw [d.occ.symm_apply_apply])

end Recovered

variable [Fintype J] (P : StubPairing (fun j => (R j).val.shape.Stub))
  (r : PatchRecord.vertices (records R)) (hc : (PatchRecord.graph (records R) P).ConnectedFrom r)

private abbrev oldMap := PatchRecord.asMap (records R) P r hc

variable (orient : ∀ e b, (P.ends (e,b)).2.val.side = b)
  (types : ∀ v, (oldMap R P r hc).typeAt v = (R v.1).val.shape.typeAt v.2)
  (pass : (tests N K ε).Pass (oldMap R P r hc) (PatchRecord.labels (records R)))
  (boundary : ∀ e, (R (P.ends (e,false)).1).patchId ≠ (R (P.ends (e,true)).1).patchId)

set_option maxHeartbeats 1600000 in
include orient types pass boundary in
/-- Re-reading the certified map on any isomorphic representative identifies
all of the decoded occurrences and their checked old records. -/
def recover (H : MapRep N) (f : (oldMap R P r hc).Iso H.map) : C.Recovered R H f.vertex := by
  let z := PatchRecord.labels (records R)
  let M := oldMap R P r hc
  have hz (v) : z v = C.label H (f.vertex v) := C.label_iso_of_pass H f z pass v
  have saved (v : PatchRecord.vertices (records R)) : patchName (z v) = (R v.1).patchId :=
    (R v.1).patchName_eq v.2
  have witness (j : J) : Nonempty (PatchRecord.pieces (records R) j).Vertex :=
    ⟨⟨0, (R j).val.shape.positive⟩⟩
  have checks := C.partition_checks M z pass
  have inj : Function.Injective (fun j => (R j).patchId) :=
    P.patchId_injective (PatchRecord.pieces (records R)) _ boundary _ saved (fun v => by
      have fiber : StubPairing.idFiber (PatchRecord.pieces (records R)) (fun x => patchName (z x)) v =
          RootedMap.patchFiber (fun x => patchName (z x)) v := by
        ext x
        simp [StubPairing.idFiber, RootedMap.patchFiber]
      rw [fiber]
      exact (checks.2.1 v).1) witness
  let chooseOcc (j : J) := C.part H (f.vertex ⟨j,(witness j).some⟩)
  have id_eq (v : PatchRecord.vertices (records R)) :
      (C.part H (f.vertex v)).val = (R v.1).patchId := (congrArg patchName (hz v).symm).trans (saved v)
  have choose_id (j : J) : (chooseOcc j).val = (R j).patchId := id_eq ⟨j,_⟩
  have part (v : PatchRecord.vertices (records R)) : C.part H (f.vertex v) = chooseOcc v.1 :=
    Subtype.ext ((id_eq v).trans (choose_id v.1).symm)
  let occ := Equiv.ofBijective chooseOcc <| by
    constructor
    · intro j k h
      exact inj (((choose_id j).symm.trans (congrArg Subtype.val h)).trans (choose_id k))
    · intro k
      obtain ⟨w,rfl⟩ := C.part_surjective H k
      obtain ⟨v,rfl⟩ := f.vertex.surjective w
      exact ⟨v.1, (part v).symm⟩
  refine ⟨occ,part,?_,hz⟩
  intro j
  apply Subtype.ext
  let nm : PatchRecord.vertices (records R) ↪ ℕ := ⟨fun v => vertexName (z v),checks.1⟩
  have flags (v : PatchRecord.vertices (records R)) :
      ((R v.1).val.shape.typeAt v.2).root = decide (v = r) := congrArg MapType.root (types v).symm
  have orig := PatchRecord.extract_asMap (records R) P orient r hc flags nm j (R j).property.sorted
  have block (v) : v ∈ PatchRecord.occurrence (records R) j ↔ f.vertex v ∈ C.block H (occ j) := by
    rw [PatchRecord.mem_occurrence, C.mem_block, part v]
    exact occ.injective.eq_iff.symm
  have he := PatchRecord.extract_iso f block nm (C.name H) (fun v => congrArg vertexName (hz v))
    z _ hz (PatchRecord.occurrence_nonempty _ j) (PatchRecord.occurrence_small _ j) (C.nonempty H _) (C.bounded H _)
  exact he.symm.trans orig

include orient types pass boundary in
/-- The old verifier supplies the cap and sphericity needed to put the actual
expanded map into the finite class sum. -/
def recoverToRep :
    let M := oldMap R P r hc
    let hm := C.member M _ pass
    C.Recovered R (M.toRep hm.1 hm.2) (M.toRepIso hm.1 hm.2).vertex :=
  C.recover R P r hc orient types pass boundary _ _

end System
end PortGraph.ReplacementChoices

end

end SpectralBooks
end LinearAlgebra
end OAI
