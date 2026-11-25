import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabels
import OAI.LinearAlgebra.SpectralBooks.PortGraph.MapLabelTestsIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPatchRecordIso
import OAI.LinearAlgebra.SpectralBooks.DecoratedMaps.DecoratedMapClass
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortPatchContraction

/-! # Canonical old records and choices of replacement terms

The full passing label at each vertex is unique. Its reported patch identifier
indexes the occurrences, and its preorder name orders the slots of each old
record. Transport of a choice preserves both the record and the list position.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace PortGraph.ReplacementChoices

open MapLabels

/-- The uniform tests on old maps at one cutoff and vertex cap. -/
structure System (N K : ℕ) (ε : ℝ) : Prop where
  encoding : Nonempty (Label N K ↪ (Fin ((80*5^(2*K+2))*Nat.clog 2 (2*N)) → Bool))
  member : ∀ {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (M : RootedMap V E) (z : V → Label N K), (tests N K ε).Pass M z →
      Fintype.card V ≤ N ∧ M.Spherical
  unique : ∀ {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (M : RootedMap V E), Fintype.card V ≤ N → M.Spherical → ∃! z, (tests N K ε).Pass M z
  partition_checks : ∀ {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (M : RootedMap V E) (z : V → Label N K), (tests N K ε).Pass M z →
      Function.Injective (fun v => vertexName (z v)) ∧
      (∀ v, PlanarPatch.Connected M.graph.tail M.graph.head (RootedMap.patchFiber (fun x => patchName (z x)) v) ∧
        (RootedMap.patchFiber (fun x => patchName (z x)) v).card ≤ K) ∧
      ((Finset.univ.filter (fun e : E => patchName (z (M.graph.tail e)) ≠
        patchName (z (M.graph.head e)))).card : ℝ) ≤ ε * Fintype.card V

/-- The cutoff is common to every vertex cap and every summand. -/
theorem exists_systems (ε : ℝ) (hε : 0 < ε) :
    ∃ K, ∀ N, 1 ≤ N → System N K ε := by
  obtain ⟨K,hK⟩ := map_labels.{0,0} ε hε
  refine ⟨K, fun N hN => ?_⟩
  obtain ⟨enc,check⟩ := hK N hN
  exact ⟨enc, fun M z hz => (check _ _ M).1.mp ⟨z,hz⟩,
    fun M => (check _ _ M).2.1, fun M => (check _ _ M).2.2⟩

/-- A record indexing the replacement catalogue has passed every internal test. -/
abbrev Checked (N K : ℕ) (ε : ℝ) :=
  {R : PatchRecord K (Label N K) //
    R.Valid vertexName patchName (tests N K ε).vertex (tests N K ε).edge}

namespace System

variable {N K : ℕ} {ε : ℝ} (C : System N K ε) (M : MapRep N)

private theorem cap : Fintype.card (Fin M.vertexCount.val) ≤ N := by
  simpa using Nat.le_of_lt_succ M.vertexCount.isLt

/-- Canonical full labelling of a member of the old map family. -/
def label : Fin M.vertexCount.val → Label N K := (C.unique M.map (cap M) M.spherical).choose

theorem pass : (tests N K ε).Pass M.map (C.label M) :=
  (C.unique M.map (cap M) M.spherical).choose_spec.1

theorem eq_label {z} (hz : (tests N K ε).Pass M.map z) : z = C.label M :=
  (C.unique M.map (cap M) M.spherical).choose_spec.2 z hz

def name : Fin M.vertexCount.val ↪ ℕ :=
  ⟨fun v => vertexName (C.label M v), (C.partition_checks M.map _ (C.pass M)).1⟩

/-- Only patch identifiers actually reported by the old vertices occur. -/
abbrev Occ := ↥(Finset.univ.image (fun v => patchName (C.label M v)))

def part (v : Fin M.vertexCount.val) : C.Occ M :=
  ⟨patchName (C.label M v), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

def block (j : C.Occ M) : Finset (Fin M.vertexCount.val) :=
  Finset.univ.filter (fun v => patchName (C.label M v) = j.val)

theorem mem_block (j : C.Occ M) (v) : v ∈ C.block M j ↔ C.part M v = j := by
  simp [block, part, Subtype.ext_iff]

theorem part_surjective : Function.Surjective (C.part M) := by
  intro j
  obtain ⟨v,_,hv⟩ := Finset.mem_image.mp j.property
  exact ⟨v,Subtype.ext hv⟩

theorem nonempty (j : C.Occ M) : (C.block M j).Nonempty := by
  obtain ⟨v,hv⟩ := C.part_surjective M j
  exact ⟨v,(C.mem_block M j v).mpr hv⟩

theorem block_part (v) : C.block M (C.part M v) =
    RootedMap.patchFiber (fun x => patchName (C.label M x)) v := rfl

theorem connected (j : C.Occ M) :
    PlanarPatch.Connected M.map.graph.tail M.map.graph.head (C.block M j) := by
  obtain ⟨v,rfl⟩ := C.part_surjective M j
  exact ((C.partition_checks M.map _ (C.pass M)).2.1 v).1

theorem bounded (j : C.Occ M) : (C.block M j).card ≤ K := by
  obtain ⟨v,rfl⟩ := C.part_surjective M j
  exact ((C.partition_checks M.map _ (C.pass M)).2.1 v).2

/-- Each crossing edge is counted once, regardless of the multiplicity of
edges between its two patches. -/
theorem cut_budget :
    (Fintype.card (M.map.graph.CrossEdge (C.part M)) : ℝ) ≤ ε * Fintype.card (Fin M.vertexCount.val) := by
  have h := (C.partition_checks M.map _ (C.pass M)).2.2
  simpa [CrossEdge, Fintype.card_subtype, part, Subtype.ext_iff] using h

/-- The old record with certified labels on its sorted original vertex slots. -/
def record (j : C.Occ M) : PatchRecord K (Label N K) :=
  PatchRecord.extract M.map (C.label M) (C.block M j) (C.name M) (C.nonempty M j) (C.bounded M j)

theorem record_valid (j : C.Occ M) :
    (C.record M j).Valid vertexName patchName (tests N K ε).vertex (tests N K ε).edge := by
  apply PatchRecord.extract_valid M.map (C.label M) _ (C.pass M) _ (C.connected M j)
    _ _ _ _ (fun _ => rfl)
  intro v hv w hw
  exact ((Finset.mem_filter.mp hv).2).trans (Finset.mem_filter.mp hw).2.symm

def checked (j : C.Occ M) : Checked N K ε := ⟨C.record M j,C.record_valid M j⟩

/-- The patch name stored at any slot is the occurrence identifier. -/
theorem record_patch (j : C.Occ M) (i : (C.record M j).shape.Vertex) :
    patchName ((C.record M j).label i) = j.val :=
  (Finset.mem_filter.mp (PatchRecord.slotOrder (C.block M j) (C.name M) i).property).2

/-- A passing labelling on any presentation of this map is its canonical
labelling read through the isomorphism. -/
theorem label_iso_of_pass {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {H : RootedMap V E} (f : H.Iso M.map) (z : V → Label N K) (hz : (tests N K ε).Pass H z)
    (v : V) : z v = C.label M (f.vertex v) := by
  let z' := z ∘ f.vertex.symm
  have pull (v) : z v = z' (f.vertex v) := by simp [z']
  have pass' := ((tests N K ε).pass_iso f z z' pull).mp hz
  exact (pull v).trans (congrFun (C.eq_label M pass') (f.vertex v))

variable {M} {H : MapRep N}

theorem label_iso (f : M.map.Iso H.map) (v) : C.label M v = C.label H (f.vertex v) :=
  C.label_iso_of_pass H f _ (C.pass M) v

/-- A relabelling preserves the actual natural-number patch identifiers. -/
def occEquiv (f : M.map.Iso H.map) : C.Occ M ≃ C.Occ H where
  toFun j := ⟨j.val, by
    obtain ⟨v,_,hv⟩ := Finset.mem_image.mp j.property
    exact Finset.mem_image.mpr ⟨f.vertex v, Finset.mem_univ _, (congrArg patchName (C.label_iso f v).symm).trans hv⟩⟩
  invFun j := ⟨j.val, by
    obtain ⟨w,_,hw⟩ := Finset.mem_image.mp j.property
    exact Finset.mem_image.mpr ⟨f.vertex.symm w, Finset.mem_univ _, (congrArg patchName (C.label_iso f.symm w).symm).trans hw⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem part_iso (f : M.map.Iso H.map) (v) :
    C.occEquiv f (C.part M v) = C.part H (f.vertex v) :=
  Subtype.ext (congrArg patchName (C.label_iso f v))

theorem block_iso (f : M.map.Iso H.map) (j : C.Occ M) (v) :
    v ∈ C.block M j ↔ f.vertex v ∈ C.block H (C.occEquiv f j) := by
  rw [C.mem_block, C.mem_block, ← C.part_iso f v]
  exact (C.occEquiv f).injective.eq_iff.symm

theorem record_iso (f : M.map.Iso H.map) (j : C.Occ M) :
    C.record M j = C.record H (C.occEquiv f j) :=
  PatchRecord.extract_iso f (C.block_iso f j) (C.name M) (C.name H)
    (fun v => congrArg vertexName (C.label_iso f v)) _ _ (C.label_iso f) _ _ _ _

theorem checked_iso (f : M.map.Iso H.map) (j : C.Occ M) :
    C.checked M j = C.checked H (C.occEquiv f j) := Subtype.ext (C.record_iso f j)

end System
end PortGraph.ReplacementChoices

end

end SpectralBooks
end LinearAlgebra
end OAI
