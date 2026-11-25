import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPatchRecordIso
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementOldMap

/-! # Re-extraction recovers the literal patch record

After expanding any collection of patch records, sorting by the certified
names in each occurrence returns exactly the saved list. Every numbered
internal pair and every distinguished stub is recovered.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace PortGraph.PatchRecord

variable {J A : Type} {K : ℕ} (R : J → PatchRecord K A)
  (C : StubPairing (fun j => (R j).shape.Stub))

/-- The actual ambient dart of a recorded slot in an expanded occurrence. -/
def ambient (j : J) (p : (R j).shape.Dart) : C.Edge (pieces R) × Bool :=
  (namedDarts R C).symm ⟨⟨j,p.1⟩,p.2⟩

theorem ambient_owner (j : J) (p : (R j).shape.Dart) :
    (graph R C).vertex (ambient R C j p).1 (ambient R C j p).2 = ⟨j,p.1⟩ :=
  (namedDarts_owner R C _).symm.trans (congrArg Sigma.fst ((namedDarts R C).apply_symm_apply _))

theorem ambient_internal (j : J) (e : (R j).shape.Wire) (b : Bool) :
    ambient R C j ((R j).shape.read (.inl (e,b))) = (Sum.inr ⟨j,e⟩,b) := by
  apply (namedDarts R C).symm_apply_eq.mpr
  cases b <;> rfl

theorem ambient_stub (j : J) (s : (R j).shape.Stub) :
    ambient R C j s.val = (Sum.inl (C.ends.symm ⟨j,s⟩).1,(C.ends.symm ⟨j,s⟩).2) := by
  apply (namedDarts R C).symm_apply_eq.mpr
  let f (q : Σ i, (R i).shape.Stub) :
      Σ v : vertices R, Fin ((R v.1).shape.typeAt v.2).degree.val :=
    ⟨⟨q.1,q.2.val.1⟩,q.2.val.2⟩
  exact congrArg f (C.ends.apply_symm_apply ⟨j,s⟩).symm

theorem ambient_pair (j : J) (p : (R j).shape.Dart) (h : (R j).shape.opposite p ≠ p) :
    ambient R C j ((R j).shape.opposite p) = cross (ambient R C j p) := by
  obtain ⟨(⟨e,(_|_)⟩|s),rfl⟩ := (R j).shape.read_bijective.surjective p
  · exact (ambient_internal R C j e true).trans (congrArg cross (ambient_internal R C j e false)).symm
  · change ambient R C j ((R j).shape.opposite ((R j).shape.opposite e.val)) = _
    rw [(R j).shape.involutive]
    exact (ambient_internal R C j e false).trans (congrArg cross (ambient_internal R C j e true)).symm
  · exact False.elim (h s.property)

theorem ambient_stub_exits (j : J) (p : (R j).shape.Dart) (h : (R j).shape.opposite p = p) :
    ((graph R C).vertex (ambient R C j p).1 (!(ambient R C j p).2)).1 ≠ j := by
  let s : (R j).shape.Stub := ⟨p,h⟩
  have he := congrArg Sigma.fst (C.ends.apply_symm_apply ⟨j,s⟩)
  have hx (e : C.Wire) (b : Bool) : (C.ends (e,!b)).1 ≠ (C.ends (e,b)).1 := by
    cases b with
    | false => exact (C.cross e).symm
    | true => exact C.cross e
  have ha := ambient_stub R C j s
  change ambient R C j p = _ at ha
  rw [ha]
  let q := C.ends.symm ⟨j,s⟩
  change ((C.assemble (pieces R)).vertex (.inl q.1) (!q.2)).1 ≠ j
  rw [StubPairing.vertex_exterior]
  exact fun h' => hx q.1 q.2 (h'.trans he.symm)

variable [Fintype J]

/-- The vertices in one expanded occurrence, as an actual finite subset. -/
def occurrence (j : J) : Finset (vertices R) := Finset.univ.filter (fun v => v.1 = j)

@[simp] theorem mem_occurrence (j : J) (v : vertices R) : v ∈ occurrence R j ↔ v.1 = j := by
  simp [occurrence]

def occurrenceEquiv (j : J) : (R j).shape.Vertex ≃ ↥(occurrence R j) where
  toFun i := ⟨⟨j,i⟩,(mem_occurrence R j _).mpr rfl⟩
  invFun v := (mem_occurrence R j _).mp v.property ▸ v.val.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨i,v⟩,h⟩
    obtain rfl : i = j := (mem_occurrence R j _).mp h
    rfl

theorem occurrence_card (j : J) : (occurrence R j).card = (R j).shape.size.val := by
  simpa only [Fintype.card_coe, PatchShape.Vertex, Fintype.card_fin] using
    (Fintype.card_congr (occurrenceEquiv R j)).symm

theorem occurrence_nonempty (j : J) : (occurrence R j).Nonempty := Finset.card_pos.mp
  ((R j).shape.positive.trans_eq (occurrence_card R j).symm)

theorem occurrence_small (j : J) : (occurrence R j).card ≤ K :=
  (occurrence_card R j).trans_le (Nat.le_of_lt_succ (R j).shape.size.isLt)

variable (orient : ∀ (e : C.Wire) (b : Bool), (C.ends (e,b)).2.val.side = b)
  (r : vertices R) (hc : (graph R C).ConnectedFrom r)
  (hr : ∀ v : vertices R, ((R v.1).shape.typeAt v.2).root = decide (v = r))

include orient hr in
/-- The reverse construction followed by canonical extraction recovers each
record, including its full certificate fields, internal edge pairs, and stubs. -/
theorem extract_asMap (name : vertices R ↪ ℕ) (j : J)
    (sorted : StrictMono (fun i : (R j).shape.Vertex => name ⟨j,i⟩)) :
    extract (asMap R C r hc) (labels R) (occurrence R j) name
      (occurrence_nonempty R j) (occurrence_small R j) = R j := by
  apply extract_presented _ _ _ _ _ _ _ (occurrenceEquiv R j) sorted
    (fun i => asMap_typeAt R C orient r hc hr ⟨j,i⟩) (fun _ => rfl)
    (ambient R C j) (ambient_owner R C j)
  · intro p
    refine (asMap_portNumber R C r hc _ _).trans ?_
    exact congrArg (fun q => q.2.val) ((namedDarts R C).apply_symm_apply ⟨⟨j,p.1⟩,p.2⟩)
  · intro p h
    exact fun hin => ambient_stub_exits R C j p h ((mem_occurrence R j _).mp hin)
  · exact ambient_pair R C j

end PortGraph.PatchRecord

end

end SpectralBooks
end LinearAlgebra
end OAI
