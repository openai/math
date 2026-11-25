import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementRecoverChoices

/-! # Comparing the recovered old decorated maps

The patch identifier is a field of the checked record. Thus matching the saved
record also matches its unique occurrence on the recovered representative.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace PortGraph.ReplacementChoices.System

universe u

variable {N K : ℕ} {ε : ℝ} (C : System N K ε) {M H : MapRep N}

theorem checked_patchId (j : C.Occ M) : (C.checked M j).patchId = j.val :=
  C.record_patch M j _

theorem checked_injective : Function.Injective (C.checked M) := by
  intro j k h
  apply Subtype.ext
  exact ((C.checked_patchId j).symm.trans (congrArg Checked.patchId h)).trans (C.checked_patchId k)

/-- Equality of the transported record-term pairs at every occurrence suffices
for equality of the entire transported choice assignment. -/
theorem choice_iso_of_sigma (Term : Checked N K ε → Type u) (f : M.map.Iso H.map)
    (a : (C.family Term).Label M) (b : (C.family Term).Label H)
    (same : ∀ j, (⟨C.checked H (C.occEquiv f j), b (C.occEquiv f j)⟩ : Σ Q, Term Q) =
      ⟨C.checked M j, a j⟩) :
    (C.family Term).IsIso ⟨M,a⟩ ⟨H,b⟩ := by
  refine ⟨f,funext fun k => ?_⟩
  obtain ⟨j,rfl⟩ := (C.occEquiv f).surjective k
  exact (Sigma.mk.inj_iff.mp ((C.family_move_sigma Term f a j).trans (same j).symm)).2.eq

namespace Recovered

variable {C} {J : Type} {R : J → Checked N K ε} {fV}
  (d : C.Recovered R M fV) (Term : Checked N K ε → Type u) (t : ∀ j, Term (R j))

/-- The decoded choices agree with a given old summand as soon as the bare
maps are isomorphic and every saved term matches its advertised occurrence. -/
theorem isIso_of_terms (f : M.map.Iso H.map) (a : (C.family Term).Label H)
    (occ : J → C.Occ H)
    (terms : ∀ j, (⟨C.checked H (occ j), a (occ j)⟩ : Σ Q, Term Q) = ⟨R j,t j⟩) :
    (C.family Term).IsIso ⟨M,d.choices Term t⟩ ⟨H,a⟩ := by
  apply C.choice_iso_of_sigma Term f
  intro k
  obtain ⟨j,rfl⟩ := d.occ.surjective k
  have he : C.occEquiv f (d.occ j) = occ j := C.checked_injective
    (((C.checked_iso f _).symm.trans (d.checked j)).trans (congrArg Sigma.fst (terms j)).symm)
  rw [he]
  exact (terms j).trans (d.choices_sigma Term t j).symm

/-- Two recovered representatives of the same old data define isomorphic
old choices whenever their numbered bare maps are isomorphic. -/
theorem isIso {gV} (d' : C.Recovered R H gV) (f : M.map.Iso H.map) :
    (C.family Term).IsIso ⟨M,d.choices Term t⟩ ⟨H,d'.choices Term t⟩ :=
  d.isIso_of_terms Term t f _ d'.occ (d'.choices_sigma Term t)

end Recovered
end PortGraph.ReplacementChoices.System

end

end SpectralBooks
end LinearAlgebra
end OAI
