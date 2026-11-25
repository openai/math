import OAI.Computability.BorderVNP.PackedSewnWireFragments
import OAI.Computability.BorderVNP.FiniteSewnFieldPortCover
import OAI.Computability.BorderVNP.DiagonalExternalSewFieldFrame

/-! # The true old-wire incidence roster in the exterior sewing fragment rectangle -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.WireFragments

open Crossing Inherited CellAddressCircuit CellAddressPhysical ParseBatchSort
open Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport
open scoped Classical

variable {D : ℕ} {A : Type} {bits : A → ℕ} (L : Network D A bits)

/-- One live source interval for each positive-width old cable at a physical site. -/
abbrev Incidences := Σ v : L.Site, {z : Incident L v // 0 < L.width z.val}

variable {m : ℕ} (edgeID : L.Edge ↪ Fin m)

/-- The source owns a loop's unique row. Every other cable has two distinct physical ends. -/
noncomputable def index (a : Incidences L) : Fin (2*m) :=
  ordinal (edgeID a.2.val.val,decide (L.src a.2.val.val = a.1))

/-- Different positive physical incidences get different source slots. -/
theorem index_injective : Function.Injective (index L edgeID) := by
  rintro ⟨v,⟨⟨e,he⟩,we⟩⟩ ⟨u,⟨⟨f,hf⟩,wf⟩⟩ eq
  have pair := ordinal.injective eq
  have ef : e=f := edgeID.injective (congrArg Prod.fst pair)
  subst f
  have side : decide (L.src e=v) = decide (L.src e=u) := congrArg Prod.snd pair
  have loc : v=u := by
    by_cases h : L.src e=v
    · have h' : L.src e=u := of_decide_eq_true (side.symm.trans (decide_eq_true h))
      exact h.symm.trans h'
    · have h' : L.src e≠u := of_decide_eq_false (side.symm.trans (decide_eq_false h))
      exact (he.resolve_left h).symm.trans (hf.resolve_left h')
  subst u
  rfl

variable {s n M N C k w : ℕ} {σ τ : Type} [Fintype σ] [Fintype τ]
variable (F : Fields s m n C w k w σ) (B : Fields s M N C w k w τ)
variable (old : σ → τ) (present : Fin m → σ) (retained : Fin m → Fin M)
variable (siteID : L.Site ↪ Fin s) (portID : A ↪ Fin n) (x : τ → Bool)
variable (beforeOK : Views.EndpointData L F siteID edgeID portID (x ∘ old))
variable (occupied : ∀ i, x (old (present i)) = true ↔ i ∈ Set.range edgeID)

include beforeOK occupied in
/-- The active set of the actual sparse gate frame is precisely the image of the
positive physical incidences, including on padded directories with empty slots. -/
theorem active_range (i : Fin (2*m)) :
    Fragment.active ((frame F B old present retained).eval x) i = true ↔ i ∈ Set.range (index L edgeID) := by
  obtain ⟨⟨a,src⟩,rfl⟩ := ordinal.surjective i
  rw [frame_active]
  constructor
  · rintro ⟨occ,pos,side⟩
    obtain ⟨e,rfl⟩ := (occupied a).mp occ
    have hp : 0<L.width e := (beforeOK.edge e) ▸ pos
    cases src with
    | true => exact ⟨⟨L.src e,⟨⟨e,Or.inl rfl⟩,hp⟩⟩,by simp [index]⟩
    | false =>
      have unequal := side.resolve_left (by decide)
      have diff : L.src e ≠ L.dst e := by
        intro h
        apply unequal
        change value ((x ∘ old) ∘ F.ptr (.inl (.inl (edgeID e)))) =
          value ((x ∘ old) ∘ F.ptr (.inl (.inr (edgeID e))))
        rw [beforeOK.src,beforeOK.dst,h]
      exact ⟨⟨L.dst e,⟨⟨e,Or.inr rfl⟩,hp⟩⟩,by simp [index,diff]⟩
  · rintro ⟨⟨v,⟨⟨e,hv⟩,hp⟩⟩,eq⟩
    have same := ordinal.injective eq
    have ea : edgeID e=a := congrArg Prod.fst same
    have sa : decide (L.src e=v)=src := congrArg Prod.snd same
    subst a
    subst src
    refine ⟨(occupied _).mpr ⟨e,rfl⟩,(beforeOK.edge e).symm ▸ hp,?_⟩
    by_cases hs : L.src e=v
    · exact Or.inl (decide_eq_true hs)
    · right
      have hd := hv.resolve_left hs
      change value ((x ∘ old) ∘ F.ptr (.inl (.inl (edgeID e)))) ≠ value ((x ∘ old) ∘ F.ptr (.inl (.inr (edgeID e))))
      rw [beforeOK.src,beforeOK.dst]
      exact fun h => hs ((siteID.injective (F.sites.injective (Fin.ext h))).trans hd)

end Packing.SewnField.WireFragments

end BorderVNP
end Computability
end OAI
