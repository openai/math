import OAI.Computability.BorderVNP.FiniteSewnFieldDirectory
import OAI.Computability.BorderVNP.PackedBankInheritedScalarBounds

/-! # Relative scalar bounds after restoring the old field site's supplied intervals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open Crossing Inherited Diagonal.ExternalSew CellSparse FiniteDiagonal

/-- A staged zero or equality row contains only unit tags, its width, and
the actual starting positions of the selected old and new intervals. -/
theorem Interval.marked_le (p : Interval) (s : Site) {n : ℕ} (old : p.oldStart+p.width ≤ s.incoming)
    (new : ∀ j, p.source=some j → j+p.width ≤ n) :
    ∀ a ∈ marked (p.record s), a.2 ≤ max 1 (s.size+n) := by
  intro a ha
  cases h : p.source with
  | none =>
    rw [Interval.record,h] at ha
    change a ∈ [(Kind.plain,0),(.plain,1),(.plain,p.width),(.bitAddress,s.work+p.oldStart),(.plain,0),(.plain,1)] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [Site.size] <;> omega
  | some j =>
    rw [Interval.record,h] at ha
    exact Slice.marked_le ⟨p.oldStart,j,p.width⟩ s old (new j h) a ha

/-- The maximum of the previous scalar bound and the actual successor site
extent controls all retained and newly appended row operands. -/
theorem stage_scalarBound (s : Site) {n U : ℕ} (before : s.ScalarBound U) (runs : List Interval)
    (read : Fin s.incoming → Option (Fin n)) (cover : Covers runs read) :
    (stage s n runs).ScalarBound (max U (max 1 (s.size+n))) := by
  intro a ha
  rw [Site.markedWords,stage_rows,List.flatMap_append,List.mem_append] at ha
  rcases ha with old | extra
  · exact (before a old).trans (le_max_left ..)
  · obtain ⟨r,hr,h⟩ := List.mem_flatMap.mp extra
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact (p.marked_le s (cover.oldFit p hp) (cover.newFit p hp) a h).trans (le_max_right ..)

variable {D : ℕ} {A P Free Cable U : Type} [Fintype A] [Fintype P] [Fintype Cable] [Fintype U]
    {width : A → ℕ} (N : Network D A width) (lane : P ↪ Σ a, Fin (width a))
    {cw : Cable → ℕ} (B : Bundle (FineView.layout N lane) Free Cable cw)
    (gw : U → ℕ) (freeLane : Free ↪ Σ u, Fin (gw u)) (owner : U → N.Site)
    (aligned : ∀ f, owner (freeLane f).1 = B.layout.attach f)
    {be bp : ℕ} (edge : (N.Edge ⊕ Cable) ↪ Fin be) (port : U ↪ Fin bp)
    {F : Type*} [Field F] {T : N.Tables F} (S : FieldSiteDirectory N T)

local notation "out" => Network.packExternal (Bundle.layout B) gw owner
local notation "site₀" => sewnSite N lane B gw freeLane owner aligned edge port S

/-- Apply the scalar bound to the actual private sewn site. The published
incoming widths and the genuine `programRead` provide every interval bound. -/
theorem sewnSite_scalarBound (v : N.Site) {bound : ℕ} (old : (S.site v).ScalarBound bound) :
    (site₀ v).ScalarBound (max bound (max 1 (site₀ v).size)) :=
  let f := programRead N lane B gw freeLane owner aligned edge port S v
  stage_scalarBound (S.site v) old (intervals f) f (intervals_cover f)

end Packing.SewnField

end BorderVNP
end Computability
end OAI
