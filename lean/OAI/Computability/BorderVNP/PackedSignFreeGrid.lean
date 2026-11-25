import OAI.Computability.BorderVNP.CellDirectorySigns
import OAI.Computability.BorderVNP.PackedBottomGridSite

/-! # Positive sparse factors in the original physically routed grid -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open CellSparse

/-- Every factor physically stored in this site's private boxes has positive sign. -/
def Site.SignFree (s : Site) : Prop := ∀ fs ∈ s.boxes, ∀ f ∈ fs, f.SignFree

/-- Retaining a site for a new cut changes its public wiring and preserves its factors. -/
theorem Site.SignFree.retain {s : Site} (hs : s.SignFree) (n : ℕ) (cuts : List Slice) :
    (s.retain n cuts).SignFree := hs

end Packing.Inherited

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports Inherited
open scoped Classical

/-- Replacing each unary source factor with its physical staged-use equality preserves positive sign. -/
theorem stage_signFree (rows : List Factor) (n : ℕ) (h : ∀ f ∈ rows, f.SignFree) :
    ∀ f ∈ stage n rows, f.SignFree := by
  induction rows generalizing n with
  | nil => simp [stage]
  | cons f fs ih =>
    obtain ⟨head,tail⟩ := List.forall_mem_cons.mp h
    cases f <;> simp only [stage,List.forall_mem_cons]
    all_goals exact ⟨head,ih _ tail⟩

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable (rules : ∀ u : {u : N.Site // cell u = v}, Rule N u.val)

/-- The real one-copy grid metadata has positive observations for source gates,
staged use equalities, both kinds of padded incidence, and unused report bits. -/
theorem stored_signFree (capFine capReport : ℕ) :
    ∀ f ∈ stored N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules capFine capReport,
      f.SignFree := by
  simp only [stored,wiring,List.forall_mem_append]
  refine ⟨⟨stage_signFree _ _ ?_,⟨⟨?_,?_⟩,?_⟩⟩,?_⟩
  · intro f hf
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hf
    cases rule : rules u <;> simp [ruleFactor,Factor.SignFree]
  · intro f hf
    obtain ⟨_,rfl⟩ := List.mem_ofFn.mp hf
    trivial
  all_goals
    intro f hf
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hf
    trivial

/-- All copies of the actual bottom grid bank use the same sign-free factor table. -/
theorem born_signFree (copies capFine capReport : ℕ) :
    (born N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
      copies capFine capReport).SignFree := by
  change ∀ fs ∈ [stored N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules capFine capReport],
    ∀ f ∈ fs, f.SignFree
  rw [List.forall_mem_singleton]
  exact stored_signFree N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules capFine capReport

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
