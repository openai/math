import OAI.Computability.BorderVNP.DiagonalExternalGridBlockHosts
import OAI.Computability.BorderVNP.DiagonalExternalSewFieldRows

/-! # Recovering a sewn block host from the actual grouped terminal port

In the flattened network the original bundle and tile still label a grouped
external port. Its attachment supplies the vertex for every real processor
lane in that block and for every exterior interval endpoint.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.GridHosts

open Crossing Packing TeamContraction FieldExport
open scoped Classical

variable {R r t pins link inner n D groups tiles copies : ℕ} {Edge : Type}
    (G : Wiring R r t pins link inner n Edge) (pos : 0<tiles) (count : groups*copies = R+1)
    (L : Network D (Fin groups × Fin tiles) (fun _ => copies*blockWidth (r*n) tiles))

/-- Use the actual grouped argument's attachment. An index outside the initial
rectangle reads the first tile, the same convention as the bottom deck grid. -/
def attachedHosts : BlockHosts (FineView.layout L (groupedLane G tiles pos groups copies count))
    (Equiv.refl (PublicPort R r (G.program.length+t) link)) (blockWidth (r*n) tiles) := by
  refine ⟨fun z => L.attach ((teamBlocks groups copies count z.1).1,if hi : z.2 < tiles then ⟨z.2,hi⟩ else ⟨0,pos⟩),?_⟩
  intro p
  let a := groupedLane G tiles pos groups copies count p
  let g := blockWidth (r*n) tiles
  have coords := groupedLane_coordinates G pos groups copies count p
  have index : (teamOrdinal p).val/g < tiles := coords.2.1 ▸ a.1.2.isLt
  change L.attach a.1 = _
  apply congrArg L.attach
  apply Prod.ext
  · rfl
  · apply Fin.ext
    have raw : (rawBlock g p).2 = (teamOrdinal p).val/g := by rw [teamOrdinal_val]; rfl
    rw [raw,dite_eq_left index]
    exact coords.2.1

/-- The static pointer name used for each original team and block. -/
def attachedName (offset : Fin groups → ℕ) (copies team block : ℕ) : ℕ :=
  if h : team/copies < groups then offset ⟨team/copies,h⟩+block else 0

/-- All exported block pointers name exactly the physical attachment, including
tiles with no live processor lane. -/
theorem attached_name {s : ℕ} (site : L.Site ↪ Fin s) (offset : Fin groups → ℕ)
    (origin : ∀ z : Fin groups × Fin tiles, (site (L.attach z)).val = offset z.1+z.2.val)
    (u : Fin (R+1)) (i : ℕ) (hi : i < tiles) :
    attachedName offset copies u.val i = (site ((attachedHosts G pos count L).host (u,i))).val := by
  let group := (teamBlocks groups copies count u).1
  have fit : u.val/copies < groups := group.isLt
  rw [attachedName,dite_eq_left fit]
  change _ = (site (L.attach (group,if h : i<tiles then ⟨i,h⟩ else ⟨0,pos⟩))).val
  rw [dite_eq_left hi]
  exact (origin (group,⟨i,hi⟩)).symm

/-- The attachment-defined table agrees with the physical grid constructor's
retained vertex map at each original block. -/
theorem attached_eq_retained {q d : ℕ}
    (order : Fin (tileCount q d) ≃ (Fin q → Cover.Deck (d+2)))
    (position : (Fin q → Cover.Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (N : Network D (Fin groups × Fin (tileCount q d)) (fun _ => copies*inputBlockWidth r n q d))
    (keep : Retains (groupedBottom G q d order position groups copies) N) (u : Fin (R+1)) (i : ℕ) :
    (attachedHosts G Fintype.card_pos count N).host (u,i) =
      (blockHosts G q d order position groups copies count N keep).host (u,i) := by
  let grp := (teamBlocks groups copies count u).1
  let v : Fin (tileCount q d) := if h : i < tileCount q d then ⟨i,h⟩ else ⟨0,Fintype.card_pos⟩
  have owner : order v = baseHost order i := by
    dsimp only [v,baseHost,tileCount]
    split <;> rfl
  exact (keep.attach (grp,v)).trans (congrArg (fun z => keep.site ⟨grp,z⟩) owner)

end Diagonal.ExternalSew.GridHosts

end BorderVNP
end Computability
end OAI
