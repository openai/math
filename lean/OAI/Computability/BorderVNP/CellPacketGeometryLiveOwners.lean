import OAI.Computability.BorderVNP.CellPacketGeometryLiveTemplate
import OAI.Computability.BorderVNP.CellPacketGeometryReferences

/-! # Fixed origin tags of the second sort's sparse chunk rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.LiveWords

open CellSparse Packet

variable {E I Orig Q : Type} {s C : ℕ}

/-- Descriptor origin tags: all cell headers, one per original or paid site box,
then the four tail reservations per cell. These are pinned before the site
owners are evaluated. -/
def Template.chunkLabels (T : Template E I Orig s C) : List (Owner s C) :=
  (List.finRange C).map Sum.inr ++
    (List.finRange s).flatMap (fun i => List.replicate (T.boxes i).length (.inl i)) ++
    (List.finRange C).flatMap (fun c => List.replicate 4 (.inr c))

private theorem referenceOwners (D : SiteWords.Directory I Orig C) (pin : Orig → Q) :
    (D.referenceRows pin).map Prod.fst = List.finRange C ++
      D.sites.flatMap (fun i => List.replicate (D.boxes i).length (D.owner i)) ++
      (List.finRange C).flatMap (fun c => List.replicate 4 c) := by
  have hs (i : Fin D.sites.length) : ((D.siteReferences pin i).map (Prod.mk (D.owner D.sites[i.val]))).map Prod.fst =
      List.replicate (D.boxes D.sites[i.val]).length (D.owner D.sites[i.val]) := by
    simp [SiteWords.Directory.siteReferences,Function.comp_def]
  have sites : (List.ofFn (fun i : Fin D.sites.length => List.replicate (D.boxes D.sites[i.val]).length
      (D.owner D.sites[i.val]))).flatten =
      D.sites.flatMap (fun i => List.replicate (D.boxes i).length (D.owner i)) := by
    rw [List.flatMap_def]
    exact congrArg List.flatten (List.ofFn_getElem_eq_map D.sites fun i => List.replicate (D.boxes i).length (D.owner i))
  simp only [SiteWords.Directory.referenceRows,List.map_append,List.map_flatten,List.map_ofFn,Function.comp_def,
    hs,sites]
  simp only [List.ofFn_eq_map,←List.flatMap_def]
  change (List.finRange C).map id ++ _ ++ _ = _
  rw [List.map_id]
  rfl

/-- The actual evaluated labels are exactly the cell-owner column of the concrete
canonical reference table, including the three initially blank descriptors. -/
theorem Template.chunkLabels_eval (T : Template E I Orig s C) (owner : Fin s → Fin C)
    (args : E → ℕ) (fields : Fin s → I → ℕ) (pin : Orig → Q) :
    T.chunkLabels.map (Sum.elim owner id) =
      ((T.directory owner args fields).referenceRows pin).map Prod.fst := by
  rw [referenceOwners]
  simp [Template.chunkLabels,Template.directory,List.map_flatMap,List.map_map,Function.comp_def]

end CellPacketGeometry.LiveWords

end BorderVNP
end Computability
end OAI
