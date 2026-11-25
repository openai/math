import OAI.Computability.BorderVNP.CellPacketGeometryOriginalSlots
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryAnchors

/-! # One original opaque source entry at each genuine retained site host -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open CellSparse Packet Packing.Inherited FrozenTape SiteWords LiveWords

variable {a C cap d t entries : ℕ} {R B U V E : Type}

/-- An original site receives its immutable one-copy description. All other
anchors contain only public one-copy factor tables in their prescribed order. -/
noncomputable def originalBoxes (entry : Fin entries ↪ Fin a) (known : Fin a → List (List Factor))
    (i : Fin a) : List (Source.Box (Fin entries)) :=
  (Function.partialInv entry i).elim ((known i).map Sum.inl) fun j => [.inr j]

/-- Exactly the host in the original transmission schedule has this opaque box. -/
theorem originalBoxes_at (entry : Fin entries ↪ Fin a) (known : Fin a → List (List Factor)) (j : Fin entries) :
    originalBoxes entry known (entry j) = [.inr j] := by simp [originalBoxes,Function.partialInv_left entry.injective]

/-- Erasing public one-copy factors leaves precisely the inverse host lookup. -/
theorem originalBoxes_private (entry : Fin entries ↪ Fin a) (known : Fin a → List (List Factor)) (i : Fin a) :
    (originalBoxes entry known i).filterMap Sum.getRight? = (Function.partialInv entry i).toList := by
  cases h : Function.partialInv entry i <;> simp [originalBoxes,h,List.filterMap_map]

variable (S : Schema R B) (L : Schema U V) (entry : Fin entries ↪ Fin a) (known : Fin a → List (List Factor))
variable (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, (L.tags r).length≤cap)
variable (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E)) (args : E → ℕ)
variable (x : Pins R B d → Bool) (y : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)

local notation3 "G₀" => directory S L (originalBoxes entry known) sh lh priv rep args x y cells off box

/-- The full selected box roster in the actual final geometry contains precisely
the original transmission IDs in increasing host order. No birth, retention,
subdivision or final-binding row slot carries an additional private box. -/
theorem original_roster :
    (G₀).originalRows.map Prod.snd = (List.finRange a).filterMap (Function.partialInv entry) := by
  let G := G₀
  let keys (z : Slot a R U) := z.elim (fun i => (Function.partialInv entry i).toList) (fun _ => [])
  have each (i : Fin (roster a S L).length) :
      (((G.boxes i).filterMap Sum.getRight?).map (Prod.mk (G.owner i))).map Prod.snd =
        keys ((roster a S L).get i) := by
    change (((((roster a S L).get i).elim (originalBoxes entry known) (fun _ => [])).filterMap Sum.getRight?).map (Prod.mk (G.owner i))).map Prod.snd = _
    cases h : (roster a S L).get i <;> simp [keys,originalBoxes_private,List.map_map,Function.comp_def]
  change (G.originalRows.map Prod.snd) = _
  rw [Directory.originalRows,List.map_flatMap]
  change (List.finRange (roster a S L).length).flatMap _ = _
  refine (List.flatMap_congr (fun i _ => each i)).trans ?_
  have eqn := congrArg (List.flatMap keys) (List.map_get_finRange (roster a S L))
  simp only [List.flatMap_map] at eqn
  rw [eqn]
  simp [roster,List.flatMap_map,keys,List.filterMap_eq_flatMap_toList]

/-- In particular the source of every selected opaque box is an injectively
named entry of the actual distributed original-input directory. -/
theorem original_once : ((G₀).originalRows.map Prod.snd).Nodup := by
  rw [original_roster]
  apply List.Nodup.filterMap _ (List.nodup_finRange a)
  intro i j u left right
  exact ((entry.injective.isPartialInv u i).mp left).symm.trans ((entry.injective.isPartialInv u j).mp right)

end CellPacketGeometry.History

end BorderVNP
end Computability
end OAI
