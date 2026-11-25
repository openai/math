import OAI.Computability.BorderVNP.CellPacketGeometryHistoryAnchors

/-! # Removing inactive and non-anchor slots from a real cell's grouped source rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open CellSparse Packet Packing.Inherited Packing.BankPacket Packing.Word FrozenTape LiveWords SiteWords
open private filter_flat from OAI.Computability.BorderVNP.CellPacketGeometryHistoryAnchors

variable {a C cap d t : ℕ} {R B U V E Orig : Type}

private theorem truncate {A : Type*} {n : ℕ} (room : a≤n) (f : Fin n → List A) (g : Fin a → List A)
    (small : ∀ i : Fin a, f (i.castLE room)=g i) (large : ∀ i : Fin n, (a ≤ i.val) → f i=[]) :
    (List.finRange n).flatMap f = (List.finRange a).flatMap g := by
  obtain ⟨tail,rfl⟩ := Nat.exists_eq_add_of_le room
  rw [List.flatMap_def,List.flatMap_def,← List.ofFn_eq_map,← List.ofFn_eq_map,List.ofFn_add,List.flatten_append]
  have head : (fun i : Fin a => f (i.castLE room)) = g := funext small
  have rest : (fun i : Fin tail => f (Fin.natAdd a i)) = fun _ => [] := by
    funext i
    apply large
    simp
  rw [head,rest]
  simp

variable (S : Schema R B) (L : Schema U V) (boxes : Fin a → List (Source.Box Orig))
variable (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, (L.tags r).length≤cap)
variable (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E)) (args : E → ℕ)
variable (x : Pins R B d → Bool) (y : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)
local notation3 "G₀" => directory S L boxes sh lh priv rep args x y cells off box

private theorem anchor_owner (j : Fin a) : (G₀).owner (anchorSlot S L j) = (cells j).castSucc := by
  change (siteOf x y ((roster a S L).get (anchorSlot S L j))).elim _ _ = _
  rw [anchorSlot_get]
  rfl

private theorem hole_owner : (G₀).owner (holeSlot a S L) = Fin.last C := by
  change (siteOf x y ((roster a S L).get (holeSlot a S L))).elim _ _ = _
  rw [holeSlot_get]
  rfl

private theorem rows_beyond (i : Fin (roster a S L).length) (hi : a < i.val) : (G₀).rows i=[] := by
  change ((List.finRange _).filter _).flatMap _ = _
  have empty : ((List.finRange (roster a S L).length).filter fun z => decide (anchor S L x y z=i))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro z _ eqn
    have h := congrArg Fin.val (of_decide_eq_true eqn)
    unfold anchor at h
    cases key : siteOf x y ((roster a S L).get z) with
    | none => simp only [key,Option.elim_none,holeSlot] at h; omega
    | some j => simp only [key,Option.elim_some,anchorSlot] at h; omega
  rw [empty,List.flatMap_nil]

/-- At a real cell only anchor rows contribute, in exactly the original
physical site-ID order. All dynamically assigned chronological piece slots
have been emptied by regrouping. -/
theorem cell_rows (c : Fin C) :
    (G₀).cellRecords c.castSucc =
      (owned c cells (List.finRange a)).flatMap (fun j => (G₀).rows (anchorSlot S L j)) := by
  let G := G₀
  change ((List.finRange (roster a S L).length).filter (fun i => decide (G.owner i=c.castSucc))).flatMap G.rows =
    ((List.finRange a).filter (fun i => decide (cells i=c))).flatMap _
  rw [filter_flat,filter_flat]
  have room : a ≤ (roster a S L).length := by simp [roster]
  apply truncate room
  · intro j
    change (if decide (G.owner (anchorSlot S L j)=c.castSucc) then _ else []) = _
    rw [anchor_owner]
    simp only [Fin.castSucc_inj,decide_eq_true_eq]
    rfl
  · intro i hi
    by_cases hole : i.val=a
    · have eqn : i=holeSlot a S L := Fin.ext hole
      rw [eqn,hole_owner]
      have ne : Fin.last C ≠ c.castSucc := by intro h; have h' := congrArg Fin.val h; simp at h'; omega
      simp [ne]
    · have past : a < i.val := by omega
      rw [rows_beyond S L boxes sh lh priv rep args x y cells off box i past]
      simp

/-- Real cells retain exactly the anchor box tables. Opaque original keys and
known paid factors therefore use the same ordinal prefix as the final network. -/
theorem cell_boxes (c : Fin C) :
    (G₀).cellBoxes c.castSucc = (owned c cells (List.finRange a)).flatMap boxes := by
  let G := G₀
  change ((List.finRange (roster a S L).length).filter (fun i => decide (G.owner i=c.castSucc))).flatMap G.boxes = _
  rw [filter_flat]
  let feed (z : Slot a R U) : List (Source.Box Orig) :=
    if (siteOf x y z).elim (Fin.last C) (fun j => (cells j).castSucc) = c.castSucc
    then z.elim boxes (fun _ => []) else []
  change (List.finRange (roster a S L).length).flatMap (fun i => if decide _ then _ else []) = _
  have same (i : Fin (roster a S L).length) :
      (if decide (G.owner i=c.castSucc) then G.boxes i else []) = feed ((roster a S L).get i) := by
    change (if decide _ then _ else []) = if _ then _ else []
    simp only [decide_eq_true_eq]
    rfl
  refine (List.flatMap_congr (fun i _ => same i)).trans ?_
  have he := congrArg (List.flatMap feed) (List.map_get_finRange (roster a S L))
  simp only [List.flatMap_map] at he
  rw [he]
  have skip (z : Option (R ⊕ U)) : feed (.inr z) = [] := by simp [feed]
  have take (j : Fin a) : feed (.inl j) = if cells j=c then boxes j else [] := by simp [feed,siteOf]
  simp [roster,List.flatMap_map,skip,take,owned,filter_flat]

end CellPacketGeometry.History

end BorderVNP
end Computability
end OAI
