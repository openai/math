import OAI.Computability.BorderVNP.CellPacketGeometryHistoryFields

/-! # Site-major order of every genuine historical and final row in the native template -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open CellSparse Packet Packing.Inherited Packing.BankPacket Packing.Word FrozenTape LiveWords SiteWords

variable {a C cap d t : ℕ} {R B U V E Orig : Type}

private theorem filter_flat {X A : Type*} (xs : List X) (test : X → Bool) (f : X → List A) :
    (xs.filter test).flatMap f = xs.flatMap (fun z => if test z then f z else []) := by
  induction xs with
  | nil => rfl
  | cons z xs ih => cases h : test z <;> simp [h,ih]

private theorem filter_single {X A : Type*} (xs : List X) (test : X → Bool) (f : X → A) :
    xs.flatMap (fun z => if test z then [f z] else []) = (xs.filter test).map f := by
  induction xs with
  | nil => rfl
  | cons z xs ih => cases h : test z <;> simp [h,ih]

private theorem addr_eq (S : Schema R B) (L : Schema U V) (z : Option (Fin a)) (j : Fin a) :
    z.elim (holeSlot a S L) (anchorSlot S L) = anchorSlot S L j ↔ z=some j := by
  cases z with
  | none =>
    simp only [Option.elim_none,reduceCtorEq,iff_false,Fin.ext_iff,holeSlot,anchorSlot]
    omega
  | some i =>
    simp [anchorSlot,Fin.ext_iff]

variable (S : Schema R B) (L : Schema U V) (boxes : Fin a → List (Source.Box Orig))
variable (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, (L.tags r).length≤cap)
variable (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E)) (args : E → ℕ)
variable (x : Pins R B d → Bool) (y : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)

/-- The branch directory fed by the actual public numeric source columns,
then stably regrouped at the physical site anchors by the native geometry. -/
def directory : SiteWords.Directory (Fin (roster a S L).length) Orig (C+1) :=
  let T := template S L boxes sh lh priv rep
  let words := fun i => scalarArgs S L x y off box ((roster a S L).get i)
  (T.directory (cellOf S L x y cells) args words).regroup (anchor S L x y)

local notation3 "G₀" => directory S L boxes sh lh priv rep args x y cells off box

/-- A real site's true historical rows precede all of its final absolute
cable/port bindings, regardless of their physical input rectangle positions. -/
theorem rows_at_anchor (j : Fin a) :
    (G₀).rows (anchorSlot S L j) =
      (S.selected x j.val).map (fun r => ((S.typed x r).shift (off j)).rebaseBox (box j)) ++
        (L.selected y j.val).map (L.typed y) := by
  let feed := fun z : Slot a R U => if siteOf x y z=some j then rowRecords S L x y off box z else []
  have slot (i : Fin (roster a S L).length) :
      (if decide (anchor S L x y i=anchorSlot S L j) then
        (format S L sh lh ((roster a S L).get i)).map
          (RecordCode.read (scalarArgs S L x y off box ((roster a S L).get i))) else []) =
        feed ((roster a S L).get i) := by
    simp [anchor,addr_eq,format_read,feed]
  change ((List.finRange _).filter _).flatMap _ = _
  rw [filter_flat]
  change (List.finRange _).flatMap (fun i => if decide (anchor S L x y i=anchorSlot S L j) then _ else []) = _
  refine (List.flatMap_congr (l := List.finRange (roster a S L).length) (fun i _ => slot i)).trans ?_
  have eqn := congrArg (List.flatMap feed) (List.map_get_finRange (roster a S L))
  simp only [List.flatMap_map] at eqn
  rw [eqn]
  have aRows : ((List.finRange a).map Sum.inl).flatMap feed = [] :=
    List.flatMap_eq_nil_iff.mpr (fun z hz => by obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz; simp [feed,rowRecords])
  have hole : feed (.inr none) = [] := by simp [feed,rowRecords]
  have hist (r : R) : feed (.inr (some (.inl r))) =
      if x (.inl (r,.inl ())) && decide (owner x r=j.val) then
        [((S.typed x r).shift (off j)).rebaseBox (box j)] else [] := by
    by_cases h : name a x r=some j
    · obtain ⟨live,atJ⟩ := (name_eq x r j).mp h
      simp [feed,siteOf,h,rowRecords,live,atJ]
    · have skip := (name_eq x r j).not.mp h
      simp [feed,siteOf,h,skip]
  have bind (u : U) : feed (.inr (some (.inr u))) =
      if y (.inl (u,.inl ())) && decide (owner y u=j.val) then [L.typed y u] else [] := by
    simp [feed,siteOf,rowRecords,name_eq]
  simp only [roster,List.flatMap_append,aRows,List.nil_append,List.flatMap_singleton,hole,List.flatMap_map,
     hist,bind,filter_single,Schema.selected]

/-- All true records at a live physical site coincide with the installed
network state and its genuine emitted final incidence bindings. -/
theorem rows_at_image {A : Type} (siteID : A ↪ Fin a) (states : A → Site) (binding : A → List Record)
    (historical : S.Image x (siteID.trans Fin.valEmbedding) states)
    (final : ∀ v, L.atSite y (siteID v).val = (binding v).map marked) (v : A) :
    (G₀).rows (anchorSlot S L (siteID v)) =
      (states v).placedRows (off (siteID v)) (box (siteID v)) ++ binding v := by
  rw [rows_at_anchor]
  have first := S.placed_atSite x (siteID.trans Fin.valEmbedding) states historical v (off (siteID v)) (box (siteID v))
  exact congrArg₂ List.append first (L.typed_section y (siteID v).val _ (final v))

end CellPacketGeometry.History

end BorderVNP
end Computability
end OAI
