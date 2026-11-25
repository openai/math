import OAI.Computability.BorderVNP.PackedBankMergedLoad
import OAI.Computability.BorderVNP.PackedInheritedPlacementTies

/-! # The sorted physical cell directory with all final incidence ties

Empty public site slots contribute no records or boxes. The sorted owner
table fixes every site's merged private box prefix, while the canonical cell
slab pass fixes the absolute bit offsets. Their actual binding rows give the
static and expanded estimates for the installed directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalCell

open Crossing Shortening CellSparse InheritedBank CellAddresses BankBoxOrdinal
open scoped Classical

variable {V : Type} {s : ℕ} (row : V ↪ Fin s) (owner : Fin s → ℕ)

/-- Live site rows in increasing public ID order within the chosen cell. -/
noncomputable def sites (c : ℕ) : List V :=
  ((List.finRange s).filter fun i => owner i = c).filterMap (Function.partialInv row)

/-- Padded physical slot view: a live row contains its site's fragment, and an
unused row contributes no entries. -/
noncomputable def slots {α : Type*} (data : V → List α) (i : Fin s) := (Function.partialInv row i).elim [] data

private theorem slot_live {α : Type*} (data : V → List α) (v : V) : slots row data (row v) = data v := by
  rw [slots,Function.partialInv_left row.injective]
  rfl

/-- Sorting the padded physical slots gives precisely the fragments of the
occupied sites selected at this cell. -/
theorem sorted_fragments {α : Type*} (data : V → List α) (c : ℕ) :
    table owner (slots row data) c = (sites row owner c).flatMap data := by
  rw [table_eq_filtered,sites]
  generalize (List.finRange s).filter (fun i => decide (owner i = c)) = is
  induction is with
  | nil => rfl
  | cons i is ih => cases he : Function.partialInv row i <;> simp [slots,he] at ih ⊢ <;> exact ih

/-- Filtering the public ID order visits each occupied site at most once. -/
theorem sites_nodup (c : ℕ) : (sites row owner c).Nodup := by
  apply List.Nodup.filterMap _ ((List.nodup_finRange _).filter _)
  intro i j v hi hj
  have h1 : row v = i := (row.injective.isPartialInv v i).mp hi
  have h2 : row v = j := (row.injective.isPartialInv v j).mp hj
  exact h1.symm.trans h2

/-- The public site owner of every live selected row is the chosen cell. -/
theorem site_owner {c : ℕ} {v : V} (h : v ∈ sites row owner c) : owner (row v) = c := by
  obtain ⟨i,hi,hv⟩ := List.mem_filterMap.mp h
  have hv' := (row.injective.isPartialInv v i).mp hv
  rw [hv']
  exact of_decide_eq_true (List.mem_filter.mp hi).2

/-- Stable public merged ordinal of the site's first private box. -/
noncomputable def firstBox (state : V → Site) (v : V) :=
  base owner (fun i => (slots row (fun u => (state u).boxes) i).length) (row v)

/-- The actual segmented public owner/count scan emits this occupied site's first
box ordinal for every input that carries the physical sorted-table columns. -/
theorem firstBox_frame {k w : ℕ} (state : V → Site) (x : Input s k w → Bool)
    (ho : ∀ i, ownerWord x i = owner i)
    (hc : ∀ i, countWord x i = (slots row (fun u => (state u).boxes) i).length)
    (room : ∀ c, (table owner (slots row fun u => (state u).boxes) c).length < 2^w) (v : V) :
    ParseBatchSort.value (fun j => (frame s k w).eval x (row v,j)) = firstBox row owner state v := by
  have fits (c : ℕ) : (∑ i, if ownerWord x i = c then countWord x i else 0) < 2^w := by
    simpa only [ho,hc,table_length] using room c
  rw [frame_value x fits,funext ho,funext hc]
  rfl

/-- The actual sorted directory resolves the stable prefix to the original
one-copy box, independent of the site's physical location or row count. -/
theorem box_get (state : V → Site) {c : ℕ} {v : V} (hv : v ∈ sites row owner c)
    (i : ℕ) (hi : i < (state v).boxes.length) :
    ((sites row owner c).flatMap fun u => (state u).boxes).getD (firstBox row owner state v+i) [] =
      (state v).boxes.getD i [] := by
  let bs := slots row (fun u => (state u).boxes)
  have live : bs (row v) = (state v).boxes := slot_live row _ v
  let j : Fin (bs (row v)).length := ⟨i,live ▸ hi⟩
  have h := table_get owner bs (row v) j
  rw [site_owner row owner hv,sorted_fragments] at h
  rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem _ _ hi]
  change ((sites row owner c).flatMap fun u => (state u).boxes)[firstBox row owner state v+i]?.getD [] = _
  have he : ((sites row owner c).flatMap fun u => (state u).boxes)[firstBox row owner state v+i]? =
      some ((bs (row v)).get j) := h
  rw [he]
  change (bs (row v))[i]'j.isLt = _
  simp only [live]

variable {D n p : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
  (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin n)
  (portID : P ↪ Fin p) (state : N.Site → Site)

private noncomputable abbrev off (v : N.Site) :=
  siteBase N cell (cell v) siteID (fun u => (state u).size) ⟨v,rfl⟩

/-- Final owner-local binding rows for a live site, in the real cable and port ID order. -/
noncomputable def binding (v : N.Site) :=
  Placement.ties N cell (cell v) siteID edgeID portID state ⟨v,rfl⟩

/-- Fully merged sparse directory built from the actual physical site's
stable prefixes, translated records and canonical incident-word bindings. -/
noncomputable def directory (c : ℕ) (reports : List (List ℕ)) : Directory :=
  mergedSiteDirectory N state (sites siteID owner c) (off N cell siteID state)
    (firstBox siteID owner state) (binding N cell siteID edgeID portID state) reports

/-- The exact private table of the final packet is the stable owner table
computed from the padded site rows. -/
theorem directory_boxes (c : ℕ) (reports : List (List ℕ)) :
    (directory owner N cell siteID edgeID portID state c reports).boxes =
      table owner (slots siteID fun u => (state u).boxes) c :=
  (sorted_fragments siteID owner _ c).symm

/-- The final packet's records have the actual padded public row order. -/
theorem directory_rows (c : ℕ) (reports : List (List ℕ)) :
    (directory owner N cell siteID edgeID portID state c reports).records =
      table owner (slots siteID fun v => (state v).placedRows (off N cell siteID state v) (firstBox siteID owner state v) ++
        binding N cell siteID edgeID portID state v) c :=
  (sorted_fragments siteID owner _ c).symm

/-- Actual load of the final packet. The prefix lookup and the binding count
premises are discharged by the verified sorted and physical cable layouts. -/
theorem directory_load (c : ℕ) (reports : List (List ℕ)) (ho : ∀ v, owner (siteID v) = cell v)
    (schema : ∀ v, (state v).Schema) :
    let dir := directory owner N cell siteID edgeID portID state c reports
    let load := fun ex => localRecords N ex (fun v => (state v).staticNodes) (fun v => (state v).expandedLoad)
      (fun v => cell v = c)
    dir.recordMass ≤ 1026*load false+1 ∧ dir.boxMass ≤ load false+1 ∧
      Packet.storedMass dir ≤ load false ∧ dir.visitCount ≤ load true := by
  apply merged_directory_load N state (sites siteID owner c) _ _ _ reports (fun v => cell v = c)
    (sites_nodup siteID owner c) (fun v hv => (ho v).symm.trans (site_owner siteID owner hv)) (fun v _ => schema v)
    (fun v hv i hi => box_get siteID owner state hv i hi)
  · intro v _ r hr
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨_,_,_,_,rfl⟩
  · intro v _
    rw [binding,Placement.length_ties,tieRows]
    let inc : Incident N v ≃ {z : N.Edge // True ∧ (N.src z = v ∨ N.dst z = v)} :=
      Equiv.subtypeEquivRight fun _ => ⟨fun h => ⟨trivial,h⟩,And.right⟩
    apply Nat.add_le_add_right
    convert! (Fintype.card_congr inc).le using 1
    congr! 2

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
