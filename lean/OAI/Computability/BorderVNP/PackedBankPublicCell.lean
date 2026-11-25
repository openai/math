import OAI.Computability.BorderVNP.PackedBankPublicNodes
import OAI.Computability.BorderVNP.PackedBankSortedCell
import OAI.Computability.BorderVNP.PackedInheritedFields

/-! # Public geometry load of the true final sorted site packet

Only public row words, guards, and the references to one-copy boxes are
charged in this pass. A private bottom truth table can be large while its
box contributes a single public reference. The final incidence bindings
add one fixed public equality for each live incident word.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalCell

open Crossing Shortening CellSparse InheritedBank Finset
open scoped Classical
open private equalityCosts from OAI.Computability.BorderVNP.PackedBankBirthCharges
open private off from OAI.Computability.BorderVNP.PackedBankSortedCell
open private recordWordLength guardShift from OAI.Computability.BorderVNP.PackedBankInheritedPlacedMass

variable {D s n p : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
  (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin n) (portID : P ↪ Fin p)
  (owner : Fin s → ℕ) (state : N.Site → Site)

/-- The public row and box-reference load used by the stable geometry frame. -/
noncomputable def publicLoad (c : ℕ) :=
  localRecords N false (fun v => (state v).publicNodes) (fun _ => 0) (fun v => cell v = c)

private noncomputable abbrev singleton (v : N.Site) :=
  localRecords N false (fun u => (state u).publicNodes) (fun _ => 0) (fun u => u = v)

private theorem group (c : ℕ) (ho : ∀ v, owner (siteID v) = cell v) (f : N.Site → ℕ) (C : ℕ)
    (one : ∀ v, f v ≤ C*singleton N state v) :
    ((sites siteID owner c).map f).sum ≤ C*publicLoad N cell state c := by
  let near := univ.filter fun v => cell v = c
  have h : (fun v => cell v = c) = (fun u => id u ∈ near) := by funext v; apply propext; simp [near]
  rw [publicLoad,h,localRecords_near,mul_sum,← List.sum_toFinset _ (sites_nodup siteID owner c)]
  apply (sum_le_sum (fun v _ => one v)).trans
  exact sum_le_sum_of_subset (fun v hv => by simpa [near] using (ho v).symm.trans (site_owner siteID owner (List.mem_toFinset.mp hv)))

private theorem site_le (v : N.Site) : (state v).publicNodes ≤ singleton N state v := by
  simp [singleton,localRecords,testedWidth,boxCost,recordCost]
  omega

/-- The public row-order cost of the final bindings uses the sparse structural
tile count, even if a previously supplied private factor table is much larger. -/
theorem binding_count_public (v : N.Site) :
    (binding N cell siteID edgeID portID state v).length ≤ singleton N state v := by
  rw [binding,Placement.length_ties]
  apply le_trans ?_ (tieRows_le N false (fun u => (state u).publicNodes) (fun _ => 0) (fun _ => True) v)
  unfold tieRows
  apply Nat.add_le_add_right
  let eq : Incident N v ≃ {z : N.Edge // True ∧ (N.src z = v ∨ N.dst z = v)} :=
    Equiv.subtypeEquivRight fun _ => ⟨fun h => ⟨trivial,h⟩,And.right⟩
  convert! (Fintype.card_congr eq).le using 1
  congr! 2

/-- The actual final public wiring word sequence, its guard syntax, and all
stored-box *references* have linear size in the public-only physical load. -/
theorem directory_public_load (c : ℕ) (reports : List (List ℕ)) (ho : ∀ v, owner (siteID v) = cell v) :
    let dir := directory owner N cell siteID edgeID portID state c reports
    let M := publicLoad N cell state c
    (Packet.fieldList Packet.record dir.records).length ≤ 10*M+1 ∧
      dir.recordMass ≤ 1026*M+1 ∧ dir.boxes.length ≤ M := by
  intro dir M
  let is := sites siteID owner c
  let extra := binding N cell siteID edgeID portID state
  let rs (v : N.Site) := (state v).placedRows (off N cell siteID state v) (firstBox siteID owner state v) ++ extra v
  have each (v : N.Site) :
      ((rs v).flatMap Packet.record).length ≤ 10*singleton N state v ∧
      Directory.recordNodes (rs v) ≤ 1026*singleton N state v ∧ (state v).boxes.length ≤ singleton N state v := by
    let s := state v
    let placed := s.placedRows (off N cell siteID state v) (firstBox siteID owner state v)
    have words : (placed.flatMap Packet.record).length = (s.rows.flatMap Packet.record).length := by
      simp [placed,Site.placedRows,List.length_flatMap,Function.comp_def,recordWordLength]
    have guards : Directory.recordNodes placed = Directory.recordNodes s.rows := by
      simp only [placed,Site.placedRows,Directory.recordNodes,List.length_map,List.map_map,Function.comp_def,
        Record.rebaseBox_guardMassBound,guardShift]
    have h := equalityCosts (extra v) (by
      intro r hr; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr; exact ⟨_,_,_,_,rfl⟩)
    have links : (extra v).length ≤ singleton N state v := binding_count_public N cell siteID edgeID portID state v
    have ht := site_le N state v
    change (Packet.fieldList Packet.record s.rows).length + Directory.recordNodes s.rows + s.boxes.length ≤ _ at ht
    simp only [Packet.fieldList,List.length_cons] at ht
    change ((placed++extra v).flatMap Packet.record).length ≤ _ ∧ Directory.recordNodes (placed++extra v) ≤ _ ∧ s.boxes.length ≤ _
    rw [List.flatMap_append,List.length_append,words,h.1,Directory.recordNodes_append,guards,h.2]
    omega
  have words := group N cell siteID owner state c ho _ 10 (fun v => (each v).1)
  have guards := group N cell siteID owner state c ho _ 1026 (fun v => (each v).2.1)
  have boxes : (is.map (fun v => (state v).boxes.length)).sum ≤ M := by
    simpa only [one_mul] using group N cell siteID owner state c ho _ 1 (fun v => by simpa only [one_mul] using (each v).2.2)
  have records : dir.records = is.flatMap rs := rfl
  refine ⟨?_,(Directory.mergeSites_recordMass is _ rs reports).le.trans (Nat.add_le_add_right guards _),?_⟩
  · simp only [Packet.fieldList,List.length_cons,records,List.flatMap_assoc,List.length_flatMap]
    exact Nat.succ_le_succ (by simpa only [List.length_flatMap] using words)
  · change (is.flatMap fun v => (state v).boxes).length ≤ M
    exact (List.length_flatMap ..).le.trans boxes

/-- A site's marked geometry word tape occupies exactly its stored public
record word count, prior to final relocation. -/
theorem markedWords_le_public (s : Site) : s.markedWords.length ≤ s.publicNodes := by
  have h (r : Record) : (marked r).length = (Packet.record r).length := by
    have eq := congrArg List.length (marked_move 0 0 r)
    rw [List.length_map,recordWordLength] at eq
    exact eq
  have lengths : s.markedWords.length = (s.rows.flatMap Packet.record).length := by
    simp [Site.markedWords,List.length_flatMap,h]
  rw [lengths]
  have size := s.packetRows_le_publicNodes
  simp only [Packet.fieldList,List.length_cons] at size
  omega

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
