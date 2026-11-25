import OAI.Computability.BorderVNP.PackedBankSortedCell
import OAI.Computability.BorderVNP.DiagonalTallyCellReports

/-! # Static private-cell compiler premises for the actual sorted packet

The reports use the real little-endian count fields at the end of the
assignment. The record-count estimate counts one row per live incident
binding, independently of the number of generated guard nodes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalCell

open Crossing Shortening CellSparse CellAddresses InheritedBank DiagonalTallyCellReports
open scoped Classical
open private ordered_sum_le site_load_le from OAI.Computability.BorderVNP.PackedBankMergedLoad
open private off from OAI.Computability.BorderVNP.PackedBankSortedCell

variable {D s n p : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
  (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin n) (portID : P ↪ Fin p)
  (owner : Fin s → ℕ) (state : N.Site → Site)

private noncomputable abbrev load (c : ℕ) (ex : Bool) :=
  localRecords N ex (fun v => (state v).staticNodes) (fun v => (state v).expandedLoad) (fun v => cell v = c)

/-- A public row contributes one entry before the guard is expanded. All final
physical incidence ties together contribute at most one more local record
count, even in a cell containing self-loops or empty cables. -/
theorem record_count_le (c : ℕ) (reports : List (List ℕ)) (ho : ∀ v, owner (siteID v) = cell v) :
    (directory owner N cell siteID edgeID portID state c reports).records.length ≤ 2*load N cell state c false := by
  let is := sites siteID owner c
  let rows (v : N.Site) := (state v).placedRows (off N cell siteID state v) (firstBox siteID owner state v) ++
    binding N cell siteID edgeID portID state v
  change (is.flatMap rows).length ≤ _
  rw [List.length_flatMap]
  apply ordered_sum_le N state false (fun v => cell v = c) is (sites_nodup _ _ _) (fun v hv =>
    (ho v).symm.trans (site_owner siteID owner hv)) (fun v => (rows v).length) 2
  intro v _
  let one := localRecords N false (fun v => (state v).staticNodes) (fun v => (state v).expandedLoad) (fun u => u = v)
  have h1 : (state v).rows.length ≤ one := by
    apply le_trans ?_ (site_load_le N state v).1
    unfold Site.staticNodes Directory.recordNodes
    omega
  have h2 := tieRows_le N false (fun v => (state v).staticNodes) (fun v => (state v).expandedLoad) (fun _ => True) v
  let equiv : Incident N v ≃ {z : N.Edge // True ∧ (N.src z = v ∨ N.dst z = v)} :=
    Equiv.subtypeEquivRight fun _ => ⟨fun h => ⟨trivial,h⟩,And.right⟩
  have cardEq : Fintype.card (Incident N v) + Fintype.card (Attached N v) = tieRows N (fun _ => True) v := by
    unfold tieRows
    apply congrArg₂ (· + ·) _ rfl
    convert! Fintype.card_congr equiv using 1
    congr! 2
  have ht : (binding N cell siteID edgeID portID state v).length ≤ one := by
    rw [binding,Placement.length_ties,cardEq]
    exact h2
  simp only [rows,List.length_append,Site.placedRows,List.length_map,two_mul]
  exact Nat.add_le_add h1 ht

/-- Report serialization contains exactly one fixed-width word per gadget. -/
theorem countFields_digits (base gadgets w : ℕ) :
    ((countFields base gadgets w).map List.length).sum = gadgets*w := by
  simp [countFields,List.map_ofFn,Function.comp_def]

/-- The actual compiler directory has its public, one-copy table, traversal
and list-length bounds at the paper's private-cell scales. -/
theorem compiler_static (c base gadgets digits M E : ℕ) (ho : ∀ v, owner (siteID v) = cell v)
    (schema : ∀ v, (state v).Schema) (hpub : load N cell state c false ≤ M) (hexp : load N cell state c true ≤ M)
    (hg : gadgets ≤ M+1) (hw : digits ≤ M+1) :
    let dir := directory owner N cell siteID edgeID portID state c (countFields base gadgets digits)
    dir.StaticBounds 1026 M ∧ Packet.storedMass dir ≤ 1026*(M+1)^2 ∧
      dir.records.length ≤ 4*(M+E+1)^3 ∧ dir.reportedCounts.length ≤ 4*(M+E+1)^3 ∧ dir.visitCount ≤ M := by
  intro dir
  obtain ⟨rec,box,store,visit⟩ := directory_load owner N cell siteID edgeID portID state c _ ho schema
  have len := record_count_le N cell siteID edgeID portID owner state c (countFields base gadgets digits) ho
  have square : M+1 ≤ (M+1)^2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right (M+1) (Nat.succ_pos M)
  have hs : M ≤ 1026*(M+1)^2 := (Nat.le_succ M).trans (square.trans (Nat.le_mul_of_pos_left _ (by decide)))
  have hc : M+1 ≤ (M+E+1)^3 :=
    (show M+1 ≤ M+E+1 by omega).trans (Nat.le_self_pow (by decide) (M+E+1))
  have hreport : dir.reportedCounts.length = gadgets := countFields_length _ _ _
  have hdigits : dir.reportWidth = gadgets*digits := countFields_digits _ _ _
  refine ⟨⟨?_,?_,?_,?_⟩,store.trans (hpub.trans hs),?_,?_,visit.trans hexp⟩
  · have h := Nat.mul_le_mul_left 1026 hpub
    have t := Nat.mul_le_mul_left 1026 square
    change dir.recordMass ≤ 1026*load N cell state c false+1 at rec
    omega
  · exact box.trans ((Nat.add_le_add_right hpub _).trans (Nat.le_mul_of_pos_left _ (by decide)))
  · rw [hdigits]
    exact (Nat.mul_le_mul hg hw).trans (by rw [pow_two]; exact Nat.le_mul_of_pos_left _ (by decide))
  · exact hreport.le.trans (hg.trans (Nat.le_mul_of_pos_left _ (by decide)))
  · exact len.trans ((Nat.mul_le_mul_left 2 hpub).trans (Nat.mul_le_mul (by decide) ((Nat.le_succ M).trans hc)))
  · exact hreport.le.trans (hg.trans (hc.trans (Nat.le_mul_of_pos_left _ (by decide))))

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
