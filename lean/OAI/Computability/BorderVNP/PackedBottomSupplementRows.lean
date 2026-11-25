import OAI.Computability.BorderVNP.PackedBottomSupplementGeometry
import OAI.Computability.BorderVNP.PackedBankInheritedSiteCharges

/-! # Charging the actual supplemental list to distinct retained birth boxes

Every marked source in the final cell's stable list was an immutable one-copy
factor in an original birth site. Its equality costs one sparse row, regardless
of multiplicity. A second contribution of one row per original description
pins its unused suffix. Both fit in the actual public record load of the cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open Crossing Shortening CellSparse Inherited
open scoped Classical

private theorem factor_pos (f : Factor) : 0 < (Packet.factor f).length := by
  cases f <;> simp [Packet.factor]

private theorem payload_length (fs : List Factor) : fs.length ≤ (fs.flatMap Packet.factor).length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    have hh := factor_pos f
    omega

/-- Retention changes neither the ordering nor the bytes of any immutable private
one-copy table. -/
theorem retention_boxes {a s : Site} (p : a.Retention s) : s.boxes = a.boxes := by
  induction p with
  | refl => rfl
  | layer prev cuts read cover ih => exact ih
  | forced prev read ih => exact ih

/-- One body containing the staged factors pays for all of its weighted source
rows and its private suffix record. -/
theorem source_count_le_static {s : Site} (body original : List Factor)
    (one : s.boxes = [body]) (stored : original.length ≤ body.length) :
    count original+1 ≤ s.staticNodes := by
  have hc := BottomGridBank.count_le_length original
  have hp := payload_length body
  have hh : body.length+1 ≤ (Packet.fieldList (Packet.fieldList Packet.factor) s.boxes).length := by
    rw [one]
    simp [Packet.fieldList] at *
    omega
  unfold Site.staticNodes
  omega

variable {D : ℕ} {P J : Type} [Fintype P] [Fintype J] {bits : P → ℕ}
variable (N : Network D P bits) (cell : N.Site → ℕ) (program : N.Site → Site)
variable (host : J ↪ N.Site) (bundle : J → Bundle) (c : ℕ)

omit [Fintype J] in
/-- The actual supplemental row count of any stable owner sublist is bounded by the
installed local history budget. Every participating fine host occurs once. -/
theorem supplemental_rows_le (origins : List J) (nd : origins.Nodup) (owned : ∀ j ∈ origins, cell (host j) = c)
    (source : ∀ j ∈ origins, ∃ (birth : Site) (body : List Factor), Nonempty (birth.Retention (program (host j))) ∧
      birth.boxes = [body] ∧ (bundle j).factors.length ≤ body.length) :
    ((origins.map bundle).map (fun b => count b.factors)).sum + (origins.map bundle).length ≤
      localRecords N false (fun v => (program v).staticNodes) (fun v => (program v).expandedLoad)
        (fun v => cell v = c) := by
  let f := fun j => count (bundle j).factors+1
  have countRows : ((origins.map bundle).map (fun b => count b.factors)).sum + (origins.map bundle).length =
      (origins.map f).sum := by
    have eq (xs : List J) : ((xs.map bundle).map (fun b => count b.factors)).sum + (xs.map bundle).length =
        (xs.map f).sum := by
      induction xs with
      | nil => rfl
      | cons j js ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons] at *
        dsimp only [f] at *
        omega
    exact eq origins
  rw [countRows,← List.sum_toFinset f nd]
  let weight := fun v => if cell v = c then boxCost false (program v).staticNodes (program v).expandedLoad else 0
  have each (j) (hj : j ∈ origins.toFinset) : f j ≤ weight (host j) := by
    have hm := List.mem_toFinset.mp hj
    obtain ⟨birth,body,⟨r⟩,hb,hs⟩ := source j hm
    have h := source_count_le_static body (bundle j).factors ((retention_boxes r).trans hb) hs
    simp only [weight,owned j hm,ite_true,boxCost,recordCost,Bool.false_eq_true,ite_false,Nat.add_zero]
    exact h.trans (Nat.le_add_right _ _)
  have sub := Finset.sum_le_sum each
  rw [← Finset.sum_map origins.toFinset host weight] at sub
  have full := sub.trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
  apply full.trans
  unfold localRecords
  have first : (∑ v, weight v) = testedWidth (fun v => boxCost false (program v).staticNodes (program v).expandedLoad)
      (fun v => cell v = c) := by
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : cell v = c <;> simp [weight,h]
  rw [first]
  exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))

omit [Fintype P] in
/-- The sparse use bits of the actual sorted cell list, with no density
requirement on that sublist, fit inside its local expanded site storage. -/
theorem supplemental_uses_le {s : ℕ} (siteID : N.Site ↪ Fin s)
    (operands : RetainedOperands N cell program siteID host bundle)
    (cap : ∀ j, count (bundle j).factors ≤ (bundle j).header.cap)
    (stride : ∀ j, (bundle j).header.stride = bottomStride (bundle j).header.orig (bundle j).header.cap)
    (origins : List J) (nd : origins.Nodup) (owned : ∀ j ∈ origins, cell (host j) = c) :
    ((origins.map bundle).map Bundle.useBits).sum ≤ CellAddresses.siteSize N cell c (fun v => (program v).size) := by
  let f := fun j => (bundle j).useBits
  have h := owned_report_le N cell program siteID host bundle operands c cap stride
  simp only [List.map_map]
  change (origins.map f).sum ≤ _
  rw [← List.sum_toFinset f nd]
  let p := fun j => cell (host j) = c
  have member : ∀ j ∈ origins.toFinset, p j := fun j h => owned j (List.mem_toFinset.mp h)
  rw [← Finset.sum_subtype_of_mem f member]
  exact (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans (h.1.trans h.2)

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
