import OAI.Computability.BorderVNP.PackedCablePhysical
import OAI.Computability.BorderVNP.PackedDirectoryKeys
import OAI.Computability.BorderVNP.PackedDirectoryBudget
import OAI.Computability.BorderVNP.CubeLabelResources

/-! # Exact traffic volumes of the sparse cable and delivery producers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CableTriples

open Crossing CellAddressCircuit CellAddressPhysical Cube.LabelIndex
open scoped BigOperators Classical

/-- Even the *raw* width sum of all reserved slots counts only physical cables
between distinct final cells. Holes and absorbed rows have actual width word zero. -/
theorem raw_width_sum {D s m n C d k w : ℕ} {P : Type*} {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
    (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ) {x : σ → Bool}
    (h : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val = c.val) :
    (∑ i, (row F x i).width) = ∑ e : N.CrossingEdge cell, N.width e.val := by
  let E := wireOrd N cell edgeID
  symm
  apply Fintype.sum_of_injective E E.injective
  · intro i hi
    rw [row_unused N cell aux siteID edgeID portID F h code i hi]
  · intro e
    rw [row_crossing N cell aux siteID edgeID portID F h code e]
    split <;> simp_all

end Packing.CableTriples

namespace Packing.Directory

open scoped BigOperators

/-- Every nonempty candidate is sourced at an actual team. In the private region
this follows from intersection with the allocated concatenation of processor tails. -/
theorem Layout.populated_team (d : Layout) (pp lp : ℕ → ℕ × ℕ)
    (hp : 0 < d.processors) (hf : 0 < d.fields)
    (fits : d.entries*d.description ≤ d.teams*d.processors*(d.literal/2))
    {r : Row} (mem : r ∈ d.directory pp lp) : r.team < d.teams := by
  obtain ⟨i,hi,rfl,positive⟩ := (d.mem_directory_iff pp lp r).mp mem
  by_cases priv : i < 2*d.entries
  · simp only [Layout.row,ite_eq_left priv] at positive ⊢
    let j := i/2
    let tail := d.literal/2
    let start := j*d.description
    let k := i%2
    let p := slice start d.description tail k
    change 0 < p.2 at positive
    have hit := (mem_slice_iff start d.description tail k p.1).mp
      ⟨le_rfl,Nat.lt_add_of_pos_right positive⟩
    change _ ∧ p.1 < start+d.description ∧ _ ≤ p.1 ∧ _ at hit
    have a : j < d.entries := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
    have h := (Nat.mul_le_mul_right d.description a).trans fits
    have upto : start+d.description ≤ d.teams*d.processors*tail := by
      simpa only [start,tail,Nat.succ_mul] using h
    have mul : (start/tail+k)*tail < (d.teams*d.processors)*tail := hit.2.2.1.trans_lt (hit.2.1.trans_le upto)
    exact (Nat.div_lt_iff_lt_mul hp).mpr (Nat.lt_of_mul_lt_mul_right mul)
  · simp only [Layout.row,ite_eq_right priv,Layout.liveRow]
    let pieces := d.literal/d.block+2
    have pos : 0 < pieces := Nat.zero_lt_succ _
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    apply (Nat.div_lt_iff_lt_mul hf).mpr
    apply (Nat.div_lt_iff_lt_mul pos).mpr
    unfold candidates at hi
    dsimp [pieces]
    omega

private theorem list_get_sum {α : Type*} (xs : List α) (f : α → ℕ) :
    (xs.map f).sum = ∑ i, f (xs.get i) := by
  conv_lhs => rw [← List.ofFn_get xs,List.map_ofFn,List.sum_ofFn]
  rfl

/-- All delivered widths, summed across both optional fields and every compact
row, are bounded by the manuscript's total source volume. -/
theorem Layout.populated_width (d : Layout) (pp lp : ℕ → ℕ × ℕ)
    (hp : 0 < d.processors) (hf : 0 < d.fields) (hb : 0 < d.block)
    (fits : d.entries*d.description ≤ d.teams*d.processors*(d.literal/2)) :
    ((d.directory pp lp).map Row.width).sum ≤ d.teams*((d.fields+1)*(d.processors*d.literal)) := by
  let rows := d.directory pp lp
  have splitRow (i : Fin rows.length) :
      (∑ t : Fin d.teams, if (rows.get i).team = t.val then (rows.get i).width else 0) = (rows.get i).width := by
    let t : Fin d.teams := ⟨(rows.get i).team,d.populated_team pp lp hp hf fits (List.get_mem ..)⟩
    change (∑ u : Fin d.teams, if t.val = u.val then (rows.get i).width else 0) = _
    simp only [Fin.val_inj,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have team (t : Fin d.teams) :
      (∑ i : Fin rows.length, if (rows.get i).team = t.val then (rows.get i).width else 0) ≤
        (d.fields+1)*(d.processors*d.literal) := by
    simpa only [list_get_sum] using d.populated_outgoing pp lp t.val hp hf hb
  rw [list_get_sum]
  change (∑ i : Fin rows.length, (rows.get i).width) ≤ _
  calc
    _ = ∑ i : Fin rows.length, ∑ t : Fin d.teams, if (rows.get i).team = t.val then (rows.get i).width else 0 :=
      Finset.sum_congr rfl (fun i _ => (splitRow i).symm)
    _ = _ := Finset.sum_comm
    _ ≤ ∑ _t : Fin d.teams, (d.fields+1)*(d.processors*d.literal) := Finset.sum_le_sum (fun t _ => team t)
    _ = _ := by simp

end Packing.Directory

end BorderVNP
end Computability
end OAI
