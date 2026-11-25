import OAI.Computability.BorderVNP.CubeDirectedIntervalPhysical
import OAI.Computability.BorderVNP.CubeMeanPhysicalTables

/-! # Constructing the ordered physical intervals from the chooser's real cable table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.NativeIntervals

open Physical Crossing MeanChoice

/-- Interval layout sharing the chooser's processed three-word table and alphabet. -/
def chooserLayout (t : LabelIndex.Layout) (frame labels widths ordinals : ℕ) : Layout :=
  ⟨frame,t.cables,t.cableCount,labels,t.labels,widths,ordinals⟩

/-- The product label's actual radix code in the public alphabet. -/
def productCode (n d z : ℕ) (h : d^(n+1) = z) : Label (n+1) d ↪ Fin z :=
  (finFunctionFinEquiv.trans (finCongr h)).toEmbedding

private theorem empty_iff (t : LabelIndex.Cable) : LabelIndex.liveWidth t = 0 ↔ t.src = t.dst ∨ t.width = 0 := by
  by_cases h : t.src = t.dst <;> simp [LabelIndex.liveWidth,h]

/-- Numbering the chooser's occupied cable rows in increasing address order
gives a physical interval directory for the actual mean-chosen labels. The
hypotheses describe the sparse traffic table and the resident chooser output. -/
theorem physicalRows_of_chooser {D n d : ℕ} {P : Type*} {bits : P → ℕ} {C : Type}
    [Fintype C] [DecidableEq C] {A : Type*} [Fintype A]
    (N : Network D P bits) (cell : N.Site → C) (recv : A → C) (dataWidth : A → ℕ)
    (t : LabelIndex.Layout) (before : ℕ → ℕ) (ep : LabelIndex.Endpoints t before)
    (cells : C ≃ Fin t.cells) (edges : N.CrossingEdge cell ↪ Fin t.cableCount)
    (data : A ↪ Fin t.deliveryCount) (hd : 0 < d) (hz : d^(n+1) = t.labels)
    (placement : RowPlacement (networkRows N cell recv dataWidth) (LabelIndex.fromTables t before ep)
      cells (edges.sumMap data)) (frame labels widths ordinals : ℕ)
    (assigned : ∀ c, before (labels+(cells c).val) = (tableCodes t before ep (d^(n+1)-1) (cells c)).val) :
    let l := chooserLayout t frame labels widths ordinals
    let cs := (List.finRange t.cells).map cells.symm
    ∃ (ord : N.CrossingEdge cell ≃ Fin (Fintype.card (N.CrossingEdge cell)))
      (row : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin l.count),
      (∀ e, row (ord e) = edges e) ∧ PhysicalRows N cell l before ord row
        (cells.toEmbedding.trans Fin.valEmbedding) (meanPackedLabel N cell recv dataWidth cs n d hd)
        (productCode n d t.labels hz) := by
  classical
  obtain ⟨ord,row,loc⟩ := exists_ordered_rows edges
  refine ⟨ord,row,loc,?_,?_,?_⟩
  · intro i
    let e := ord.symm i
    have hi : row i = edges e := by simpa only [e,Equiv.apply_symm_apply] using loc e
    have hval : (row i).val = (edges e).val := congrArg Fin.val hi
    let r := LabelIndex.cableAt t before (edges e)
    have equiv := placement.live (.inl e)
    change rowEquivalent (.cable ⟨r.src,_⟩ ⟨r.dst,_⟩ (LabelIndex.liveWidth r))
      (.cable (cells (crossSrc N cell e)) (cells (crossDst N cell e)) (crossWidth N cell e)) at equiv
    change (before (t.cables+3*(row i).val) = _ ∧ before (t.cables+3*(row i).val+1) = _ ∧
      before (t.cables+3*(row i).val+2) = _) ∨
      ((before (t.cables+3*(row i).val) = before (t.cables+3*(row i).val+1) ∨
        before (t.cables+3*(row i).val+2) = 0) ∧ _)
    rw [hval,Nat.mul_comm 3]
    change (r.src = (cells (crossSrc N cell e)).val ∧ r.dst = (cells (crossDst N cell e)).val ∧
      r.width = crossWidth N cell e) ∨ ((r.src = r.dst ∨ r.width = 0) ∧ crossWidth N cell e = 0)
    rcases equiv with he | ⟨hr,hw⟩
    · obtain ⟨hs,ht,hw⟩ := Traffic.cable.inj he
      have a := congrArg (fun j : Fin t.cells => j.val) hs
      have b := congrArg (fun j : Fin t.cells => j.val) ht
      have distinct : r.src ≠ r.dst := by
        intro eq
        exact e.property (cells.injective (Fin.ext (a.symm.trans (eq.trans b))))
      exact Or.inl ⟨a,b,by simpa only [LabelIndex.liveWidth,ite_eq_right distinct] using hw⟩
    · exact Or.inr ⟨(empty_iff r).mp hr,hw⟩
  · intro c
    rw [← decoded_tableCodes N cell recv dataWidth t before ep cells placement n d hd c]
    change before (labels+(cells c).val) = (finFunctionFinEquiv (finFunctionFinEquiv.symm _)).val
    rw [Equiv.apply_symm_apply]
    exact assigned c
  · intro r hr
    have hx : Sum.inl r ∉ Set.range (edges.sumMap data) := by
      rintro ⟨e|a,he⟩
      · exact hr ⟨ord e,(loc e).trans (Sum.inl.inj he)⟩
      · cases he
    have hz := placement.unused (.inl r) hx
    change LabelIndex.liveWidth (LabelIndex.cableAt t before r) = 0 at hz
    simpa only [Layout.src,Layout.dst,Layout.width,chooserLayout,LabelIndex.cableAt,Nat.mul_comm 3]
      using (empty_iff _).mp hz

end Cube.NativeIntervals

end BorderVNP
end Computability
end OAI
