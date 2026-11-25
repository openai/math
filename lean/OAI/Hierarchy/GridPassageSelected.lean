import OAI.Hierarchy.GridThroughSelect
import OAI.Hierarchy.GridPassageVariableScan

namespace OAI
/-! # The corrected native mark is the selected-passage predicate of the actual wiring -/

namespace Hierarchy.GridThrough.Program
open GridLens
open GridPassageRAMRow (rankIn AddressMap DecodeReads cursor)
open scoped Classical Fin.CommRing

variable {k n p E w B : ℕ} {width : Fin k → ℕ}

/-- The legal reserved wires themselves exhibit enough untouched rails in every cell. -/
theorem untouched_capacity (P : GridThrough.Program (Fin E) n p width) (x : GridThrough.Cell k n) (j : Fin k) :
    width j ≤ (untouchedRails P.direction P.row P.touch x j).card := by
  let f (i : Fin (width j)) : (untouchedRails P.direction P.row P.touch x j) :=
    ⟨P.pass x ⟨j,i⟩, by
      apply Finset.mem_filter.mpr
      have axis := P.pass_dir x ⟨j,i⟩
      refine ⟨Finset.mem_univ _, axis, ?_, ?_⟩
      · simpa only [axis] using P.pass_line x ⟨j,i⟩
      · simpa only [axis] using P.pass_untouched x ⟨j,i⟩⟩
  have inj : Function.Injective f := by
    intro i i' h
    have h' : (Sigma.mk j i : Catalyst.Wire width) = ⟨j,i'⟩ :=
      P.pass_injective x (congrArg Subtype.val h)
    simpa using h'
  simpa using Fintype.card_le_of_injective f inj

/-- The scheduled and idle constructors both install `firstPassage` by reflexivity. -/
theorem selected_iff_rank (P : GridThrough.Program (Fin E) n p width)
    (cap : ∀ x j, width j ≤ (untouchedRails P.direction P.row P.touch x j).card)
    (installed : P.pass = firstPassage P.direction P.row P.touch width cap) (e : Fin E) (t : Fin (n+1)) :
    P.Selected e t ↔ P.touch e ≠ some t ∧
      rankIn P.direction P.row P.touch (P.railCell e t) (P.direction e) e < width (P.direction e) := by
  let x := P.railCell e t
  have time : x (P.direction e) = t := by simp [x,railCell]
  constructor
  · rintro ⟨⟨j,r⟩,chosen⟩
    change P.pass x ⟨j,r⟩ = e at chosen
    have dir : P.direction e = j := chosen ▸ P.pass_dir x ⟨j,r⟩
    subst j
    rw [installed] at chosen
    let s := untouchedRails P.direction P.row P.touch x (P.direction e)
    have member : firstPassage P.direction P.row P.touch width cap x ⟨P.direction e,r⟩ ∈ s :=
      s.orderEmbOfCardLe_mem (cap x (P.direction e)) r
    rw [chosen] at member
    have pass := (Finset.mem_filter.mp member).2.2.2
    have rank : rankIn P.direction P.row P.touch x (P.direction e) e = r.val := by
      exact (GridPassageRank.orderEmbOfCardLe_eq_iff_rank s (cap x (P.direction e)) r member).mp chosen
    exact ⟨by simpa only [time] using pass,rank.trans_lt r.isLt⟩
  · rintro ⟨pass,small⟩
    let s := untouchedRails P.direction P.row P.touch x (P.direction e)
    have member : e ∈ s := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,rfl,by rw [time]; rfl,by simpa only [time] using pass⟩
    let r : Fin (width (P.direction e)) := ⟨rankIn P.direction P.row P.touch x (P.direction e) e,small⟩
    refine ⟨⟨P.direction e,r⟩,?_⟩
    rw [installed]
    exact (GridPassageRank.orderEmbOfCardLe_eq_iff_rank s (cap x (P.direction e)) r member).mpr rfl

theorem corrected_mark_eq_selected (P : GridThrough.Program (Fin E) n p width)
    (cap : ∀ x j, width j ≤ (untouchedRails P.direction P.row P.touch x j).card)
    (installed : P.pass = firstPassage P.direction P.row P.touch width cap)
    (a : AddressMap) (fits : a.Fits w k n E B) (input : Computability.VPVNP.BurstRAM.Memory w)
    (loaded : ∀ e : Fin E, DecodeReads input a.dir a.cell a.powers a.touch e.val (P.direction e) (P.row e) (P.touch e))
    (pad : ∀ j, width j ≤ B) (e : Fin E) (t : Fin (n+1)) :
    GridPassageRAMMask.finalMemory P.direction P.row P.touch width a B input (a.out.mark+cursor e.val t) =
      if P.Selected e t then 1 else 0 := by
  rw [GridPassageRAMMask.final_mark P.direction P.row P.touch width a B fits input loaded pad e t]
  by_cases yes : P.Selected e t
  · rw [ite_eq_left yes]
    split
    · rfl
    · rename_i absent
      exact False.elim (absent (by simpa only [railCell] using (P.selected_iff_rank cap installed e t).mp yes))
  · rw [ite_eq_right yes]
    split
    · rename_i present
      exact False.elim (yes ((P.selected_iff_rank cap installed e t).mpr (by simpa only [railCell] using present)))
    · rfl

end Hierarchy.GridThrough.Program

end OAI
