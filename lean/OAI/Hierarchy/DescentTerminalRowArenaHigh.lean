import OAI.Hierarchy.DescentTerminalRowArena

namespace OAI
/-! # The complete terminal row allocator preserves the words beyond its workspace -/

namespace Hierarchy.DescentTerminalRowArena.Arena
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalRowPlan DescentTerminalSpanBook
open DescentTerminalHeaderScatter ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable (A : Arena) {w : ℕ}

private theorem ends_before {i n x : ℕ} (slot : i < 22) (count : n ≤ A.stride) (tail : A.finish ≤ x) :
    A.atBand i+n ≤ x :=
  ((Nat.add_le_add_left count _).trans (A.band_after slot)).trans tail

theorem header_after (m : Memory w) {x : ℕ} (tail : A.finish ≤ x) :
    DescentTerminalRowPlan.header A.row A.sites m x=m x := by
  have cap := A.stride_min
  have old (i : ℕ) (hi : i < 22) : ¬x < A.atBand i+A.sites :=
    not_lt_of_ge (A.ends_before hi (by omega) tail)
  simp only [DescentTerminalRowPlan.header,DescentTerminalRowPlan.allocated,DescentTerminalRowPlan.sized,
    DescentTerminalRowPlan.printed,DescentTerminalBinPackCheap.headerImage,DescentTerminalUniversalWrite.image,
    ProtocolRAM.image,fillSegment,row,bank,old 2 (by decide),old 3 (by decide),old 4 (by decide),
    old 5 (by decide),old 6 (by decide),and_false,ite_false]

private theorem mark_after (m : Memory w) (fit : A.finish < 2^w) {x : ℕ} (tail : A.finish ≤ x) :
    A.row.mark.result A.row.markedScratch A.sites A.rows m x=m x := by
  let L := A.row.mark
  let empty := L.clear A.rows m
  have cap := A.stride_min
  have aperture := A.fits_band fit (by decide : 7 < 8) (by decide)
  have top : A.atBand 8 < 2^w := (A.band_mono (by decide : 8 ≤ 22)).trans_lt fit
  have scratch : ¬x < A.atBand 8+2*A.sites := not_lt_of_ge (A.ends_before (by decide) (by omega) tail)
  have marker : ¬x < A.atBand 7+A.rows := not_lt_of_ge (A.ends_before (by decide) (by omega) tail)
  have address : A.atBand 7+A.stride ≤ x := (A.band_after (by decide : 7 < 22)).trans tail
  have cleared : empty x=m x := by
    simp only [empty,L,MarkerBanks.clear,row,bank,image,fillSegment,marker,and_false,ite_false]
  apply published
  · intro i hit
    change ((bounded (A.bank 7) L.startExpr).eval empty _).val=x at hit
    rw [bounded_val _ _ _ _ aperture top] at hit
    have small := Nat.mod_lt
      ((L.startExpr.eval empty ((field i 0).val : Word w)-(L.mark.base : Word w)).val) aperture.1
    change A.atBand 7+((L.startExpr.eval empty ((field i 0).val : Word w)-
      (L.mark.base : Word w)).val%A.stride)=x at hit
    rw [A.bank_size 7] at small
    omega
  · left
    change image (A.atBand 8) (2*A.sites) _ empty x=m x
    simpa only [ProtocolRAM.image,fillSegment,scratch,and_false,ite_false] using cleared

theorem plan_after (m : Memory w) (fit : A.finish < 2^w) {x : ℕ} (tail : A.finish ≤ x) :
    DescentTerminalRowPlan.result A.row A.sites A.rows m x=m x := by
  have cap := A.stride_min
  have old (i : ℕ) (hi : i < 22) : ¬x < A.atBand i+A.rows :=
    not_lt_of_ge (A.ends_before hi (by omega) tail)
  have kept := (A.mark_after (DescentTerminalRowPlan.header A.row A.sites m) fit tail).trans
    (A.header_after m tail)
  change A.row.locate.final A.rows (DescentTerminalRowPlan.marked A.row A.sites A.rows m) x=m x
  simpa only [Cursors.final,Cursors.located,Cursors.activated,Cursors.state,
    DescentTerminalHeaderPrefixRAM.result,DescentTerminalRowPlan.marked,ProtocolRAM.image,fillSegment,
    row,bank,old 9 (by decide),old 10 (by decide),old 11 (by decide),old 12 (by decide),
    and_false,ite_false] using kept

end
end Hierarchy.DescentTerminalRowArena.Arena

end OAI
