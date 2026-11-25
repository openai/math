import OAI.Hierarchy.DescentTerminalRowOwner

namespace OAI
/-! # Protected addresses through the entire common-position row publication -/
namespace Hierarchy.DescentTerminalRowPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalLocalPortBook
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {w S n G V M A a:ℕ}

structure Lower (L : Layout) (p:ℕ) : Prop where
  num : p<L.locate.number.base
  flag : p<L.mark.mark.base
  last : p<L.siteLast.base
  first : p<L.siteFirst.base
  allocated : p<L.cursors.base
  sized : p<L.counts.base

theorem after_publishing (L:Layout) (m:Memory w) (ok:Room L S n w) {p:ℕ} (low:Lower L p) :
    result L S n m p=printed L S m p := by
  rw [result,locate_early _ _ ok.locate low.num,marked,mark_early _ _ ok.marker low.flag]
  simp [header,DescentTerminalBinPackCheap.headerImage,allocated,DescentTerminalUniversalWrite.image,sized,
    image,fillSegment,not_le.mpr low.last,not_le.mpr low.first,not_le.mpr low.allocated,not_le.mpr low.sized]

theorem before_publishing (L:Layout) (m:Memory w) (ok:Room L S n w) {p:ℕ} (low:Lower L p)
    (first:p<L.books.base) : result L S n m p=m p := by
  rw [after_publishing L m ok low,printed,DescentTerminalChipRuntime.image_low _ _ _ _ first]

theorem site_head (L:Layout) (m:Memory w) (ok:Room L S n w)
    (book : Fin S→Book G V M A a) (parts:Book.Issued L.parts book m)
    (i:Fin S) (low:Lower L (L.books.base+i.val)) :
    result L S n m (L.books.base+i.val)=((book i).bytes.val:Word w) := by
  rw [after_publishing L m ok low]
  exact (Book.publish L.parts m L.books.base ok.book ok.bookEnd book parts).2.2 i

theorem after_header (L:Layout) (m:Memory w) (ok:Room L S n w) {p:ℕ}
    (mark:p<L.mark.mark.base) (sum:p<L.locate.number.base) : result L S n m p=header L S m p := by
  rw [result,locate_early _ _ ok.locate sum,marked,mark_early _ _ ok.marker mark]

end
end Hierarchy.DescentTerminalRowPlan

end OAI
