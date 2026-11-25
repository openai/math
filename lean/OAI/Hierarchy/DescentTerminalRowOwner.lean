import OAI.Hierarchy.DescentTerminalRowAllocation
import OAI.Hierarchy.DescentTerminalSpanRead

namespace OAI
/-! # Read fixed paid row ownership and offsets from native allocation on all real rows -/
namespace Hierarchy.DescentTerminalRowPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalRecipeRows DescentTerminalBinPack
open DescentTerminalSpanBook DescentTerminalHeaderScatter
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w S n q W src : ℕ}

theorem mark_early (L : MarkerBanks) (m : Memory w) (f : L.Room w src n S) {j:ℕ} (lo:j<L.mark.base) :
    L.result src S n m j=m j := by
  let cleared:=L.clear n m
  have endAt:=f.endAt
  have low : j<src:=by have:=f.mark.2.2;omega
  have read : cleared j=m j:=by simp [cleared,MarkerBanks.clear,image,fillSegment,not_le.mpr lo]
  apply published
  · intro i hit
    change ((bounded L.mark L.startExpr).eval cleared ((field i 0).val : Word w)).val=j at hit
    rw [bounded_val L.mark L.startExpr cleared _ f.mark (by omega)] at hit
    omega
  · left;simpa [image,fillSegment,not_le.mpr low] using read

theorem locate_early (L : Cursors) (m : Memory w) (f:L.Fits w n) {j:ℕ} (low:j<L.number.base) :
    L.final n m j=m j := by
  have f1:=f.number.2.2;have f2:=f.active.2.2;have f3:=f.owner.2.2
  simp [Cursors.final,Cursors.located,Cursors.activated,Cursors.state,DescentTerminalHeaderPrefixRAM.result,
    image,fillSegment,not_le.mpr low,
    not_le.mpr (show j<L.active.base by omega),not_le.mpr (show j<L.owner.base by omega),
    not_le.mpr (show j<L.localRow.base by omega)]

structure Linked (L : Layout) (S : ℕ) : Prop where
  marker : L.mark.mark=L.locate.marker
  first : L.mark.first=L.siteFirst
  locateFirst : L.locate.first=L.siteFirst
  locateLast : L.locate.last=L.siteLast
  firstSize : S≤L.siteFirst.size
  lastSize : S≤L.siteLast.size
  lastLow : L.siteLast.Fits w L.mark.mark.base

theorem owner (L : Layout) (sites : Fin S→Site) (m : Memory w) (room : Room L S n w) (links : Linked (w:=w) L S)
    (fit : ∀i,(sites i).rows q≤W) (positive:0<w) (wpos:0<W) (paid : purchased W (counts (q:=q) sites)≤n)
    (siteRoom:S<2^w) (atEnd:n<2^w) (localRoom:n≤L.locate.localRow.size)
    (half : ∀i:Fin S,L.mark.half.read (header L S m) ((field i 0).val:Word w)=(i.val:Word w))
    (starts : ∀i:Fin S,header L S m (L.siteFirst.base+i.val)=(first W (counts (q:=q) sites) i:Word w))
    (ends : ∀i:Fin S,header L S m (L.siteLast.base+i.val)=(last W (counts (q:=q) sites) i:Word w))
    (r:Fin n) : Cursors.Facts (q:=q) L.locate sites r fit (result L S n m) := by
  let C:=counts (q:=q) sites
  have stops (i:Fin S) : first W C i+C i≤n:=by
    rw [←cursor_step]
    exact ((cursor_mono W C (show i.val+1≤S from i.isLt)).trans (end_le_purchased wpos C)).trans paid
  have passFirst (i : Fin S) : first W C i < n := by
    have stop := stops i
    have hz : 0 < C i := by simp [C,Site.rows]
    omega
  have lowFirst:L.siteFirst.Fits w L.mark.mark.base:=links.first ▸ room.marker.first
  have get (b:Bank) (safe:b.Fits w L.mark.mark.base) (size:S≤b.size) (i:Fin S) :
      b.read (marked L S n m) (i.val:Word w)=header L S m (b.base+i.val) := by
    have valid:=i.isLt.trans_le size
    rw [Bank.read,Fin.val_cast_of_lt (i.isLt.trans siteRoom),Nat.mod_eq_of_lt valid]
    apply mark_early _ _ room.marker
    have:=safe.2.2;omega
  have begin (i:Fin S) : L.mark.first.read (header L S m) (i.val:Word w)=(first W C i:Word w):=by
    rw [links.first,Bank.read,Fin.val_cast_of_lt (i.isLt.trans siteRoom),Nat.mod_eq_of_lt (i.isLt.trans_le links.firstSize)]
    exact starts i
  apply Cursors.read L.locate (marked L S n m) room.locate sites fit r siteRoom localRoom positive
  · intro z
    have valid:=z.isLt.trans_le room.marker.endMark
    rw [←links.marker,Bank.read,Fin.val_cast_of_lt (z.isLt.trans atEnd),Nat.mod_eq_of_lt valid]
    exact L.mark.truth L.markedScratch n sites (header L S m) room.marker passFirst begin half z
  · intro i;rw [links.locateFirst,get _ lowFirst links.firstSize];exact starts i
  · intro i;rw [links.locateLast,get _ links.lastLow links.lastSize];exact ends i
  · intro i;have:=stops i;change first W C i+C i-1<2^w;omega

end
end Hierarchy.DescentTerminalRowPlan

end OAI
