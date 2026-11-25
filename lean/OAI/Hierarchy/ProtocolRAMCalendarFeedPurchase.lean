import OAI.Hierarchy.ProtocolRAMCalendarFeedLayout
import OAI.Hierarchy.ProtocolRAMCalendarArchive

namespace OAI
/-! # The original reserve source, from the native purchase commit -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing
variable {w q d : ℕ}

/-- The installed calendar first copies the previous stock into a fresh bank.
The purchase commit then returns its integral half and archives the complementary reserve. -/
theorem fresh_buy (a : Area) (s : Sources) (b : Batch q d) (m : Memory w) (i : Fin a.goods)
    (mounted : (freshSegment a s w b).ready m) (prefixFit : PrefixFits a s b)
    (room : a.stop<2^w) (wide : 4≤2^w) (oldFits : a.goods ≤ s.old.size)
    (idle : ∀ e : Fin a.occurrences,RepairHistogram.delta (a.columns s) ((a.seed s).apply m) e=0)
    (bought : let st := fresh a s
      let raw := RepairHistogram.beforeTransfer st.columns st.plan a.occurrences a.goods
        (st.beforeApply b a.rows ((a.seed s).apply m))
      (s.mode.eval raw (i.val:Word w)).val=3)
    (half : let st := fresh a s
      let raw := RepairHistogram.beforeTransfer st.columns st.plan a.occurrences a.goods
        (st.beforeApply b a.rows ((a.seed s).apply m))
      let old := a.bank.read raw (i.val:Word w)
      (s.half.read raw old).val=old.val/2) :
    let out := (freshSegment a s w b).after m
    let old := (m (s.old.base+i.val)).val
    (out (a.output+i.val)).val=old/2 ∧
    (out (a.output+a.goods+i.val)).val=old-old/2 ∧ out (a.output+a.goods+a.goods+i.val)=0 := by
  obtain ⟨padding,initial,fees,flags,tape,cap,capOut,final⟩ := a.order
  have small : a.direct<2^w := by omega
  have start : a.start ≤ a.direct := by omega
  have previous := previous_stock a s m i room oldFits
  have read := (fresh a s).buy_receipt (rows:=a.rows) b ((a.seed s).apply m) i mounted.2
    (show a.direct≤a.broadcast by omega)
    (s.credit.fits_of_inputEnd (prefixFit.credit.trans start) small)
    (s.charge.fits_of_inputEnd (prefixFit.charge.trans start) small)
    (show a.start+a.goods≤a.direct by omega) (show a.start+a.goods≤a.src by omega)
    (show a.start+a.goods≤a.clip by omega) wide padding.le idle bought half
  dsimp only at read
  rw [previous] at read
  simpa only [freshSegment, fresh, Area.plan] using read

/-- Replay the label pass as well: all original stock words are below that pass's
output. Its actual input is the entry memory both accounts use. -/
theorem priced_buy (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d) (m : Memory w)
    (i : Fin a.goods) (mounted : (pricedSegment a s g w b).ready m)
    (prefixFit : PrefixFits a s b) (room : a.stop<2^w) (wide : 4≤2^w)
    (oldFits : a.goods ≤ s.old.size) (oldBelow : s.old.base+a.goods≤g.out)
    (idle : let stamped := (g.pass a.occurrences).apply m
      ∀ e : Fin a.occurrences,RepairHistogram.delta (a.columns s) ((a.seed s).apply stamped) e=0)
    (bought : let st := fresh a s
      let stamped := (g.pass a.occurrences).apply m
      let raw := RepairHistogram.beforeTransfer st.columns st.plan a.occurrences a.goods
        (st.beforeApply b a.rows ((a.seed s).apply stamped))
      (s.mode.eval raw (i.val:Word w)).val=3)
    (half : let st := fresh a s
      let stamped := (g.pass a.occurrences).apply m
      let raw := RepairHistogram.beforeTransfer st.columns st.plan a.occurrences a.goods
        (st.beforeApply b a.rows ((a.seed s).apply stamped))
      let old := a.bank.read raw (i.val:Word w)
      (s.half.read raw old).val=old.val/2) :
    let out := (pricedSegment a s g w b).after m
    let old := (m (s.old.base+i.val)).val
    (out (a.output+i.val)).val=old/2 ∧
    (out (a.output+a.goods+i.val)).val=old-old/2 ∧ out (a.output+a.goods+a.goods+i.val)=0 := by
  let stamped := (g.pass a.occurrences).apply m
  have frame : stamped (s.old.base+i.val)=m (s.old.base+i.val) :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl (by have := i.isLt; change s.old.base+i.val<g.out; omega))
  have read := fresh_buy a s b stamped i mounted.2 prefixFit room wide oldFits idle bought half
  dsimp only at read
  rw [frame] at read
  exact read

end Hierarchy.ProtocolRAM.Calendar.StockCommit

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {w q d total : ℕ} {C : Chart w q d} {m : Memory w}

theorem ArchiveRoom.bought_word (archive : ArchiveRoom C m total) {p a : ℕ}
    (hp : p<total) (ha : a<C.mesh.outerFuel) (bought : observedMode C m p a=3) :
    reserveState C m p a 0 (C.modeAt (.outer p a))=3 := by
  apply Fin.ext
  have wide := archive.wide
  exact (archive.outer_word hp ha).trans (bought.trans (Fin.val_cast_of_lt (by omega : 3<2^w)).symm)

end Hierarchy.ProtocolRAM.Calendar

end OAI
