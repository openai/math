import OAI.Hierarchy.ProtocolRAMCalendarHalfROM
import OAI.Hierarchy.ProtocolRAMCalendarPurchaseStock

namespace OAI
/-! # The integral half read on the native label-and-seed purchase commit -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing
variable {w q d : ℕ}

/-- Memory immediately before the installed commit transfers the active, reserve and
spill arrays. All labels, fresh stock, histogram debits and clip columns already ran. -/
def pricedTransfer (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d) (m : Memory w) :=
  let st := fresh a s
  let u := st.beforeApply b a.rows ((a.seed s).apply ((g.pass a.occurrences).apply m))
  RepairHistogram.beforeTransfer st.columns st.plan a.occurrences a.goods u

theorem pricedTransfer_prior (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d) (m : Memory w)
    (room : a.stop<2^w) (label : g.out≤a.start) (x : ℕ) (prior : x<g.out) :
    pricedTransfer a s g b m x=m x := by
  let stamped := (g.pass a.occurrences).apply m
  let seed := (a.seed s).apply stamped
  let st := fresh a s
  let u := st.beforeApply b a.rows seed
  obtain ⟨pad,first,fees,flags,tape,cap,out,last⟩ := a.order
  have stock : a.start+a.goods<2^w := by omega
  have target (e : Fin a.occurrences) : a.start≤RepairHistogram.address st.columns u e := by
    change a.start≤((RepairHistogram.destination a.start a.goods s.slot).eval u (e.val:Word w)).val
    rw [RepairHistogram.destination_val _ _ _ _ _ stock]
    omega
  exact (RepairHistogram.input_frame (n:=a.occurrences) (goods:=a.goods) st.columns st.plan u x
      (show x<a.src by omega) (show x<a.clip by omega)
      (fun e=>(prior.trans_le (label.trans (target e))).ne')).trans
    ((st.beforeCore (rows:=a.rows) b seed (show a.direct≤a.broadcast by omega) x (show x<a.direct by omega)).trans
      ((a.seed_frame s stamped x (.inl (prior.trans_le label))).trans
        (ProtocolRAMGeneratedWrite.frame_image _ _ _ m x (.inl prior))))

/-- With the histogram disabled in buy mode, the actual native bank value is exactly
the entry stock before the labels and seed, so it is a legitimate half-table index. -/
theorem pricedTransfer_stock (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d) (m : Memory w)
    (i : Fin a.goods) (fit : PrefixFits a s b) (room : a.stop<2^w)
    (oldFits : a.goods ≤ s.old.size) (oldBelow : s.old.base+a.goods≤g.out)
    (idle : let stamped := (g.pass a.occurrences).apply m
      ∀ e : Fin a.occurrences,RepairHistogram.delta (a.columns s) ((a.seed s).apply stamped) e=0) :
    (a.bank.read (pricedTransfer a s g b m) (i.val:Word w)).val=(m (s.old.base+i.val)).val := by
  let stamped := (g.pass a.occurrences).apply m
  let seed := (a.seed s).apply stamped
  let st := fresh a s
  let u := st.beforeApply b a.rows seed
  obtain ⟨pad,first,fees,flags,tape,cap,out,last⟩ := a.order
  have order : st.direct≤ st.broadcast := by change a.direct≤a.broadcast; omega
  have credit : st.columns.credit.Fits w st.direct :=
    s.credit.fits_of_inputEnd (fit.credit.trans (show a.start≤a.direct by omega)) (show a.direct<2^w by omega)
  have debit : st.columns.charge.Fits w st.direct :=
    s.charge.fits_of_inputEnd (fit.charge.trans (show a.start≤a.direct by omega)) (show a.direct<2^w by omega)
  have noDelta (e : Fin a.occurrences) : RepairHistogram.delta st.columns u e=0 :=
    (st.delta_beforeApply b seed order credit debit e).trans (idle e)
  have firstStock := RepairHistogram.stock_read_raw (n:=a.occurrences) st.columns st.plan u i
    (show a.start+a.goods≤a.clip by omega) (show a.goods≤2^w by omega) pad.le
  have nochange := RepairHistogram.raw_idle st.columns st.plan u i noDelta (show a.start+a.goods≤a.src by omega)
  have core := st.beforeCore (rows:=a.rows) b seed order (a.start+i.val) (show a.start+i.val<a.direct by have := i.isLt; omega)
  have source := previous_stock a s stamped i room oldFits
  have stamp : stamped (s.old.base+i.val)=m (s.old.base+i.val) :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by change s.old.base+i.val<g.out; have := i.isLt; omega))
  exact firstStock.trans (nochange.trans ((congrArg Fin.val core).trans (source.trans (congrArg Fin.val stamp))))

theorem priced_half (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d) (m fixture : Memory w)
    (i : Fin a.goods) (fit : PrefixFits a s b) (room : a.stop<2^w)
    (oldFits : a.goods ≤ s.old.size) (oldBelow : s.old.base+a.goods≤g.out)
    (label : g.out≤a.start) (table : s.half.base+s.half.size≤g.out)
    (bounded : (m (s.old.base+i.val)).val < s.half.size)
    (mounted : ∀ x,s.half.base≤x → x < s.half.base+s.half.size → m x=FeedROM.halfAdvice s.half fixture x)
    (idle : let stamped := (g.pass a.occurrences).apply m
      ∀ e : Fin a.occurrences,RepairHistogram.delta (a.columns s) ((a.seed s).apply stamped) e=0) :
    let raw := pricedTransfer a s g b m
    let old := a.bank.read raw (i.val:Word w)
    (s.half.read raw old).val=old.val/2 := by
  have value := pricedTransfer_stock a s g b m i fit room oldFits oldBelow idle
  apply FeedROM.read_frame _ _ fixture _ (value.trans_lt bounded)
  intro x hx endAt
  exact (pricedTransfer_prior a s g b m room label x (endAt.trans_le table)).trans (mounted x hx endAt)

theorem calibrated_buy (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d) (m fixture : Memory w)
    (i : Fin a.goods) (fit : PrefixFits a s b) (room : a.stop<2^w)
    (oldFits : a.goods ≤ s.old.size) (oldBelow : s.old.base+a.goods≤g.out)
    (label : g.out≤a.start) (table : s.half.base+s.half.size≤g.out)
    (bounded : (m (s.old.base+i.val)).val < s.half.size)
    (mounted : ∀ x,s.half.base≤x → x < s.half.base+s.half.size → m x=FeedROM.halfAdvice s.half fixture x)
    (addr : ℕ) (modeWord : s.mode=word addr) (before : addr<g.out) (observed : (m addr).val=3)
    (idle : let stamped := (g.pass a.occurrences).apply m
      ∀ e : Fin a.occurrences,RepairHistogram.delta (a.columns s) ((a.seed s).apply stamped) e=0) :
    BuyInput a s g b m i := by
  refine ⟨idle,?_,priced_half a s g b m fixture i fit room oldFits oldBelow label table bounded mounted idle⟩
  change (s.mode.eval (pricedTransfer a s g b m) (i.val:Word w)).val=3
  rw [modeWord,word_eval,pricedTransfer_prior a s g b m room label addr before]
  exact observed

end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
