import OAI.Hierarchy.ProtocolRAMCalendarBuyMask

namespace OAI
/-! # Stock caps at the output of the priced native attempt -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM PurchaseStage
open ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section
variable {w q d : ℕ}

/-- Public layout of the seed, reserve and half table for a single priced attempt. -/
structure StockWindow (a : Area) (s : Sources) (g : LabelSource) (addr stockCap w : ℕ) : Prop where
  room : a.stop<2^w
  wide : 4≤2^w
  capacity : a.goods≤ s.old.size ∧ a.goods≤ s.reserve.size
  old : s.old.base+a.goods≤g.out
  reserve : s.reserve.base+a.goods≤g.out
  label : g.out≤a.start
  mode : s.mode=word addr
  modeBefore : addr<g.out
  table : s.half.base+s.half.size≤g.out
  budget : a.limit=stockCap
  wordRoom : stockCap<2^w
  halfRoom : stockCap<s.half.size

/-- The repair branch uses the clipped RAM word. Every other mode leaves the
histogram inactive. A buy reads the integral half table and writes its complement
to the saved bank. -/
theorem priced_bounded (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d)
    (m fixture : Memory w) (i : Fin a.goods) (addr cap width : ℕ)
    (window : StockWindow a s g addr (cap*width) w) (prefixFit : PrefixFits a s b)
    (ready : (pricedSegment a s g w b).ready m)
    (half : ∀ x,s.half.base≤x → x<s.half.base+s.half.size → m x=FeedROM.halfAdvice s.half fixture x)
    (inactive : (m addr).val≠2 → ∀ e : Fin a.occurrences,
      RepairHistogram.delta (a.columns s) (stageInput a s g m) e=0)
    (old : (m (s.old.base+i.val)).val≤cap*width)
    (saved : (m (s.reserve.base+i.val)).val≤cap*width) :
    let out := (pricedSegment a s g w b).after m
    (out (a.output+i.val)).val≤cap*width ∧ (out (a.output+a.goods+i.val)).val≤cap*width := by
  let st := fresh a s
  let u := st.beforeApply b a.rows (stageInput a s g m)
  let raw := pricedTransfer a s g b m
  let r : Word w := i.val
  let out := (pricedSegment a s g w b).after m
  change (out (a.output+i.val)).val≤_ ∧ (out (a.output+a.goods+i.val)).val≤_
  obtain ⟨pad,first,fees,flags,tape,clips,output,last⟩ := a.order
  have wordRoom := window.room
  have widthFit : a.goods≤2^w := by omega
  have active : RepairHistogram.CommitReady st.columns st.plan w a.occurrences a.goods u := ready.2.2.2.1
  have mode : (s.mode.eval raw r).val=(m addr).val := by
    rw [window.mode,word_eval]
    exact congrArg Fin.val (pricedTransfer_prior a s g b m window.room window.label addr window.modeBefore)
  have read := RepairHistogram.commit_mode st.columns st.plan u active i window.wide
  change out (a.output+i.val)=(if (s.mode.eval raw r).val=2 then (a.plan s).clip.read raw r
        else if (s.mode.eval raw r).val=3 then s.half.read raw (a.bank.read raw r) else a.bank.read raw r) ∧
    out (a.output+a.goods+i.val)=(if (s.mode.eval raw r).val=3 then
      a.bank.read raw r-s.half.read raw (a.bank.read raw r) else s.reserve.read raw r) ∧ _ at read
  rw [mode] at read
  have prior : (s.reserve.read raw r).val=(m (s.reserve.base+i.val)).val := by
    change (raw (s.reserve.base+(i.val:Word w).val%s.reserve.size)).val=_
    rw [Fin.val_cast_of_lt (i.isLt.trans_le widthFit),Nat.mod_eq_of_lt (i.isLt.trans_le window.capacity.2)]
    exact congrArg Fin.val (pricedTransfer_prior a s g b m window.room window.label _ (by
      have := i.isLt
      have := window.reserve
      omega))
  by_cases repair : (m addr).val=2
  · have clipCap : a.goods≤(a.plan s).clip.size := pad.le
    have excessCap : a.goods≤(a.plan s).excess.size := pad.le
    have bankCap : a.goods≤(a.plan s).bank.size := pad.le
    have kept := (RepairHistogram.commit_repair st.columns st.plan u active i window.wide width cap
      window.budget (by change a.limit<2^w; rw [window.budget]; exact window.wordRoom) rfl clipCap excessCap bankCap
      (mode.trans repair)).1
    change (out (a.output+i.val)).val=min _ (cap*width) at kept
    have rest := read.2.1
    rw [ite_eq_right (by omega : (m addr).val≠3)] at rest
    exact ⟨kept.trans_le (Nat.min_le_right ..),((congrArg Fin.val rest).trans prior).trans_le saved⟩
  · have idle := inactive repair
    by_cases buy : (m addr).val=3
    · have cal := calibrated_buy a s g b m fixture i prefixFit window.room window.capacity.1 window.old
        window.label window.table (old.trans_lt window.halfRoom) half addr window.mode window.modeBefore buy idle
      obtain ⟨keep,release,_⟩ := priced_buy a s g b m i ready prefixFit window.room window.wide
        window.capacity.1 window.old cal.idle cal.bought cal.half
      exact ⟨keep.trans_le ((Nat.div_le_self _ _).trans old),release.trans_le ((Nat.sub_le ..).trans old)⟩
    · have keep := read.1
      have rest := read.2.1
      simp only [ite_eq_right repair,ite_eq_right buy] at keep rest
      have source := pricedTransfer_stock a s g b m i prefixFit window.room window.capacity.1 window.old idle
      exact ⟨((congrArg Fin.val keep).trans source).trans_le old,
        ((congrArg Fin.val rest).trans prior).trans_le saved⟩

/-- At an actual attempt the native mask supplies the zero-delta hypothesis
for idle, advance, and buy. The old and saved hypotheses are on the memory at
entry, before the guard, frozen sampler, postprocessor, or commit ran. -/
theorem post_bounded (C : Chart w q d) (x : Attempt) (entry : Memory w)
    (a : Area) (s : Sources) (g : LabelSource) (fixture : Memory w) (i : Fin a.goods)
    (cap width : ℕ)
    (window : StockWindow a s g (C.modeAt x) (cap*width) w)
    (fit : ready C (.attempt x) entry)
    (installed : C.commit x=pricedSegment a s g w (enabledBatch (C.layout x) (repair C x)))
    (prefixFit : PrefixFits a s (enabledBatch (C.layout x) (repair C x)))
    (space : MaskSpace (C.layout x) (repair C x))
    (board : Board (C.layout x) (repair C x) w)
    (positive : 0<(C.layout x).candidates)
    (padded : (C.layout x).candidates≤(repair C x).repairBits.size)
    (padBefore : (repair C x).repairBits.base+(C.layout x).candidates≤g.out)
    (ports : let B := repair C x
      let L := C.layout x
      let posted := postOutput L B (prepared C x entry)
      PortPlan (fresh a s) (enabledBatch L B) (stageInput a s g posted) L.candidates)
    (oldSafe : protected C (s.old.base+i.val) (.attempt x))
    (reserveSafe : protected C (s.reserve.base+i.val) (.attempt x))
    (halfSafe : ∀u,s.half.base≤u → u<s.half.base+s.half.size → protected C u (.attempt x))
    (half : ∀u,s.half.base≤u → u<s.half.base+s.half.size → entry u=FeedROM.halfAdvice s.half fixture u)
    (old : (entry (s.old.base+i.val)).val≤cap*width)
    (saved : (entry (s.reserve.base+i.val)).val≤cap*width) :
    let out := after C (.attempt x) entry
    (out (a.output+i.val)).val≤cap*width ∧ (out (a.output+a.goods+i.val)).val≤cap*width := by
  let B := repair C x
  let L := C.layout x
  let v := prepared C x entry
  let posted := postOutput L B v
  let b := enabledBatch L B
  have restore (u : ℕ) (safe : protected C u (.attempt x)) : posted u=entry u :=
    postOutput_prior C x entry u fit safe
  obtain ⟨_,_,_,_,_,maskRoom,checks,_,_,_,mounted,_,_⟩ := fit
  have check : AuditReady (audits L B) (postSnapshot L B v) := checks
  have stamp : (posted (C.modeAt x)).val=AttemptGate.actual B.policy (postSnapshot L B v) := by
    let j : Fin L.candidates := ⟨0,positive⟩
    let mode : Pass := ⟨B.modeOut,L.candidates,AttemptGate.mode B.policy⟩
    have read := post_read L B v check board mode
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) j
    have eqn : posted (C.modeAt x)=(AttemptGate.actual B.policy (postSnapshot L B v):Word w) :=
      read.trans (AttemptGate.mode_eval ..)
    exact (congrArg Fin.val eqn).trans
      (Fin.val_cast_of_lt ((AttemptGate.actual_lt ..).trans_le window.wide))
  have idle (off : (posted (C.modeAt x)).val≠2) :
      ∀ e : Fin a.occurrences,RepairHistogram.delta (a.columns s) (stageInput a s g posted) e=0 :=
    buy_idle L B space v a s g window.wide (by change B.repairBits.base+L.candidates<2^w at maskRoom; omega)
      padded check (fun hit=>off (stamp.trans hit)) padBefore window.label ports
  have applied : (pricedSegment a s g w b).ready posted := by
    rw [installed] at mounted
    exact mounted
  have limits := priced_bounded a s g b posted fixture i (C.modeAt x) cap width window prefixFit applied
    (fun u hu hv=>(restore u (halfSafe u hu hv)).trans (half u hu hv)) idle
    (by rw [restore _ oldSafe]; exact old) (by rw [restore _ reserveSafe]; exact saved)
  simpa only [after,installed] using limits


end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
