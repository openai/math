import OAI.Hierarchy.ProtocolRAMCalendarPriced
import OAI.Hierarchy.ProtocolRAMPrefixAgreement

namespace OAI
/-! # The complete signed priced stock commit only reads its mounted prefix -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open PrefixAgreement
variable {w q d n cut : ℕ}

private theorem atRow_bound (e index : Expr) : e.inputEnd≤(e.atRow index).inputEnd := by
  induction e with
  | row => exact Nat.zero_le _
  | lit => rfl
  | lookup b i ih => exact max_le_max (le_refl _) ih
  | op _ _ _ lu lv => exact max_le_max lu lv
  | branch _ _ _ _ _ lu lv la lb => exact max_le_max (max_le_max lu lv) (max_le_max la lb)

private theorem operands (p : RepairHistogram.Columns) (h : (RepairHistogram.pair p).inputEnd≤cut) :
    p.destination.inputEnd≤cut ∧ p.credit.inputEnd≤cut ∧ p.charge.inputEnd≤cut := by
  let i:=Expr.lookup p.occurrence .row
  have terms : max (p.destination.atRow i).inputEnd (max (p.credit.atRow i).inputEnd (p.charge.atRow i).inputEnd)≤cut :=
    (max_le_iff.mp h).2
  obtain ⟨dst,cs⟩:=max_le_iff.mp terms
  obtain ⟨cr,ch⟩:=max_le_iff.mp cs
  exact ⟨(atRow_bound _ _).trans dst,(atRow_bound _ _).trans cr,(atRow_bound _ _).trans ch⟩

theorem sparse_low (p : RepairHistogram.Columns) (src : ℕ) (left right : Memory w)
    (pair : (RepairHistogram.pair p).inputEnd≤ cut) (addr : p.destination.inputEnd≤ cut)
    (credit : p.credit.inputEnd≤ cut) (charge : p.charge.inputEnd≤ cut) (σ : Low cut left right) :
    Low cut (RepairHistogram.result p src n left) (RepairHistogram.result p src n right) := by
  have key : RepairHistogram.address (n:=n) p left=RepairHistogram.address p right := by
    funext i
    exact congrArg Fin.val (expr _ _ _ _ addr σ _)
  have increment : RepairHistogram.delta (n:=n) p left=RepairHistogram.delta p right := by
    funext i
    unfold RepairHistogram.delta
    rw [expr _ _ _ _ credit σ,expr _ _ _ _ charge σ]
  have pre:=pass (w:=w) ⟨src,2*n,RepairHistogram.pair p⟩ left right cut pair σ
  intro x hx
  have same := pre x hx
  change image src (2*n) (RepairHistogram.pair p) left x =
    image src (2*n) (RepairHistogram.pair p) right x at same
  simp only [RepairHistogram.result,ProtocolRAMWeightedScatter.image,key,increment,same]

/-- Any differences at or above cut are irrelevant even in intermediate
scratch cells. The sparse destination and signed deltas are real input reads. -/
theorem pricedSegment_low (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d) (left right : Memory w)
    (label : (g.pass a.occurrences).term.inputEnd≤ cut) (all : a.stop≤ cut)
    (ready : (pricedSegment a s g w b).ready left) (σ : Low cut left right) :
    Low cut ((pricedSegment a s g w b).after left) ((pricedSegment a s g w b).after right) := by
  obtain ⟨goods,seed,fees,flags,tape,cap,capOut,last⟩:=a.order
  obtain ⟨_,seedFits,charges,mount,_⟩:=ready
  have start:a.start≤ cut:=by omega
  have first:=pass (g.pass a.occurrences) left right cut label σ
  have seedRead:=inputEnd_of_fits _ seedFits.1
  have second:=pass (a.seed s) _ _ cut (seedRead.trans start) first
  let st:=fresh a s
  have cashLow : ∀u∈st.charges b a.rows,u.term.inputEnd≤ cut := by
    intro u hu
    have fits:=inputEnd_of_fits _ (charges u hu).1
    unfold StockCommit.charges RepairHistogram.directColumns at hu
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with (rfl|rfl)|rfl <;> apply fits.trans <;> change _≤ cut <;> dsimp only [st,fresh] <;> omega
  have cash:=passes (st.charges b a.rows) _ _ cut cashLow second
  have pairRead : (RepairHistogram.pair (a.columns s)).inputEnd≤cut:=
    (inputEnd_of_fits _ mount.pairFits).trans (by change a.src≤cut;omega)
  obtain ⟨addr,credit,charge⟩:=operands _ pairRead
  have delta:=sparse_low (n:=a.occurrences) (a.columns s) a.src _ _ pairRead addr credit charge cash
  let total:=Expr.lookup a.bank .row
  have read : total.inputEnd≤ cut := mount.clipFits.trans (by change a.clip≤ cut;omega)
  have capFits : ∀u∈StockAccounts.columns a.clip a.goods a.limit total,u.term.inputEnd≤ cut := by
    intro u hu
    simp only [StockAccounts.columns,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl <;> simp [StockAccounts.clipped,StockAccounts.overflow,Expr.inputEnd,read]
  have conserved:=passes (StockAccounts.columns a.clip a.goods a.limit total) _ _ cut capFits delta
  apply passes _ _ _ cut _ conserved
  intro u hu
  exact (inputEnd_of_fits _ (mount.inputs u hu)).trans (by change a.output≤ cut;omega)

end Hierarchy.ProtocolRAM.Calendar.StockCommit

namespace Hierarchy.ProtocolRAM.Calendar
open ProbeStage ProbeStage.Native PurchaseStage
open Computability.VPVNP.BurstRAM
variable {z d k q goods r edges cut : ℕ}

theorem Format.pricedCommit_low (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ)
    (role : Expr) (ids : Fin goods→Expr) (b : Batch q goods) (left right : Memory (wordBits z d copies))
    (labels : ((p.labelSource sink idBase role ids).pass p.occurrences).term.inputEnd≤ cut)
    (all : p.pricedArea.stop≤ cut) (ready : (p.pricedCommit sink idBase role ids b).ready left)
    (σ : PrefixAgreement.Low cut left right) :
    PrefixAgreement.Low cut ((p.pricedCommit sink idBase role ids b).after left)
      ((p.pricedCommit sink idBase role ids b).after right) :=
  StockCommit.pricedSegment_low _ _ _ _ _ _ labels all ready σ

theorem Format.pricedCommit_agree (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ)
    (role : Expr) (ids : Fin goods→Expr) (b : Batch q goods) (left right : Memory (wordBits z d copies))
    (all : p.pricedArea.stop≤ cut)
    (ready : (p.pricedCommit sink idBase role ids b).ready left) (σ : PrefixAgreement.Low cut left right) :
    PrefixAgreement.Low cut ((p.pricedCommit sink idBase role ids b).after left)
      ((p.pricedCommit sink idBase role ids b).after right) := by
  apply p.pricedCommit_low sink idBase role ids b left right _ all ready σ
  have low:=PrefixAgreement.inputEnd_of_fits _ ready.1.1
  apply low.trans
  change p.labelStart≤ cut
  let a:=p.pricedArea
  obtain ⟨_,sd,fees,flags,tape,cap,capOut,last⟩:=a.order
  have beginAt:a.start=p.labelStart+p.occurrences:=rfl
  change a.stop≤ cut at all
  omega

end Hierarchy.ProtocolRAM.Calendar

end OAI
