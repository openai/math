import OAI.Hierarchy.ProtocolRAMStockCommitProgram
import OAI.Hierarchy.ProtocolRAMBinarySpan
import OAI.Hierarchy.ProtocolRAMRouteSettlement

namespace OAI
/-! # Reading the signed debit from the physical stock commit -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {w q d rows : ℕ}

def beforeApply (s : StockCommit) (b : Batch q d) (rows : ℕ) (m : Memory w) := result (s.charges b rows) m

theorem beforeCore (s : StockCommit) (b : Batch q d) (m : Memory w) (order : s.direct≤ s.broadcast)
    (x : ℕ) (hx : x<s.direct) : s.beforeApply b rows m x=m x := by
  apply result_below
  intro p hp
  simp only [charges,RepairHistogram.directColumns,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with (rfl | rfl) | rfl <;> simp only <;> omega

theorem inputs_beforeApply (s : StockCommit) (b : Batch q d) (m : Memory w) (order : s.direct≤ s.broadcast)
    (term : Expr) (fits : term.Fits w s.direct) (r : Word w) :
    term.eval (s.beforeApply b rows m) r=term.eval m r :=
  eval_below _ _ _ _ fits (fun x hx => beforeCore s b m order x hx)

theorem read_direct (s : StockCommit) (b : Batch q d) (m : Memory w) (j : Fin s.occurrences)
    (ready : (s.native w rows b).ready m)
    (inputs : (RepairHistogram.ordinaryTerm s.columns s.plan s.goods s.columns.charge).Fits w s.direct)
    (order : s.direct+s.occurrences+s.occurrences≤ s.broadcast)
    (hit : s.plan.bank.base≤RepairHistogram.address s.columns m j ∧
      RepairHistogram.address s.columns m j≤ s.plan.bank.base+s.goods)
    (bound : s.plan.bank.base+s.goods<2^w)
    (keep : RepairHistogram.commit_keeps s.plan s.occurrences s.goods (s.direct+j.val) ∧
      RepairHistogram.commit_keeps s.plan s.occurrences s.goods (s.direct+s.occurrences+j.val)) :
    let out := (s.native w rows b).after m
    let ordinary := RepairHistogram.kind (goods:=s.goods) s.plan.bank s.columns m j=none
    (out (s.direct+j.val)).val=(if ordinary then RepairHistogram.installedBits s.columns m j else 0) ∧
      (out (s.direct+s.occurrences+j.val)).val=(if ordinary then RepairHistogram.consumedBits s.columns m j else 0) := by
  let base := result (RepairHistogram.directColumns s.direct s.occurrences s.goods s.plan s.columns) m
  let after := s.beforeApply b rows m
  have prefixRead (x : ℕ) (prior : x<s.broadcast) : after x=base x := by
    change image s.broadcast rows (RepairHistogram.broadcastTerm b s.price) base x=base x
    exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl prior)
  have kept (x : ℕ) (hx : RepairHistogram.commit_keeps s.plan s.occurrences s.goods x) :
      (s.native w rows b).after m x=after x := RepairHistogram.commit_frame s.columns s.plan _ _ after x ready.2.2 hx
  have jlt := j.isLt
  dsimp only
  rw [kept _ keep.1,kept _ keep.2,prefixRead _ (by omega),prefixRead _ (by omega)]
  exact RepairHistogram.direct_read _ _ _ _ _ _ j inputs hit bound

/-- The archive and sparse windows use an ordered physical layout. -/
structure EventBoard (s : StockCommit) (w : ℕ) : Prop where
  chargeFits : (RepairHistogram.ordinaryTerm s.columns s.plan s.goods s.columns.charge).Fits w s.direct
  order : s.direct+s.occurrences+s.occurrences≤ s.broadcast
  bound : s.plan.bank.base+s.goods<2^w
  keep : ∀ e : Fin s.occurrences, RepairHistogram.commit_keeps s.plan s.occurrences s.goods (s.direct+e.val) ∧
    RepairHistogram.commit_keeps s.plan s.occurrences s.goods (s.direct+s.occurrences+e.val)

theorem EventBoard.hit {s : StockCommit} (board : EventBoard s w) (b : Batch q d) (m : Memory w)
    (ready : (s.native w rows b).ready m) (e : Fin s.occurrences) :
    s.plan.bank.base≤RepairHistogram.address s.columns m e ∧ RepairHistogram.address s.columns m e≤ s.plan.bank.base+s.goods := by
  have ord := board.order
  have same := congrArg Fin.val (s.inputs_beforeApply (rows:=rows) b m (by omega) _ board.chargeFits.1 (e.val:Word w))
  change RepairHistogram.address s.columns (s.beforeApply b rows m) e=RepairHistogram.address s.columns m e at same
  have resultBounds := ready.2.2 e
  change s.plan.bank.base ≤ RepairHistogram.address s.columns (s.beforeApply b rows m) e ∧
    RepairHistogram.address s.columns (s.beforeApply b rows m) e ≤ s.plan.bank.base+s.goods at resultBounds
  exact same ▸ resultBounds

/-- `old` and `reserve` are the actual preceding snapshot. The ordinal in `slot`
selects an outstanding commodity or the separate ordinary-link destination. -/
structure Sources where
  old : Bank
  reserve : Bank
  half : Bank
  price : Bank
  mode : Expr
  owner : Bank
  parity : Bank
  slot : Expr
  credit : Expr
  charge : Expr

/-- All newly written regions are derived from the next free word and finite row
counts. The first padded region includes a disposable cell after all commodities. -/
structure Area where
  start : ℕ
  rows : ℕ
  occurrences : ℕ
  goods : ℕ
  limit : ℕ

def Area.pad (a : Area) := ProtocolRAMPurchaseSampler.span a.goods
def Area.bank (a : Area) : Bank := ⟨a.start,ProtocolRAMPurchaseSampler.bits a.goods⟩
def Area.direct (a : Area) := a.start+a.pad
def Area.broadcast (a : Area) := a.direct+2*a.occurrences
def Area.src (a : Area) := a.broadcast+a.rows
def Area.clip (a : Area) := a.src+2*a.occurrences
def Area.excess (a : Area) := a.clip+a.goods
def Area.output (a : Area) := a.excess+a.pad
def Area.stop (a : Area) := a.output+3*a.goods

def Area.columns (a : Area) (s : Sources) : RepairHistogram.Columns :=
  ⟨s.owner,s.parity,RepairHistogram.destination a.start a.goods s.slot,s.credit,s.charge⟩

def Area.plan (a : Area) (s : Sources) : RepairHistogram.CommitPlan :=
  ⟨a.bank,s.reserve,s.half,⟨a.clip,ProtocolRAMPurchaseSampler.bits a.goods⟩,
    ⟨a.excess,ProtocolRAMPurchaseSampler.bits a.goods⟩,s.mode,a.src,a.output,a.limit⟩

def fresh (a : Area) (s : Sources) : StockCommit :=
  ⟨a.occurrences,a.goods,a.columns s,a.plan s,a.direct,a.broadcast,s.price⟩

def Area.seed (a : Area) (s : Sources) : Pass := ⟨a.start,a.goods,.lookup s.old .row⟩

theorem Area.seed_frame (a : Area) (s : Sources) (m : Memory w) (x : ℕ) (h : x<a.start ∨ a.start+a.goods≤x) :
    (a.seed s).apply m x=m x := ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ h

attribute [local irreducible] Procedure.Exec CheapCode

def freshSegment (a : Area) (s : Sources) (w : ℕ) (b : Batch q d) : Commit w where
  native := ((a.seed s).procedure w).seq (((fresh a s).native w a.rows b).native)
  after := fun m => ((fresh a s).native w a.rows b).after ((a.seed s).apply m)
  ticks := (a.seed s).clock+((fresh a s).native w a.rows b).ticks
  ready := fun m => (a.seed s).Fits w ∧ ((fresh a s).native w a.rows b).ready ((a.seed s).apply m)
  cheap := @cheap_seq w ((a.seed s).procedure w) ((fresh a s).native w a.rows b).native (@scan_cheap w (a.seed s).out (a.seed s).rows (a.seed s).term) ((fresh a s).native w a.rows b).cheap
  runs := by
    rintro m ⟨seed,run⟩
    have copy : ((a.seed s).procedure w).Exec m ((a.seed s).apply m) (a.seed s).clock :=
      scan_exec _ _ _ m seed.1 seed.2
    exact copy.then (((fresh a s).native w a.rows b).runs _ run)
  keeps := fun x => (x<a.start ∨ a.start+a.goods≤x) ∧ ((fresh a s).native w a.rows b).keeps x
  frame := by
    rintro m x ⟨_,ready⟩ ⟨first,rest⟩
    exact ((((fresh a s).native w a.rows b).frame _ x ready rest)).trans (a.seed_frame s m x first)

/-- A current packet occurrence first resolves its physical edge ordinal. Its label
is the same fifth-indexed metric field used in the final seven-field reporter. -/
structure LabelSource where
  out : ℕ
  edge : Expr
  geometry : Fin 7 → Expr

def LabelSource.pass (g : LabelSource) (n : ℕ) : Pass := ⟨g.out,n,(g.geometry 5).atRow g.edge⟩

def pricedSegment (a : Area) (s : Sources) (g : LabelSource) (w : ℕ) (b : Batch q d) : Commit w where
  native := ((g.pass a.occurrences).procedure w).seq (freshSegment a s w b).native
  after := fun m => (freshSegment a s w b).after ((g.pass a.occurrences).apply m)
  ticks := (g.pass a.occurrences).clock+(freshSegment a s w b).ticks
  ready := fun m => (g.pass a.occurrences).Fits w ∧ (freshSegment a s w b).ready ((g.pass a.occurrences).apply m)
  cheap := @cheap_seq w ((g.pass a.occurrences).procedure w) (freshSegment a s w b).native (@scan_cheap w (g.pass a.occurrences).out (g.pass a.occurrences).rows (g.pass a.occurrences).term) (freshSegment a s w b).cheap
  runs := by
    rintro m ⟨heads,next⟩
    have stamp : ((g.pass a.occurrences).procedure w).Exec m ((g.pass a.occurrences).apply m) (g.pass a.occurrences).clock :=
      scan_exec _ _ _ m heads.1 heads.2
    exact stamp.then ((freshSegment a s w b).runs _ next)
  keeps := fun x => (x<g.out ∨ g.out+a.occurrences≤x) ∧ (freshSegment a s w b).keeps x
  frame := by
    rintro m x ⟨_,mounted⟩ ⟨first,next⟩
    exact (((freshSegment a s w b).frame _ x mounted next)).trans (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ first)

/-- Exactly the memory consumed by the stock correction after both physical preambles. -/
def stageInput (a : Area) (s : Sources) (g : LabelSource) (m : Memory w) :=
  (a.seed s).apply ((g.pass a.occurrences).apply m)

theorem priced_after (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d) (m : Memory w) :
    (pricedSegment a s g w b).after m=((fresh a s).native w a.rows b).after (stageInput a s g m) := rfl

end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
