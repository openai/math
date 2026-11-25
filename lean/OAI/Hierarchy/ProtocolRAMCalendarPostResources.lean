import OAI.Hierarchy.ProtocolRAMBatchResources
import OAI.Hierarchy.ProtocolRAMPostFactorResources

namespace OAI
/-! # Fixed text and linear work from the actual operands of a posted repair -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.PostResources
open PurchaseStage RowResources
open scoped Classical
variable {q d U : ℕ}

structure LinkCaps (l : Link) (U : ℕ) : Prop where
  group : l.group.work≤U
  endpoint : l.endpoint.work≤U
  opposite : l.opposite.work≤U
  length : l.lengthCode.work≤U

structure Caps (L : Dispatch) (B : Repair q d) (U : ℕ) : Prop where
  arity : q≤U
  goods : d≤U
  maxWidth : B.batch.maxWidth≤U
  packet : (enabledBatch L B).packet.work≤U
  owner : B.batch.owner.work≤U
  field : ∀j,(B.batch.field j).work≤U
  stock : ∀j,(B.batch.stock j).work≤U
  perCopy : ∀j,(B.batch.perCopy j).work≤U
  wire : ∀i j,(B.wire i j).work≤U
  printed : ∀j,(B.reportWidth j).work≤U
  link : LinkCaps B.link U
  purchase : LinkCaps B.purchaseLink U
  menu : B.purchaseMenu.work≤U
  reserve : ∀i,(B.reserve i).work≤U
  quotes : ∀e∈B.batch.quotes,e.work≤U
  quoteCount : B.batch.quotes.length≤U
  excess : B.tests.excess.term.work≤U
  payload : B.tests.payload.term.work≤U
  discrepancy : B.tests.discrepancy.term.work≤U

/-- These are the only nonconstant indexed expression builders in the post
program. All depend solely on the actual batch width and the two port counts. -/
private structure Compiled (L : Dispatch) (B : Repair q d) (K : ℕ) : Prop where
  invalid : (invalidExpr (enabledBatch L B)).work≤K
  selected : ((enabledBatch L B).ifSelected ((enabledBatch L B).ifPacket (enabledBatch L B).packet (.lit 0)) (.lit 0)).work≤K
  report : ((enabledBatch L B).wire B.reportWidth).work≤K
  update : ∀j,((enabledBatch L B).nextStock j ((enabledBatch L B).wire (B.wire j))).work≤K

private theorem bounded_args {I J : Type*} [Fintype J] (e : I→J→Expr)
    (bound : ∀j,RowResources.Bounded (fun i=>e i j)) : ∃K,∀i j,(e i j).work≤K := by
  classical
  let c (j : J):=Classical.choose (bound j)
  exact ⟨Finset.univ.sup c,fun i j=>(Classical.choose_spec (bound j) i).trans (Finset.le_sup (f := c) (Finset.mem_univ j))⟩

private theorem compiled_at (q d M U : ℕ) : ∃K,∀(L : Dispatch)(B : Repair q d),
    Caps L B U→B.batch.maxWidth=M → Compiled L B K := by
  let I:={t : Dispatch×Repair q d // Caps t.1 t.2 U ∧ t.2.batch.maxWidth=M}
  let b (i : I):=enabledBatch i.1.1 i.1.2
  have batch : BatchOperands b M :=
    ⟨fun i=>i.2.2,⟨U,fun i=>i.2.1.packet⟩,RowResources.row,
      fun j=>⟨U,fun i=>i.2.1.field j⟩,fun j=>⟨U,fun i=>i.2.1.stock j⟩,fun j=>⟨U,fun i=>i.2.1.perCopy j⟩⟩
  obtain ⟨ki,hi⟩:=batch.valid (RowResources.lit (fun _=>0)) (RowResources.lit (fun _=>1))
  obtain ⟨ks,hs⟩:=batch.selection (batch.hist batch.packet (RowResources.lit (fun _=>0))) (RowResources.lit (fun _=>0))
  obtain ⟨kr,hr⟩:=batch.width (fun i=>i.1.2.reportWidth) (fun j=>⟨U,fun i=>i.2.1.printed j⟩)
  have updates (j : Fin d) : Bounded (fun i=> (b i).nextStock j ((b i).wire (i.1.2.wire j))) :=
    batch.updated j (batch.width (fun i=>i.1.2.wire j) (fun s=>⟨U,fun i=>i.2.1.wire j s⟩))
  obtain ⟨ku,hu⟩:=bounded_args _ updates
  refine ⟨ki+ks+kr+ku,?_⟩
  intro L B small width
  let i : I:=⟨(L,B),small,width⟩
  exact ⟨(hi i).trans (by omega),(hs i).trans (by omega),(hr i).trans (by omega),
    fun j=>(hu i j).trans (by omega)⟩

private theorem compiled (U : ℕ) : ∃K,∀{q d}(L : Dispatch)(B : Repair q d),Caps L B U → Compiled L B K := by
  classical
  let I:=Fin (U+1)×Fin (U+1)×Fin (U+1)
  let fee (j : I):=Classical.choose (compiled_at j.1.val j.2.1.val j.2.2.val U)
  refine ⟨Finset.univ.sup fee,?_⟩
  intro q d L B caps
  let j : I:=(⟨q,Nat.lt_succ_of_le caps.arity⟩,⟨d,Nat.lt_succ_of_le caps.goods⟩,
    ⟨B.batch.maxWidth,Nat.lt_succ_of_le caps.maxWidth⟩)
  have spec : Compiled L B (fee j):=Classical.choose_spec (compiled_at q d B.batch.maxWidth U) L B caps rfl
  have top : fee j≤Finset.univ.sup fee:=Finset.le_sup (Finset.mem_univ j)
  exact ⟨spec.invalid.trans top,spec.selected.trans top,spec.report.trans top,fun i=>(spec.update i).trans top⟩

private theorem mode_bound (t : AttemptGate.Inputs) : (AttemptGate.mode t).work≤64 := by
  obtain ⟨a,b,c,d,i,r⟩:=t
  cases i <;> cases r <;> norm_num [AttemptGate.mode,AttemptGate.nonzero,Expr.work]

private theorem listed {K : ℕ} (L : Dispatch) (B : Repair q d) (small : Caps L B U)
    (core : Compiled L B K) (p : Pass) (hp : p∈writes L B) : p.term.work≤2000*(K+U+1) := by
  have mode:=mode_bound B.policy
  have price : (buyWord L B).work≤80 := by
    simp only [buyWord,AttemptGate.ifPurchase,AttemptGate.ifMode,Expr.work]
    omega
  simp only [writes,List.mem_cons,List.mem_append] at hp
  rcases hp with rfl|rfl|rfl|((report|purchase)|stocks|quotes)
  · exact small.packet.trans (by omega)
  · exact price.trans (by omega)
  · exact mode.trans (by omega)
  · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp report
    obtain ⟨hg,he,ho,hl⟩:=small.link
    have named:=core.selected
    have width:=core.report
    have smallRoom : U ≤ 2000*(K+U+1) := by omega
    have codeRoom : K ≤ 2000*(K+U+1) := by omega
    fin_cases j
    · exact hg.trans smallRoom
    · exact he.trans smallRoom
    · exact ho.trans smallRoom
    · change 4 ≤ 2000*(K+U+1)
      omega
    · exact width.trans codeRoom
    · exact hl.trans smallRoom
    · exact named.trans codeRoom
  · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp purchase
    obtain ⟨hg,he,ho,hl⟩:=small.purchase
    have menu:=small.menu
    have smallRoom : U ≤ 2000*(K+U+1) := by omega
    fin_cases j
    · exact hg.trans smallRoom
    · exact he.trans smallRoom
    · exact ho.trans smallRoom
    · change 4 ≤ 2000*(K+U+1)
      omega
    · change 1 ≤ 2000*(K+U+1)
      omega
    · exact hl.trans smallRoom
    · change (buyWord L B).work + 1 + 1 + B.purchaseMenu.work + 1 ≤ 2000*(K+U+1)
      omega
  · obtain ⟨ps,psmem,hp⟩:=List.mem_flatten.mp stocks
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp psmem
    have updated:=core.update j
    have stock:=small.stock j
    have held:=small.reserve j
    simp only [stockWrites,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl <;>
      cases adv:B.feedOnAdvance <;>
      simp only [retained,discharge,saved,fedStock,feed,AttemptGate.ifMode,AttemptGate.ifRepair,
        AttemptGate.ifPurchase,AttemptGate.ifAdvance,StockAccounts.clipped,StockAccounts.overflow,
        adv,Bool.false_eq_true,ite_true,ite_false,Expr.work] <;>
      first | omega | (change (B.batch.stock j).work≤U at stock; dsimp only [enabledBatch] at *; omega)
  · obtain ⟨i,rfl⟩:=List.mem_ofFn.mp quotes
    exact (small.quotes _ (List.getElem_mem ..)).trans (by omega)

theorem bills (U : ℕ) : ∃C,∀{q d h : ℕ}(L : Dispatch)(B : Repair q d),Caps L B U →
    L.candidates≤2^h*U → B.tests.excess.rows≤2^h*U → B.tests.payload.rows≤2^h*U →
    B.tests.discrepancy.rows≤2^h*U → postTicks L B≤C*2^h ∧ postText L B≤C := by
  obtain ⟨K,code⟩:=compiled U
  obtain ⟨C,bound⟩:=post_resources_of_work U (2000*(K+U+1))
  refine ⟨C,?_⟩
  intro q d h L B small
  have pay:=code L B small
  refine bound L B small.goods small.quoteCount (listed L B small pay) ?_ ?_ ?_ ?_ ?_
  · have mode:=mode_bound B.policy
    have own:=small.owner
    simp only [repairMask,AttemptGate.ifRepair,AttemptGate.ifMode,Expr.work]
    omega
  · exact pay.invalid.trans (by omega)
  · exact small.excess.trans (by omega)
  · exact small.payload.trans (by omega)
  · exact small.discrepancy.trans (by omega)

end Hierarchy.ProtocolRAM.Calendar.PostResources
end

end OAI
