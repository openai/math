import OAI.Hierarchy.ProtocolRAMStripNativeIDs
import OAI.Hierarchy.ProtocolRAMColumnReaderBounds
import OAI.Hierarchy.ProtocolRAMCatalogueEdgeCost

namespace OAI
/-! # Per-port cost of decoding the actual placed strip's physical edge -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open ProbeStage CoreBoard AdaptiveProbe BoughtSockets PurchaseFrozen
variable {h d k depth attempts : ℕ} {S : PurchaseSampler} {C H A B : Type*}

private theorem core_work (b : Board) (e : Expr) : (b.coreOnly e).work=2*e.work+3 := by
  simp only [Board.coreOnly,Expr.work];omega

theorem StripPorts.primary_work (p : StripPorts S h d k C H B) (b : Board) (u t v : ℕ)
    (col : ∀c,(p.column c).work≤u) (horiz : ∀i l,(p.horizontal i l).work≤t)
    (probe : ∀i,(p.probe i).work≤v) (e : ColumnWires.Role C H (A⊕B) k) :
    (p.primary b e).work≤2*(u+t+v+6)+3 := by
  cases e with
  | catalyst c axis =>
    change (b.coreOnly (p.radiusAt c axis false)).work≤_
    rw [core_work];have read:=col c;change 2*((p.column c).work+5)+3≤_;omega
  | radius c axis side =>
    change (b.coreOnly (p.radiusAt c axis side)).work≤_
    rw [core_work];have read:=col c;change 2*((p.column c).work+5)+3≤_;omega
  | cross c axes left right =>
    change (b.coreOnly (p.crossAt c axes left right)).work≤_
    rw [core_work];have read:=col c;change 2*((p.column c).work+5)+3≤_;omega
  | horizontal i l =>
    change (b.coreOnly (p.horizontal i l)).work≤_
    rw [core_work];have read:=horiz i l;omega
  | extra i =>
    rcases i with a|bought
    · change 1≤_;omega
    · exact (probe bought).trans (by omega)

theorem StripPorts.mate_work (p : StripPorts S h d k C H B) (b : Board) (u : ℕ)
    (col : ∀c,(p.column c).work≤u) (e : ColumnWires.Role C H (A⊕B) k) :
    (p.mate b e).work≤2*(u+5)+3 := by
  cases e with
  | catalyst c axis =>
    change (b.coreOnly (p.radiusAt c axis true)).work≤_
    rw [core_work];have read:=col c;change 2*((p.column c).work+5)+3≤_;omega
  | radius | cross | horizontal | extra => change 1≤_;omega

theorem payloadHorizontal_work (S : PurchaseSampler) (h d k base u : ℕ)
    (col : PayloadStrip.Columns (Stages h d)→Expr) (read : ∀c,(col c).work≤u)
    (e : Fin (PayloadStrip.edgeCount (Stages h d))) (l : ColumnLayer k) :
    (payloadHorizontal S h d k base col e l).work≤u+7 := by
  unfold payloadHorizontal;split
  · rw [CoreLookup.field_work];have size:=read (Strip.horizontal _ e).left;omega
  · change 7≤_;omega

def chainWork (N D keys u : ℕ) :=
  (1+N*(selectWork keys 1+selectWork keys 9+7))+
    (1+D*(selectWork keys 7+u+7))

theorem chainHorizontal_work (sh : Shelf) (S : PurchaseSampler) (h d k depth base start u : ℕ)
    (col : ChainStrip.Columns depth→Expr) (read : ∀c,(col c).work≤u)
    (e : Fin (ChainStrip.edgeCount depth)) (l : ColumnLayer k) :
    (chainHorizontal sh S h d k depth base start col e l).work≤ chainWork (Stages h d) S.degree (count h d k) u := by
  let head:=StripDirectory.stratumHeader h d k S.degree depth start
  have stages : (stageKey head h d k).work≤ selectWork (count h d k) 1 := select_work _ _ (fun _=>le_rfl)
  have rows (j : Fin (depth+1)) : (rowKey sh S head h d k depth j).work≤ selectWork (count h d k) 9 :=
    select_work _ _ (fun _=>le_rfl)
  have digits (j : Fin depth) : (digitKey sh S head h d k depth j).work≤ selectWork (count h d k) 7 :=
    select_work _ _ (fun _=>le_rfl)
  unfold chainHorizontal;split
  · rename_i ok
    let j : Fin (depth+1):=⟨e.val/2,by have := e.isLt;dsimp [ChainStrip.edgeCount] at this;omega⟩
    apply (choose_work_bound _ _ (selectWork (count h d k) 9+5) _ (stageKey head h d k) (fun t=>by
      rw [CoreLookup.field_work];exact Nat.add_le_add_right (rows j) 5)).trans
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) 1).trans (Nat.le_add_right _ _)
  · rename_i ok
    let j : Fin depth:=⟨e.val/2,by have := e.isLt;dsimp [ChainStrip.edgeCount] at this;omega⟩
    apply (choose_work_bound _ _ (u+5) _ (digitKey sh S head h d k depth j) (fun i=>by
      rw [CoreLookup.field_work];exact Nat.add_le_add_right (read _) 5)).trans
    have size:=digits j
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) 1).trans (Nat.le_add_left _ _)

def purchasedColumnWork (d k attempts : ℕ) :=
  selectWork ((2*rounds d+1)*(2*k)) (70+15*ReportSockets.copies k attempts)

theorem payloadWork (S : PurchaseSampler) (b : Board) (directory col remap sites super K G H h W k attempts : ℕ)
    (i : Fin (Fintype.card (StripDirectory.PayloadRole (Stages h (2^W)) k))) :
    let u:=56+8*ReportSockets.copies k attempts
    (payloadEdge (payloadPorts S directory col remap sites super K G H h W k attempts) b i).work≤2*(u+(u+7)+0+6)+3 := by
  intro u
  let p:=payloadPorts S directory col remap sites super K G H h W k attempts
  have cells (c) : (p.column c).work≤u := ColumnROM.payload_work _ _ _ _ _ _ _ _ _ _
  exact p.primary_work b u (u+7) 0 cells (payloadHorizontal_work S _ _ _ _ _ p.column cells) (fun i=>i.elim) _

theorem purchased_column_work (v : Directory attempts) (sh : Shelf) (S : PurchaseSampler) (b : Board)
    (directory col keyBase K G H h W k depth birth : ℕ) (c : ChainStrip.Columns depth) :
    ((purchasePorts b v sh S directory col keyBase K G H h W k depth birth).column c).work≤
      purchasedColumnWork (2^W) k attempts := by
  change _≤ selectWork ((2*rounds (2^W)+1)*(2*k)) (70+15*ReportSockets.copies k attempts)
  rw [←count_eq h (2^W) k]
  apply select_work
  intro i
  rw [ColumnROM.stage_work]
  change 2*9+52+ReportSockets.copies k attempts*(9+6)≤_
  omega

theorem purchaseWork (v : Directory attempts) (sh : Shelf) (S : PurchaseSampler) (b : Board)
    (directory col keyBase K G H h W k depth birth : ℕ)
    (i : Fin (Fintype.card (StripDirectory.PurchasedRole depth k))) :
    let u:=purchasedColumnWork (2^W) k attempts
    let t:=chainWork (Stages h (2^W)) S.degree (count h (2^W) k) u
    (purchaseEdge (purchasePorts b v sh S directory col keyBase K G H h W k depth birth) b i).work≤2*(u+t+4+6)+3 := by
  intro u t
  let p:=purchasePorts b v sh S directory col keyBase K G H h W k depth birth
  have cells (c) : (p.column c).work≤u:=
    purchased_column_work v sh S b directory col keyBase K G H h W k depth birth c
  exact p.primary_work b u t 4 cells (chainHorizontal_work sh S _ _ _ _ _ _ _ p.column cells) (fun _=>le_rfl) _

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
