import OAI.Hierarchy.ProbeCoreCode
import OAI.Hierarchy.ProbePaidPayloadHoriz
import OAI.Hierarchy.ProtocolRAMStripPhysicalStep

namespace OAI
/-! # Both endpoints of the originally retained DFS candidate's paid horizontals -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard PurchaseFrozen StockCommit
open scoped Fin.CommRing Classical

variable {h d k R w H : ℕ} {S : PurchaseSampler}

def retainedCol (π : Equiv.Perm (Fin (2^h))) (marks : StageAt h d→(Fin k×Bool)→Finset (Fin (2^h)))
    (p : LiveChains S π H marks) (c : ChainStrip.Columns H) : Columns h d :=
  .inr (.inl (stripPlace S π H marks p c))

private theorem retained_in (π : Equiv.Perm (Fin (2^h))) (marks : StageAt h d→(Fin k×Bool)→Finset (Fin (2^h)))
    (p : LiveChains S π H marks) (j : Fin (H+1)) :
    let a:=advisedStage h d π p.1
    let v:=liveRow S π H marks p j
    retainedCol π marks p (ChainStrip.inlet H j)=inputCol p.1 (a.group v) (a.input v) := by
  intro a v
  rw [retainedCol, stripPlace_in]
  exact congrArg (fun g => inputCol p.1 g (a.input v)) (live_in_ball S π H marks p j).1.symm

private theorem retained_out (π : Equiv.Perm (Fin (2^h))) (marks : StageAt h d→(Fin k×Bool)→Finset (Fin (2^h)))
    (p : LiveChains S π H marks) (j : Fin (H+1)) :
    let a:=advisedStage h d π p.1
    let v:=liveRow S π H marks p j
    retainedCol π marks p (ChainStrip.outlet H j)=outputCol p.1 (a.group v) (a.output v) := by
  intro a v
  rw [retainedCol, stripPlace_out]
  exact congrArg (fun g => outputCol p.1 g (a.output v)) (live_in_ball S π H marks p j).1.symm

private theorem sample_from (S : PurchaseSampler) (t : StageAt h d) (g : (stageAt h d t).Group)
    (o : Fin (stageAt h d t).span) (digit : Fin S.degree) (f : Sample S h d)
    (read : CoreLookup.neighbor S (outputCol t g o) digit=some f) (l : ColumnLayer k) :
    (freeEnds (.inr (.inr (.inr (f,l))))).1=(outputCol t g o,l) := by
  simp only [CoreLookup.neighbor,outputCol] at read
  split at read
  · obtain rfl := Option.some.inj read
    rfl
  · contradiction

/-- Alternating choice of original stage tile and actual sampler digit.
The typed input key and all per-step DFSTile words are read at the
same candidate row. No data-dependent adjacency table is supplied. -/
theorem chain_faces_price (M : ℕ) (sh : Shelf) (base start : ℕ) (col : ChainStrip.Columns H→Expr)
    (order : Fin R≃Edges S h d k) (m : Memory w) (loaded : CoreLookup.Loaded base order m)
    (π : Equiv.Perm (Fin (2^h))) (marks : StageAt h d→(Fin k×Bool)→Finset (Fin (2^h)))
    (p : LiveChains S π H marks) (r : Word w) (stageRoom : Stages h d≤2^w) (degreeRoom : S.degree≤2^w)
    (stage : ((stageKey (StripDirectory.stratumHeader h d k S.degree H start) h d k).eval m r).val=p.1.val)
    (rows : ∀j,((rowKey sh S (StripDirectory.stratumHeader h d k S.degree H start) h d k H j).eval m r).val=
      (liveRow S π H marks p j).val)
    (digits : ∀j,((digitKey sh S (StripDirectory.stratumHeader h d k S.degree H start) h d k H j).eval m r).val=
      ((PurchaseDirectory.item (BoughtLocation.localIndex p)).2 j).val)
    (column : ∀c,((col c).eval m r).val=((Fintype.equivFin _) (retainedCol π marks p c)).val)
    (e : Fin (ChainStrip.edgeCount H)) (l : ColumnLayer k) :
    ∃f : Edges S h d k,
      (chainHorizontal sh S h d k H base start col e l).eval m r=((order.symm f).val:Word w) ∧
      (coreCode S M f:ℝ)=ChainStrip.length H e ∧
      HorizontalFaces (retainedCol π marks p) (Strip.horizontal _ e) l (CoreBoard.ends π f) := by
  let a:=advisedStage h d π p.1
  let row:=liveRow S π H marks p
  let ends:=Strip.horizontal (ChainStrip.edgeCount H) e
  have bound:=e.isLt
  change e.val<2*H+1 at bound
  by_cases even : e.val%2=0
  · let j : Fin (H+1):=⟨e.val/2,by omega⟩
    have pos : e.val=2*j.val := by dsimp [j];omega
    have left : ends.left=ChainStrip.inlet H j := Subtype.ext (Fin.ext pos)
    have right : ends.right=ChainStrip.outlet H j := Subtype.ext (Fin.ext (by change e.val+1=2*j.val+1;omega))
    refine ⟨.inr ((row j,p.1),l),chain_tile sh S base start col order m loaded e j pos l r p.1 (row j) stageRoom stage (rows j),by simp [coreCode,ChainStrip.length,even],Or.inl ?_⟩
    change ((inputCol p.1 (a.group (row j)) (a.input (row j)),l),
        (outputCol p.1 (a.group (row j)) (a.output (row j)),l))=
      ((retainedCol π marks p ends.left,l),(retainedCol π marks p ends.right,l))
    rw [left,right,retained_in,retained_out]
  · let j : Fin H:=⟨e.val/2,by omega⟩
    have pos : e.val=2*j.val+1 := by dsimp [j];omega
    have left : ends.left=ChainStrip.outlet H j.castSucc := Subtype.ext (Fin.ext pos)
    have right : ends.right=ChainStrip.inlet H j.succ := Subtype.ext (Fin.ext (by change e.val+1=2*(j.val+1);omega))
    let u:=outputCol p.1 (a.group (row j.castSucc)) (a.output (row j.castSucc))
    let digit:=(PurchaseDirectory.item (BoughtLocation.localIndex p)).2 j
    obtain ⟨f,lookup,toCol⟩:=retained_step S π H marks p j
    have sourceCol : retainedCol π marks p ends.left=u := left ▸ retained_out π marks p j.castSucc
    have targetCol : retainedCol π marks p ends.right=inputCol p.1 (a.group (row j.succ)) (a.input (row j.succ)) :=
      right ▸ retained_in π marks p j.succ
    have sourceRead : ((col ends.left).eval m r).val=((Fintype.equivFin _) u).val := by rw [column,sourceCol]
    let actual : Edges S h d k:=.inl (.inr (.inr (.inr (f,l))))
    refine ⟨actual,chain_sample sh S base start col order m loaded e j pos l r u digit f degreeRoom (digits j) sourceRead lookup,
      by simp [actual,coreCode,ChainStrip.length,even],Or.inl ?_⟩
    have fromCol:=sample_from S p.1 _ _ digit f lookup l
    have dst := congrArg Prod.fst toCol
    apply Prod.ext
    · exact fromCol.trans (congrArg (fun c=>(c,l)) sourceCol.symm)
    · exact Prod.ext (dst.trans targetCol.symm) rfl

theorem chain_faces (sh : Shelf) (base start : ℕ) (col : ChainStrip.Columns H→Expr)
    (order : Fin R≃Edges S h d k) (m : Memory w) (loaded : CoreLookup.Loaded base order m)
    (π : Equiv.Perm (Fin (2^h))) (marks : StageAt h d→(Fin k×Bool)→Finset (Fin (2^h)))
    (p : LiveChains S π H marks) (r : Word w) (stageRoom : Stages h d≤2^w) (degreeRoom : S.degree≤2^w)
    (stage : ((stageKey (StripDirectory.stratumHeader h d k S.degree H start) h d k).eval m r).val=p.1.val)
    (rows : ∀j,((rowKey sh S (StripDirectory.stratumHeader h d k S.degree H start) h d k H j).eval m r).val=
      (liveRow S π H marks p j).val)
    (digits : ∀j,((digitKey sh S (StripDirectory.stratumHeader h d k S.degree H start) h d k H j).eval m r).val=
      ((PurchaseDirectory.item (BoughtLocation.localIndex p)).2 j).val)
    (column : ∀c,((col c).eval m r).val=((Fintype.equivFin _) (retainedCol π marks p c)).val)
    (e : Fin (ChainStrip.edgeCount H)) (l : ColumnLayer k) :
    ∃f : Edges S h d k,
      (chainHorizontal sh S h d k H base start col e l).eval m r=((order.symm f).val:Word w) ∧
      HorizontalFaces (retainedCol π marks p) (Strip.horizontal _ e) l (CoreBoard.ends π f) := by
  obtain ⟨f,read,_,faces⟩:=chain_faces_price 0 sh base start col order m loaded π marks p r stageRoom degreeRoom stage rows digits column e l
  exact ⟨f,read,faces⟩

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
