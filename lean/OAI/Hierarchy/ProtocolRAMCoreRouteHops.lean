import OAI.Hierarchy.ProtocolRAMStripPortReads
import OAI.Hierarchy.ProtocolRAMStripHorizontal
import OAI.Hierarchy.ProbeCoreWalks

namespace OAI
/-! # Native edge ordinals for payload, quote and catalyst settlement walks -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard ReportSockets BoughtSockets CatalogueRows
open scoped Classical Fin.CommRing
variable {z W k attempts K H w R : ℕ} {S : PurchaseSampler}

structure Source where
  catalogue : ℕ
  columnBase : ℕ
  remap : ℕ
  sites : ℕ
  superBase : ℕ
  oldGroups : ℕ
  bins : ℕ
  height : ℕ

def Source.payloadExpr (x : Source) (S : PurchaseSampler) (z W k attempts : ℕ)
    (e : Fin (PayloadStrip.edgeCount (Stages z (2^W)))) : Expr :=
  let p := payloadPorts S x.catalogue x.columnBase x.remap x.sites x.superBase x.oldGroups x.bins x.height z W k attempts
  payloadHorizontal S z (2^W) k x.catalogue p.column e none

def Source.tileExpr (x : Source) (S : PurchaseSampler) (z W k : ℕ) (t : StageAt z (2^W)) : Expr :=
  CoreLookup.field (S:=S) (h:=z) (d:=2^W) x.catalogue (CoreLookup.tile t (none : ColumnLayer k)) .row

def Source.quoteExpr (x : Source) (S : PurchaseSampler) (z W k attempts : ℕ) (t : StageAt z (2^W))
    (layer : Fin k×Bool) : Expr :=
  CoreLookup.field (S:=S) (h:=z) (d:=2^W) x.catalogue (CoreLookup.radius layer.1 layer.2)
    (ColumnROM.payloadColumn x.columnBase x.remap x.sites x.superBase x.oldGroups x.bins x.height k attempts (.stage t true))

def Source.centerExpr (x : Source) (S : PurchaseSampler) (z W k : ℕ) (layer : Fin k×Bool) : Expr :=
  CoreLookup.field (S:=S) (h:=z) (d:=2^W) x.catalogue (CoreLookup.radius layer.1 layer.2) .row

def addresses (catalogue columnBase remap sites superBase K G H : ℕ) : Source :=
  ⟨catalogue,columnBase,remap,sites,superBase,K,G,H⟩

structure Readable (x : Source) (S : PurchaseSampler) (z W k attempts : ℕ)
    (order : Fin R≃Edges S z (2^W) k) (π : Equiv.Perm (Fin (2^z))) (m : Memory w) : Prop where
  groups : ∃ gs : Fin x.oldGroups≃AllGroups z (2^W),
    ∃ dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) x.height,
      dir.groups=x.bins ∧ ColumnROM.Tables z W k attempts x.columnBase x.remap x.sites x.superBase gs dir π m
  raw : Native.Resident (Native.initialOutput z) m (fun p : Fin (2^z)=>(π p).val)
  lookup : CoreLookup.Loaded x.catalogue order m
  rows : 2^z≤2^w
  columns : Fintype.card (CoreBoard.Columns z (2^W))≤2^w

theorem Readable.tile {x : Source} {order : Fin R≃Edges S z (2^W) k} {π : Equiv.Perm (Fin (2^z))} {m : Memory w}
    (data : Readable x S z W k attempts order π m) (p : Fin (2^z)) (t : StageAt z (2^W)) :
    (x.tileExpr S z W k t).eval m (p.val:Word w)=((order.symm (tileEdge p t none)).val:Word w) := by
  let ix : Fin (CoreLookup.positions z (2^W)) := ⟨p.val,p.isLt.trans_le (Nat.le_max_right _ _)⟩
  exact data.lookup.read (CoreLookup.tile t none) .row (p.val : Word w) ix
    (Fin.val_cast_of_lt (p.isLt.trans_le data.rows)) _ (CoreLookup.resolve_tile p t none)

theorem Readable.center {x : Source} {order : Fin R≃Edges S z (2^W) k} {π : Equiv.Perm (Fin (2^z))} {m : Memory w}
    (data : Readable x S z W k attempts order π m) (c : CoreBoard.Columns z (2^W)) (l : Fin k×Bool) :
    (x.centerExpr S z W k l).eval m (((Fintype.equivFin _) c).val:Word w)=((order.symm (radiusEdge c l)).val:Word w) := by
  let ix : Fin (CoreLookup.positions z (2^W)) := ⟨_,((Fintype.equivFin _) c).isLt.trans_le (Nat.le_max_left _ _)⟩
  exact data.lookup.read (CoreLookup.radius l.1 l.2) .row (((Fintype.equivFin _) c).val : Word w) ix
    (Fin.val_cast_of_lt (((Fintype.equivFin _) c).isLt.trans_le data.columns)) _ (CoreLookup.resolve_radius c l.1 l.2)

theorem Readable.quote {x : Source} {order : Fin R≃Edges S z (2^W) k} {π : Equiv.Perm (Fin (2^z))} {m : Memory w}
    (data : Readable x S z W k attempts order π m) (p : Fin (2^z)) (t : StageAt z (2^W)) (l : Fin k×Bool) :
    let a:=advisedStage z (2^W) π t
    (x.quoteExpr S z W k attempts t l).eval m (p.val:Word w)=
      ((order.symm (radiusEdge (outputCol t (a.group p) (a.output p)) l)).val:Word w) := by
  intro a
  obtain ⟨groups,dir,bins,tables⟩ := data.groups
  let c := outputCol t (a.group p) (a.output p)
  let ix : Fin (CoreLookup.positions z (2^W)) := ⟨_,((Fintype.equivFin _) c).isLt.trans_le (Nat.le_max_left _ _)⟩
  have read := ColumnROM.payload_read x.columnBase x.remap x.sites x.superBase groups dir π m tables data.raw p (.stage t true)
  rw [bins] at read
  exact data.lookup.read _ _ _ ix ((congrArg Fin.val read).trans
    (Fin.val_cast_of_lt (((Fintype.equivFin _) c).isLt.trans_le data.columns))) _ (CoreLookup.resolve_radius c l.1 l.2)

theorem Readable.payload_tile {x : Source} {order : Fin R≃Edges S z (2^W) k} {π : Equiv.Perm (Fin (2^z))} {m : Memory w}
    (data : Readable x S z W k attempts order π m) (p : Fin (2^z))
    (e : Fin (PayloadStrip.edgeCount (Stages z (2^W)))) (t : StageAt z (2^W)) (atStage : e.val=2*t.val+1) :
    (x.payloadExpr S z W k attempts e).eval m (p.val:Word w)=((order.symm (tileEdge p t none)).val:Word w) :=
  CatalogueRows.payload_tile _ _ order m data.lookup p e t none atStage data.rows

theorem Readable.payload_joint {x : Source} {order : Fin R≃Edges S z (2^W) k} {π : Equiv.Perm (Fin (2^z))} {m : Memory w}
    (data : Readable x S z W k attempts order π m) (p : Fin (2^z)) (j : Fin (Stages z (2^W)+1))
    (e : Fin (PayloadStrip.edgeCount (Stages z (2^W)))) (atJoint : e.val=2*j.val) :
    (x.payloadExpr S z W k attempts e).eval m (p.val:Word w)=((order.symm (jointEdge π p j none)).val:Word w) := by
  obtain ⟨groups,dir,bins,tables⟩ := data.groups
  let fromCol:=payloadFreeFrom π p j
  let toCol:=payloadFreeTo π p j
  let chart:=Strip.horizontal (PayloadStrip.edgeCount (Stages z (2^W))) e
  obtain ⟨left,right,_⟩ := payloadPlace_free π p j
  have same : e=(⟨2*j.val,by have := j.isLt;unfold PayloadStrip.edgeCount;omega⟩ : Fin (PayloadStrip.edgeCount (Stages z (2^W)))) :=
    Fin.ext atJoint
  have first : payloadPlace π p chart.left=fromCol := by simpa only [chart,same] using left
  have second : payloadPlace π p chart.right=toCol := by simpa only [chart,same] using right
  have apart : fromCol≠toCol := by rw [←first,←second];exact (payloadPlace π p).injective.ne chart.apart
  let ports := payloadPorts S x.catalogue x.columnBase x.remap x.sites x.superBase x.oldGroups x.bins x.height z W k attempts
  have native := CatalogueRows.payload_column S x.catalogue x.columnBase x.remap x.sites x.superBase groups dir π m tables
    data.raw p chart.left
  rw [bins,first] at native
  have val : ((ports.column chart.left).eval m (p.val:Word w)).val=((Fintype.equivFin _) fromCol).val :=
    (congrArg Fin.val native).trans (Fin.val_cast_of_lt (((Fintype.equivFin _) fromCol).isLt.trans_le data.columns))
  exact CatalogueRows.payload_fixed x.catalogue ports.column order m data.lookup _ e (by omega) none fromCol toCol
    (payloadFree_fixed π p j) apart val

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
