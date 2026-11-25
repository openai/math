import OAI.Hierarchy.ProtocolRAMStoredStageColumns
import OAI.Hierarchy.ProtocolRAMCoreEdgeLookup
import OAI.Hierarchy.ProtocolRAMCatalogueEdgeID
import OAI.Hierarchy.ProbeShapeMenus
import OAI.Hierarchy.ProbePayloadPlacement
import OAI.Hierarchy.ProbeChainPlacement

namespace OAI
/-! # Physical programs and column readbacks for outer and purchased strip ports -/

noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage PurchaseFrozen
open scoped Classical Fin.CommRing
variable {attempts : ℕ}

/-- At an inner repair the originating trial is already part of the public
schedule. Only its own physical slab is read, including for inactive candidates. -/
def Directory.eventPosition (v : Directory attempts) (sh : Shelf) (base : ℕ) (S : PurchaseSampler)
    (h W k depth K G H : ℕ) (position : Fin (depth+1)) (side : Bool) : Expr :=
  select (StripDirectory.stratumHeader h (2^W) k S.degree depth v.keysBase) (fun i : Key h (2^W) k=>
    ColumnROM.stageColumn base v.remapBase v.sitesBase v.superBase K G H k attempts
      (stage i) side (readTile sh S depth i position))

end Hierarchy.ProtocolRAM.BoughtSockets

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard PurchaseFrozen BoughtSockets StockCommit
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
variable {h d k z W w dp attempts K : ℕ} {S : PurchaseSampler} {C H A B : Type*}

/-- Column queries, horizontal queries, and the acquired candidate all take the
original ball ordinal. Fixed local roles choose the relevant expression at compile time. -/
structure StripPorts (S : PurchaseSampler) (h d k : ℕ) (C H B : Type*) where
  directory : ℕ
  column : C→Expr
  horizontal : H → ColumnLayer k→Expr
  probe : B→Expr

def StripPorts.radiusAt (p : StripPorts S h d k C H B) (c : C) (axis : Fin k) (side : Bool) :=
  CoreLookup.field (S:=S) (h:=h) (d:=d) p.directory (CoreLookup.radius axis side) (p.column c)

def crossDatum (axes : {ab : Fin k×Fin k // ab.1≠ab.2}) (s t : Bool) : CoreLookup.AxisPair k×(Bool×Bool) :=
  if asc : axes.val.1<axes.val.2 then (⟨axes.val,asc⟩,s,t)
  else (⟨(axes.val.2,axes.val.1),lt_of_le_of_ne (le_of_not_gt asc) axes.property.symm⟩,t,s)

def StripPorts.crossAt (p : StripPorts S h d k C H B) (c : C)
    (axes : {ab : Fin k×Fin k // ab.1≠ab.2}) (s t : Bool) : Expr :=
  let a:=crossDatum axes s t
  CoreLookup.field (S:=S) (h:=h) (d:=d) p.directory (CoreLookup.cross a.1 a.2.1 a.2.2) (p.column c)

/-- A failed core directory query cannot alias the first acquired candidate. -/
def Board.coreOnly (b : Board) (e : Expr) : Expr :=
  .branch .lt e (.lit b.coreRows) e (.lit b.rows)
/-- The demand of a commodity flows into the inventory. The actual cash-paid
ports resolve to the public core or original acquired probe. -/
def StripPorts.primary (p : StripPorts S h d k C H B) (b : Board) : ColumnWires.Role C H (A⊕B) k→Expr
  | .catalyst c axis => b.coreOnly (p.radiusAt c axis false)
  | .radius c axis side => b.coreOnly (p.radiusAt c axis side)
  | .cross c axes s t => b.coreOnly (p.crossAt c axes s t)
  | .horizontal e l => b.coreOnly (p.horizontal e l)
  | .extra (.inl _) => .lit b.rows
  | .extra (.inr birth) => p.probe birth

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard PurchaseFrozen BoughtSockets StockCommit
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
variable {h d k z W w H dp attempts K : ℕ} {S : PurchaseSampler}

/-- A payload route alternates free joins and the actual advised tile of the original
record. Fixed joins can be looked up by their starting column since they form a matching. -/
def payloadHorizontal (S : PurchaseSampler) (h d k base : ℕ)
    (col : PayloadStrip.Columns (Stages h d)→Expr)
    (edge : Fin (PayloadStrip.edgeCount (Stages h d))) (layer : ColumnLayer k) : Expr :=
  if even : edge.val%2=0 then
    CoreLookup.field (h:=h) (d:=d) (S:=S) base (CoreLookup.fixed layer)
      (col (Strip.horizontal (PayloadStrip.edgeCount (Stages h d)) edge).left)
  else
    let t : StageAt h d := ⟨edge.val/2, by
      change edge.val/2 < Stages h d
      have bound : edge.val < 2 * Stages h d + 1 := edge.isLt
      omega⟩
    CoreLookup.field (h:=h) (d:=d) (S:=S) base (CoreLookup.tile t layer) .row

/-- Gather at the actual original signed-stratum/DFS candidate. The stage is a
public directory entry and the operand digit was installed independently of the matching. -/
def stageKey (head : PortHeader) (h d k : ℕ) :=
  BoughtSockets.select head (fun i : Key h d k=>Expr.lit (stage i).val)
def rowKey (sh : Shelf) (S : PurchaseSampler) (head : PortHeader) (h d k H : ℕ) (j : Fin (H+1)) :=
  BoughtSockets.select head (fun i : Key h d k=>BoughtSockets.readTile sh S H i j)
def digitKey (sh : Shelf) (S : PurchaseSampler) (head : PortHeader) (h d k H : ℕ) (j : Fin H) :=
  BoughtSockets.select head (fun i : Key h d k=>Expr.lookup
    (PurchaseDirectory.bank (sh.L S H i).directory (2^h) S.degree H (j.val+1)) .row)

def chainHorizontal (sh : Shelf) (S : PurchaseSampler) (h d k H base start : ℕ)
    (col : ChainStrip.Columns H→Expr) (edge : Fin (ChainStrip.edgeCount H)) (layer : ColumnLayer k) : Expr :=
  let head:=StripDirectory.stratumHeader h d k S.degree H start
  if even : edge.val%2=0 then
    let j : Fin (H+1):=⟨edge.val/2,by have small:=edge.isLt;dsimp [ChainStrip.edgeCount] at small;omega⟩
    chooseField (Stages h d) 0 (fun t=>CoreLookup.field (h:=h) (d:=d) (S:=S) base
      (CoreLookup.tile t layer) (rowKey sh S head h d k H j)) (stageKey head h d k)
  else
    let j : Fin H:=⟨edge.val/2,by have small:=edge.isLt;dsimp [ChainStrip.edgeCount] at small;omega⟩
    chooseField S.degree 0 (fun digit=>CoreLookup.field (h:=h) (d:=d) (S:=S) base (CoreLookup.sample digit layer)
      (col (Strip.horizontal (ChainStrip.edgeCount H) edge).left)) (digitKey sh S head h d k H j)

def payloadChoice (z W : ℕ) (c : PayloadStrip.Columns (Stages z (2^W))) : ColumnROM.PayloadChoice z W :=
  if c.val.val=0 then .source
  else if t : (c.val.val-1)/2<Stages z (2^W) then
    .stage ⟨(c.val.val-1)/2,t⟩ (decide (c.val.val%2=0))
  else .target

theorem payloadChoice_read (π : Equiv.Perm (Fin (2^z))) (p : Fin (2^z))
    (c : PayloadStrip.Columns (Stages z (2^W))) :
    ColumnROM.payloadValue π p (payloadChoice z W c)=payloadPlace π p c := by
  let N:=Stages z (2^W)
  have bound := c.val.isLt
  change c.val.val<2*N+1+1 at bound
  unfold payloadChoice
  split
  · rename_i zero
    have hc : c=PayloadStrip.first N 0 := Subtype.ext (Fin.ext (by change c.val.val=2*0;omega))
    exact hc ▸ (payloadPlace_input (d:=2^W) π p).symm
  · rename_i nz
    split
    · rename_i hit
      let t : StageAt z (2^W):=⟨(c.val.val-1)/2,hit⟩
      by_cases isEven : c.val.val%2=0
      · rw [decide_eq_true isEven]
        have hc : c=PayloadStrip.first N t.succ := Subtype.ext (Fin.ext (by change c.val.val=2*((c.val.val-1)/2+1);omega))
        change ColumnROM.chosenColumn π t p true=payloadPlace π p c
        rw [hc]
        exact (payloadPlace_stage_out π p t).symm
      · rw [decide_eq_false isEven]
        have hc : c=PayloadStrip.last N t.castSucc := Subtype.ext (Fin.ext (by change c.val.val=2*((c.val.val-1)/2)+1;omega))
        change ColumnROM.chosenColumn π t p false=payloadPlace π p c
        rw [hc]
        exact (payloadPlace_stage_in π p t).symm
    · rename_i noStage
      have hc : c=PayloadStrip.last N (Fin.last N) := Subtype.ext (Fin.ext (by change c.val.val=2*N+1;omega))
      exact hc ▸ (payloadPlace_output (d:=2^W) π p).symm

def payloadPorts (S : PurchaseSampler) (directory columnBase remap sites superBase oldGroups bins height z W k attempts : ℕ) :
    StripPorts S z (2^W) k (PayloadStrip.Columns (Stages z (2^W)))
      (Fin (PayloadStrip.edgeCount (Stages z (2^W)))) Empty :=
  let col:=fun c=>ColumnROM.payloadColumn columnBase remap sites superBase oldGroups bins height k attempts (payloadChoice z W c)
  ⟨directory,col,payloadHorizontal S z (2^W) k directory col,Empty.elim⟩

def chainPosition (depth : ℕ) (c : ChainStrip.Columns depth) : Fin (depth+1) :=
  ⟨c.val.val/2,by have small:=c.val.isLt;dsimp [ChainStrip.edgeCount] at small;omega⟩

def purchasePorts (catalogue : Board) (v : Directory attempts) (sh : Shelf) (S : PurchaseSampler)
    (directory columnBase keyBase oldGroups bins height z W k depth birth : ℕ) :
    StripPorts S z (2^W) k (ChainStrip.Columns depth) (Fin (ChainStrip.edgeCount depth)) Unit :=
  let stride := (v.header z (2^W) k S.degree depth).ports
  let col := fun c : ChainStrip.Columns depth=>
    v.eventPosition sh columnBase S z W k depth oldGroups bins height (chainPosition depth c) (decide (c.val.val%2=1))
  ⟨directory,col,chainHorizontal sh S z (2^W) k depth directory keyBase col,
    fun _=>catalogue.originalProbe stride birth .row⟩

/-- Direct specializations for `StripChart.Boards.payloadEdge` and `purchaseEdge`.
Charge-role filtering, original ball decoding and final guarding happen in `StripChart.edge`. -/
def payloadEdge (p : StripPorts S z (2^W) k (PayloadStrip.Columns (Stages z (2^W)))
    (Fin (PayloadStrip.edgeCount (Stages z (2^W)))) Empty) (b : Board)
    (i : Fin (Fintype.card (StripDirectory.PayloadRole (Stages z (2^W)) k))) : Expr :=
  p.primary b ((Fintype.equivFin (StripDirectory.PayloadRole (Stages z (2^W)) k)).symm i)

def purchaseEdge (p : StripPorts S z (2^W) k (ChainStrip.Columns dp) (Fin (ChainStrip.edgeCount dp)) Unit)
    (b : Board) (i : Fin (Fintype.card (StripDirectory.PurchasedRole dp k))) : Expr :=
  p.primary b ((Fintype.equivFin (StripDirectory.PurchasedRole dp k)).symm i)

theorem payload_column (S : PurchaseSampler) (catalogue columnBase remap sites superBase : ℕ)
    (groups : Fin K≃AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k attempts)) H)
    (π : Equiv.Perm (Fin (2^z))) (m : Memory w)
    (tables : ColumnROM.Tables z W k attempts columnBase remap sites superBase groups packed π m)
    (raw : Native.Resident (Native.initialOutput z) m (fun p : Fin (2^z)=>(π p).val))
    (p : Fin (2^z)) (c : PayloadStrip.Columns (Stages z (2^W))) :
    let ports:=payloadPorts S catalogue columnBase remap sites superBase K packed.groups H z W k attempts
    ((ports.column c).eval m (p.val:Word w))=(ColumnROM.number (payloadPlace π p c):Word w) := by
  apply (ColumnROM.payload_read columnBase remap sites superBase groups packed π m tables raw p (payloadChoice z W c)).trans
  rw [payloadChoice_read]

theorem chain_chosenColumn (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (marks : StageAt z (2^W)→(Fin k×Bool)→Finset (Fin (2^z))) (p : LiveChains S π depth marks)
    (c : ChainStrip.Columns depth) :
    ColumnROM.chosenColumn π p.1 (liveRow S π depth marks p (chainPosition depth c)) (decide (c.val.val%2=1)) =
      .inr (.inl (stripPlace S π depth marks p c)) := by
  let j:=chainPosition depth c
  have grp := (live_in_ball S π depth marks p j).1
  by_cases odd : c.val.val%2=1
  · have same : c=ChainStrip.outlet depth j := Subtype.ext (Fin.ext (by change c.val.val=2*(c.val.val/2)+1;omega))
    rw [decide_eq_true odd]
    change ColumnROM.chosenColumn π p.1 (liveRow S π depth marks p j) true=_
    calc
      _=.inr (.inl (stripPlace S π depth marks p (ChainStrip.outlet depth j))) := by
        rw [stripPlace_out];simp [ColumnROM.chosenColumn,outputCol,grp]
      _=_ := by rw [←same]
  · have same : c=ChainStrip.inlet depth j := Subtype.ext (Fin.ext (by change c.val.val=2*(c.val.val/2);omega))
    rw [decide_eq_false odd]
    change ColumnROM.chosenColumn π p.1 (liveRow S π depth marks p j) false=_
    calc
      _=.inr (.inl (stripPlace S π depth marks p (ChainStrip.inlet depth j))) := by
        rw [stripPlace_in];simp [ColumnROM.chosenColumn,inputCol,grp]
      _=_ := by rw [←same]

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end

end OAI
