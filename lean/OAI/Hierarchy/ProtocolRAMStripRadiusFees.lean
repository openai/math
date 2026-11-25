import OAI.Hierarchy.ProtocolRAMStripPriceCode
import OAI.Hierarchy.ProtocolRAMCalendarStripPorts

namespace OAI
/-! # The two price-bearing native radius indices of a genuine catalyst row -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CatalogueRows StripDirectory
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
variable {w z d k D : ℕ} {S : PurchaseSampler} {A B C H : Type*}

/-- Read the two core IDs selected by the actual native primary and mate
expressions. Both are charged against the same global column and axis. -/
theorem CatalogueRows.StripPorts.priced_radii [Fintype C] [Fintype H] [Fintype A] [Fintype B]
    (ports : StripPorts S z d k C H B) (board : CatalogueRows.Board) (order : Fin board.coreRows≃Edges S z d k)
    (m : Memory w) (occ ball : Word w) (global : Columns z d) (c : C) (axis : Fin k) (i : Fin D)
    (head : StockCommit.PortHeader) (ids : Fin D→Expr) (role : Expr) (raw keep : Expr)
    (mask : Fin D→Expr) (mate : Fin D→Expr) (room : board.rows<2^w) (width : D≤2^w)
    (loaded : CoreLookup.Loaded ports.directory order m)
    (atCol : ((ports.column c).eval m ball).val=((Fintype.equivFin _) global).val)
    (index : (role.eval m occ).val=i.val) (which : (head.fieldTerm.eval m occ).val=i.val)
    (atBall : head.ballTerm.eval m occ=ball)
    (direct : raw.eval m occ=(ports.primary board (.catalyst (E:=A⊕B) c axis)).eval m ball)
    (encoded : (ids i).eval m occ=(board.idBase:Word w)+(StripChart.physicalEdge board keep raw).eval m occ)
    (second : mate i=ports.mate board (.catalyst (E:=A⊕B) c axis)) (flag : mask i=.lit 1)
    (start : ℕ) :
    let L:=StockCommit.LabelSource.fromPorts start board.idBase board.geometry role ids
    let M:=chooseField D 0 mask head.fieldTerm
    let E:=board.checkedEdge (chooseField D 0 (fun j=>(mate j).atRow head.ballTerm) head.fieldTerm)
    let first:=board.coreIndex (order.symm (.inl (.inl (global,axis,false))))
    let last:=board.coreIndex (order.symm (.inl (.inl (global,axis,true))))
    L.edge.eval m occ=(first.val:Word w) ∧ M.eval m occ=1 ∧ E.eval m occ=(last.val:Word w) := by
  intro L M E first last
  obtain ⟨one,two⟩:=ports.catalyst_hops (A:=A) board order m loaded room c global axis ball atCol
  let f : Fin board.coreRows:=order.symm (.inl (.inl (global,axis,false)))
  let t : Fin board.coreRows:=order.symm (.inl (.inl (global,axis,true)))
  have fFit:f.val<2^w:=(board.coreIndex f).isLt.trans room
  have tFit:t.val<2^w:=(board.coreIndex t).isLt.trans room
  have rawAt : (raw.eval m occ).val=f.val:=(congrArg Fin.val (direct.trans one)).trans (Fin.val_cast_of_lt fFit)
  have guarded : (StripChart.physicalEdge board keep raw).eval m occ=(f.val:Word w):=by
    apply Fin.ext
    rw [physicalEdge_val board keep raw m occ room,rawAt,ite_eq_left f.isLt,Fin.val_cast_of_lt fFit]
  have physical : (ids i).eval m occ=((board.idBase+first.val:ℕ):Word w):=by
    rw [encoded,guarded,Nat.cast_add];rfl
  refine ⟨StockCommit.LabelSource.resolve_port _ _ _ _ _ m occ i first width index physical,?_,?_⟩
  · change (chooseField D 0 mask head.fieldTerm).eval m occ=1
    rw [eval_chooseField _ _ _ _ _ _ i (by simpa using width) (by simpa using which),flag]
    rfl
  · apply board.checked_core _ m occ t room
    rw [eval_chooseField _ _ _ _ _ _ i (by simpa using width) (by simpa using which),eval_atRow,atBall,second,two]
    exact Fin.val_cast_of_lt tFit

namespace StripChart
variable {z W k q depth : ℕ} (s : Boards z (2^W) k q depth) (calendar : Mesh) (board : CatalogueRows.Board)
  (G : PortBanks ((calendar.inject+calendar.cool)*calendar.outerFuel)) (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
local notation "N" => Stages z (2^W)
local notation "n₀" => Fintype.card (PayloadRole N k)
local notation "n₁" => Fintype.card (PurchasedRole depth k)
local notation "dim" => max n₀ n₁
local notation "bs" => withPorts s calendar board G

/-- The fixed payload forest and the actual direct label both select radius
records at opposite signs of the typed catalyst coordinate. -/
theorem payload_radius_ids (phase trial start : ℕ) (order : Fin board.coreRows≃Edges s.sampler z (2^W) k)
    (m : Memory w) (occ ball : Word w) (c : PayloadStrip.Columns N) (global : Columns z (2^W)) (axis : Fin k)
    (room : board.rows<2^w) (width : dim≤2^w) (loaded : CoreLookup.Loaded G.core order m)
    (atCol : (((payloadPortsAt s calendar G).column c).eval m ball).val=((Fintype.equivFin _) global).val) :
    let a : Attempt:=(.outer phase trial)
    let head:=header F bs a
    let r : PayloadRole N k:=.catalyst c axis
    let i:=PortPadding.inject (Nat.le_max_left n₀ n₁) ((Fintype.equivFin _) r)
    let L:=StockCommit.LabelSource.fromPorts start board.idBase board.geometry head.fieldTerm (id F bs board a)
    let mask:=chooseField dim 0 (catalystFlag (z:=z) (W:=W) (k:=k) (depth:=depth) a) head.fieldTerm
    let mate:=board.checkedEdge (chooseField dim 0 (fun j=>((radiusMate s calendar board G a j).atRow head.ballTerm)) head.fieldTerm)
    (head.fieldTerm.eval m occ).val=i.val → head.ballTerm.eval m occ=ball →
      L.edge.eval m occ=((order.symm (.inl (.inl (global,axis,false)))).val:Word w) ∧ mask.eval m occ=1 ∧
        mate.eval m occ=((order.symm (.inl (.inl (global,axis,true)))).val:Word w) := by
  intro a head r i L mask mate which atBall
  apply (payloadPortsAt s calendar G).priced_radii (A := PayloadStrip.Quotes N k) board order m occ ball global c axis i head (id F bs board a)
    head.fieldTerm (edge F bs board.rows a i) (retainedAt F bs a)
    (catalystFlag (z:=z) (W:=W) (k:=k) (depth:=depth) a) (radiusMate s calendar board G a)
    room width loaded atCol which which atBall _ rfl _ _ start
  · change (edge F bs board.rows (.outer phase trial) (PortPadding.inject (Nat.le_max_left n₀ n₁) ((Fintype.equivFin _) r))).eval m occ=_
    rw [payload_edge,atBall]
    change ((payloadPortsAt s calendar G).primary board ((Fintype.equivFin _).symm ((Fintype.equivFin _) r))).eval m ball=_
    rw [Equiv.symm_apply_apply]
  · simp only [a,i,radiusMate,PortPadding.extend_real,Equiv.symm_apply_apply,r]
  · simp only [a,i,catalystFlag,PortPadding.extend_real,Equiv.symm_apply_apply,r,catalystBit]

/-- The fixed purchased forest and the actual direct label both select radius
records at opposite signs of the typed catalyst coordinate. -/
theorem purchased_radius_ids (phase trial slice idx start : ℕ) (order : Fin board.coreRows≃Edges s.sampler z (2^W) k)
    (m : Memory w) (occ ball : Word w) (c : ChainStrip.Columns depth) (global : Columns z (2^W)) (axis : Fin k)
    (room : board.rows<2^w) (width : dim≤2^w) (loaded : CoreLookup.Loaded G.core order m)
    (atCol : (((boughtPortsAt s calendar board G phase trial).column c).eval m ball).val=((Fintype.equivFin _) global).val) :
    let a : Attempt:=(.inner phase trial slice idx)
    let head:=header F bs a
    let r : PurchasedRole depth k:=.catalyst c axis
    let i:=PortPadding.inject (Nat.le_max_right n₀ n₁) ((Fintype.equivFin _) r)
    let L:=StockCommit.LabelSource.fromPorts start board.idBase board.geometry head.fieldTerm (id F bs board a)
    let mask:=chooseField dim 0 (catalystFlag (z:=z) (W:=W) (k:=k) (depth:=depth) a) head.fieldTerm
    let mate:=board.checkedEdge (chooseField dim 0 (fun j=>((radiusMate s calendar board G a j).atRow head.ballTerm)) head.fieldTerm)
    (head.fieldTerm.eval m occ).val=i.val → head.ballTerm.eval m occ=ball →
      L.edge.eval m occ=((order.symm (.inl (.inl (global,axis,false)))).val:Word w) ∧ mask.eval m occ=1 ∧
        mate.eval m occ=((order.symm (.inl (.inl (global,axis,true)))).val:Word w) := by
  intro a head r i L mask mate which atBall
  apply (boughtPortsAt s calendar board G phase trial).priced_radii (A := ChainStrip.Axes depth k) board order m occ ball global c axis i head (id F bs board a)
    head.fieldTerm (edge F bs board.rows a i) (retainedAt F bs a)
    (catalystFlag (z:=z) (W:=W) (k:=k) (depth:=depth) a) (radiusMate s calendar board G a)
    room width loaded atCol which which atBall _ rfl _ _ start
  · change (edge F bs board.rows (.inner phase trial slice idx) (PortPadding.inject (Nat.le_max_right n₀ n₁) ((Fintype.equivFin _) r))).eval m occ=_
    rw [purchased_edge,atBall]
    change ((boughtPortsAt s calendar board G phase trial).primary board ((Fintype.equivFin _).symm ((Fintype.equivFin _) r))).eval m ball=_
    rw [Equiv.symm_apply_apply]
  · simp only [a,i,radiusMate,PortPadding.extend_real,Equiv.symm_apply_apply,r]
  · simp only [a,i,catalystFlag,PortPadding.extend_real,Equiv.symm_apply_apply,r,catalystBit]

end StripChart

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
