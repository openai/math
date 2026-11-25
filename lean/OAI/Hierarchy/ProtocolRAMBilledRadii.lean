import OAI.Hierarchy.ProtocolRAMCorePadded
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

/-- Every physical hit at a signed radius is an original core ordinal or the
disposable slot. This includes padded source columns. -/
def CatalogueRows.Board.RadiusAddress (b : Board) (order : Fin b.coreRows≃Edges S z d k)
    (axis : Fin k) (side : Bool) (n : ℕ) : Prop :=
  (∃c : Columns z d,n=(order.symm (.inl (.inl (c,axis,side)))).val) ∨ n=b.rows

theorem CatalogueRows.StripPorts.radius_address (ports : StripPorts S z d k C H B) (b : Board)
    (order : Fin b.coreRows≃Edges S z d k) (m : Memory w) (r : Word w) (c : C) (axis : Fin k) (side : Bool)
    (rom : CoreLookup.Padded ports.directory order m) (fit : b.rows<2^w) :
    b.RadiusAddress order axis side ((b.coreOnly (ports.radiusAt c axis side)).eval m r).val := by
  let x:=ports.radiusAt c axis side
  have core : b.coreRows<2^w := (Nat.le_add_right ..).trans_lt fit
  rcases rom.radius_cases axis side (ports.column c) r with ⟨col,h⟩|off
  · let e:=order.symm (.inl (.inl (col,axis,side)))
    have value:(x.eval m r).val=e.val:=(congrArg Fin.val h).trans (Fin.val_cast_of_lt (e.isLt.trans core))
    exact Or.inl ⟨col,(congrArg Fin.val (b.coreOnly_true x m r e fit value)).trans value⟩
  · right
    change (x.eval m r)=(b.coreRows:Word w) at off
    change ((b.coreOnly x).eval m r).val=b.rows
    simp only [Board.coreOnly,Expr.eval,Comparison.test,decide_eq_true_eq,off,lt_self_iff_false,
      ite_false,Fin.val_cast_of_lt fit]

private theorem CatalogueRows.Board.radius_guard (b : Board) (order : Fin b.coreRows≃Edges S z d k)
    (axis : Fin k) (side : Bool) (m : Memory w) (r : Word w) (raw keep : Expr) (room : b.rows<2^w)
    (hit : b.RadiusAddress order axis side (raw.eval m r).val) :
    ((StripChart.physicalEdge b keep raw).eval m r).val=(raw.eval m r).val ∧
    ((b.checkedEdge raw).eval m r).val=(raw.eval m r).val := by
  rw [physicalEdge_val b keep raw m r room,b.checkedEdge_val raw m r room]
  rcases hit with ⟨col,h⟩|off
  · have core : (raw.eval m r).val < b.coreRows := by
      rw [h]
      exact (order.symm _).isLt
    exact ⟨ite_eq_left core, ite_eq_left core⟩
  · have core : b.coreRows≤b.rows:=Nat.le_add_right ..
    simp [off, Nat.not_lt.mpr core]

theorem CatalogueRows.StripPorts.billed_radii (ports : StripPorts S z d k C H B)
    (board : Board) (order : Fin board.coreRows≃Edges S z d k)
    (m : Memory w) (occ ball : Word w) (c : C) (axis : Fin k) (i : Fin D)
    (head : StockCommit.PortHeader) (ids : Fin D→Expr) (role : Expr) (raw keep : Expr)
    (mate : Fin D→Expr) (room : board.rows<2^w) (width : D≤2^w)
    (loaded : CoreLookup.Padded ports.directory order m)
    (index : (role.eval m occ).val=i.val) (which : (head.fieldTerm.eval m occ).val=i.val)
    (atBall : head.ballTerm.eval m occ=ball)
    (direct : raw.eval m occ=(ports.primary board (.catalyst (E:=A⊕B) c axis)).eval m ball)
    (encoded : (ids i).eval m occ=(board.idBase:Word w)+(StripChart.physicalEdge board keep raw).eval m occ)
    (second : mate i=ports.mate board (.catalyst (E:=A⊕B) c axis)) (start : ℕ) :
    let L:=StockCommit.LabelSource.fromPorts start board.idBase board.geometry role ids
    let E:=board.checkedEdge (chooseField D 0 (fun j=>(mate j).atRow head.ballTerm) head.fieldTerm)
    board.RadiusAddress order axis false (L.edge.eval m occ).val ∧
      board.RadiusAddress order axis true (E.eval m occ).val := by
  intro L E
  have one : board.RadiusAddress order axis false (raw.eval m occ).val := by
    rw [direct];exact ports.radius_address board order m ball c axis false loaded room
  let exp:=chooseField D 0 (fun j=>(mate j).atRow head.ballTerm) head.fieldTerm
  have two : board.RadiusAddress order axis true (exp.eval m occ).val := by
    unfold exp
    rw [eval_chooseField _ _ _ _ _ _ i (by simpa using width) (by simpa using which),eval_atRow,atBall,second]
    exact ports.radius_address board order m ball c axis true loaded room
  have eqn : L.edge.eval m occ=(StripChart.physicalEdge board keep raw).eval m occ := by
    change (chooseField D 0 ids role).eval m occ-(board.idBase:Word w)=_
    rw [eval_chooseField _ _ _ _ _ _ i (by simpa using width) (by simpa using index),encoded]
    abel
  rw [eqn,(board.radius_guard order axis false m occ raw keep room one).1]
  exact ⟨one,(board.radius_guard order axis true m occ exp keep room two).2.symm ▸ two⟩

namespace StripChart
set_option maxHeartbeats 1000000
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
theorem payload_billed_radii (phase trial start : ℕ) (order : Fin board.coreRows≃Edges s.sampler z (2^W) k)
    (m : Memory w) (occ ball : Word w) (c : PayloadStrip.Columns N) (axis : Fin k)
    (room : board.rows<2^w) (width : dim≤2^w) (loaded : CoreLookup.Padded G.core order m) :
    let a : Attempt:=(.outer phase trial)
    let head:=header F bs a
    let r : PayloadRole N k:=.catalyst c axis
    let i:=PortPadding.inject (Nat.le_max_left n₀ n₁) ((Fintype.equivFin _) r)
    let L:=StockCommit.LabelSource.fromPorts start board.idBase board.geometry head.fieldTerm (id F bs board a)
    let mate:=board.checkedEdge (chooseField dim 0 (fun j=>((radiusMate s calendar board G a j).atRow head.ballTerm)) head.fieldTerm)
    (head.fieldTerm.eval m occ).val=i.val → head.ballTerm.eval m occ=ball →
      board.RadiusAddress order axis false (L.edge.eval m occ).val ∧
        board.RadiusAddress order axis true (mate.eval m occ).val := by
  intro a head r i L mate which atBall
  apply (payloadPortsAt s calendar G).billed_radii (A := PayloadStrip.Quotes N k) board order m occ ball c axis i head (id F bs board a)
    head.fieldTerm (edge F bs board.rows a i) (retainedAt F bs a)
    (radiusMate s calendar board G a)
    room width loaded which which atBall _ rfl _ start
  · change (edge F bs board.rows (.outer phase trial) (PortPadding.inject (Nat.le_max_left n₀ n₁) ((Fintype.equivFin _) r))).eval m occ=_
    rw [payload_edge,atBall]
    change ((payloadPortsAt s calendar G).primary board ((Fintype.equivFin _).symm ((Fintype.equivFin _) r))).eval m ball=_
    rw [Equiv.symm_apply_apply]
  · simp only [a,i,radiusMate,PortPadding.extend_real,Equiv.symm_apply_apply,r]

/-- The fixed purchased forest and the actual direct label both select radius
records at opposite signs of the typed catalyst coordinate. -/
theorem purchased_billed_radii (phase trial slice idx start : ℕ) (order : Fin board.coreRows≃Edges s.sampler z (2^W) k)
    (m : Memory w) (occ ball : Word w) (c : ChainStrip.Columns depth) (axis : Fin k)
    (room : board.rows<2^w) (width : dim≤2^w) (loaded : CoreLookup.Padded G.core order m) :
    let a : Attempt:=(.inner phase trial slice idx)
    let head:=header F bs a
    let r : PurchasedRole depth k:=.catalyst c axis
    let i:=PortPadding.inject (Nat.le_max_right n₀ n₁) ((Fintype.equivFin _) r)
    let L:=StockCommit.LabelSource.fromPorts start board.idBase board.geometry head.fieldTerm (id F bs board a)
    let mate:=board.checkedEdge (chooseField dim 0 (fun j=>((radiusMate s calendar board G a j).atRow head.ballTerm)) head.fieldTerm)
    (head.fieldTerm.eval m occ).val=i.val → head.ballTerm.eval m occ=ball →
      board.RadiusAddress order axis false (L.edge.eval m occ).val ∧
        board.RadiusAddress order axis true (mate.eval m occ).val := by
  intro a head r i L mate which atBall
  apply (boughtPortsAt s calendar board G phase trial).billed_radii (A := ChainStrip.Axes depth k) board order m occ ball c axis i head (id F bs board a)
    head.fieldTerm (edge F bs board.rows a i) (retainedAt F bs a)
    (radiusMate s calendar board G a)
    room width loaded which which atBall _ rfl _ start
  · change (edge F bs board.rows (.inner phase trial slice idx) (PortPadding.inject (Nat.le_max_right n₀ n₁) ((Fintype.equivFin _) r))).eval m occ=_
    rw [purchased_edge,atBall]
    change ((boughtPortsAt s calendar board G phase trial).primary board ((Fintype.equivFin _).symm ((Fintype.equivFin _) r))).eval m ball=_
    rw [Equiv.symm_apply_apply]
  · simp only [a,i,radiusMate,PortPadding.extend_real,Equiv.symm_apply_apply,r]

end StripChart
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
