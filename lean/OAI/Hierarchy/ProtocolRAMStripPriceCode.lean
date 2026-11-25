import OAI.Hierarchy.ProtocolRAMStripEdgeSupport
import OAI.Hierarchy.ProtocolRAMReportedChargeKeys
import OAI.Hierarchy.ProbeCoreCode

namespace OAI
/-! # The link label written by a native strip and the price of its two catalyst radii -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe StockCommit
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
variable {C H A B : Type*} {S : PurchaseSampler} {z d k w q D : ℕ}

/-- The fifth-indexed native length field is constant on the entire suffix of
the catalogue after its core, including dormant candidates and the dummy row. -/
theorem Board.unit_metric (b : Board) (m : Memory w) (j : Word w) (fit : b.rows<2^w)
    (suffix : b.coreRows≤ j.val) : (b.geometry 5).eval m j=1 := by
  have small:b.coreRows<2^w:=by unfold rows at fit;omega
  change (b.select b.core.lengthCode (.lit 1)).eval m j=1
  simp [select,Expr.eval,Comparison.test,Fin.lt_def,Fin.val_cast_of_lt small,not_lt.mpr suffix,eval_atRow]

/-- Reading the actual acquisition flag can replace an unretained candidate by
the dummy row. Their encoded ordinary length is identical. -/
theorem Board.guard_metric (b : Board) (keep raw : Expr) (m : Memory w) (r : Word w)
    (room : b.rows<2^w) :
    (b.geometry 5).eval m ((StripChart.physicalEdge b keep raw).eval m r)=
      (b.geometry 5).eval m (raw.eval m r) := by
  have guard:=physicalEdge_val b keep raw m r room
  by_cases old:(raw.eval m r).val< b.coreRows
  · rw [ite_eq_left old] at guard
    exact congrArg (fun i : Word w => (b.geometry 5).eval m i) (Fin.ext guard)
  · rw [b.unit_metric m _ room (le_of_not_gt old)]
    apply b.unit_metric m _ room
    rw [guard,ite_eq_right old]
    have core:b.coreRows≤ b.rows:=Nat.le_add_right _ _
    split_ifs <;> omega

/-- Any actual loaded core price word can be extracted directly from the fifth
column. In particular it can be supplied by `CoreCatalogue.Rows`. -/
theorem Board.core_metric (b : Board) (m : Memory w) (i : Fin b.coreRows) (room : b.rows<2^w) :
    (b.geometry 5).eval m (i.val:Word w)=b.core.lengthCode.eval m (i.val:Word w) :=
  b.select_core m _ _ i room

/-- A genuine physical occurrence resolves the public compile-time term after
reading its true role ordinal. The exact stored, unsigned RAM word has the
same geometric price as its raw role edge. -/
theorem Board.price_word (b : Board) (a : Area) (s : Sources) (B₀ : Batch q D) (m : Memory w)
    (out : ℕ) (role : Expr) (ids : Fin D→Expr) (i : Fin a.occurrences) (j : Fin D)
    (keep raw : Expr) (room : b.rows<2^w) (Droom : D≤2^w)
    (which : (role.eval m (i.val:Word w)).val=j.val)
    (id : (ids j).eval m (i.val:Word w)=(b.idBase:Word w)+
      (StripChart.physicalEdge b keep raw).eval m (i.val:Word w))
    (ready : (pricedSegment a s (LabelSource.fromPorts out b.idBase b.geometry role ids) w B₀).ready m)
    (before : out+a.occurrences≤ a.start) :
    (pricedSegment a s (LabelSource.fromPorts out b.idBase b.geometry role ids) w B₀).after m (out+i.val)=
      (b.geometry 5).eval m (raw.eval m (i.val:Word w)) := by
  let g:=LabelSource.fromPorts out b.idBase b.geometry role ids
  have lookup : g.edge.eval m (i.val:Word w)=(StripChart.physicalEdge b keep raw).eval m (i.val:Word w) := by
    change (chooseField D 0 ids role).eval m (i.val:Word w)-(b.idBase:Word w)=_
    rw [eval_chooseField _ _ _ _ _ _ j (by simpa using Droom) (by simpa using which),id]
    abel
  exact (price_label a s g B₀ m i ready before).trans ((congrArg ((b.geometry 5).eval m) lookup).trans
    (b.guard_metric keep raw m _ room))

/-- The physical code of a true resolved original, taken on its own source
bank. The radius, diagonal and horizontal cases select fixed core records,
and the acquired candidate is an ordinary unit-length edge. -/
theorem StripPorts.printed_metric (p : StripPorts S z d k C H B) (b : Board)
    (order : Fin b.coreRows≃Edges S z d k) (M : ℕ) (len : H→ℝ) (m : Memory w) (r : Word w)
    (loaded : CoreLookup.Loaded p.directory order m) (room : b.rows<2^w) (wide : 0< w)
    (codes : ∀f,b.core.lengthCode.eval m ((order.symm f).val:Word w)=(coreCode S M f:Word w))
    (fit : ∀f : Edges S z d k,coreCode S M f<2^w)
    (global : C → Columns z d) (columns : ∀c,((p.column c).eval m r).val=((Fintype.equivFin _) (global c)).val)
    (horiz : ∀e l,∃ f : Edges S z d k,(p.horizontal e l).eval m r=((order.symm f).val:Word w) ∧
      (coreCode S M f:ℝ)=len e)
    (birth : ∀u,b.coreRows≤((p.probe u).eval m r).val)
    (role : ColumnWires.Role C H (A⊕B) k) (cash : ColumnWires.account _root_.id role=none) :
    externalPrice (decide (catalystBit role=1)) M 1
      ((b.geometry 5).eval m ((p.primary b role).eval m r)).val=ColumnWires.printed M len role := by
  have core (f : Edges S z d k) :
      ((b.geometry 5).eval m ((order.symm f).val:Word w)).val=coreCode S M f :=
    congrArg Fin.val (b.core_metric m (order.symm f) room) |>.trans
      ((congrArg Fin.val (codes f)).trans (Fin.val_cast_of_lt (fit f)))
  cases role with
  | catalyst c axis => simp [externalPrice,catalystBit,ColumnWires.printed,ColumnWires.quote]
  | radius c axis side =>
    let key : Fin (CoreLookup.positions z d) :=
      ⟨_, ((Fintype.equivFin _) (global c)).isLt.trans_le (Nat.le_max_left _ _)⟩
    have hop : (p.primary b (.radius (E:=A⊕B) c axis side)).eval m r =
        ((order.symm (.inl (.inl (global c,axis,side)))).val : Word w) :=
      b.coreOnly_read _ m r _ room
        (loaded.read _ (p.column c) r key (columns c) _ (CoreLookup.resolve_radius (global c) axis side))
    rw [hop,core]
    simp [externalPrice,catalystBit,lengthPrice,ColumnWires.printed,ColumnWires.quote,coreCode]
  | cross c axes s t =>
    let key : Fin (CoreLookup.positions z d) :=
      ⟨_, ((Fintype.equivFin _) (global c)).isLt.trans_le (Nat.le_max_left _ _)⟩
    let x := crossDatum axes s t
    have hop : (p.primary b (.cross (E:=A⊕B) c axes s t)).eval m r =
        ((order.symm (.inl (.inr (.inl (global c,x))))).val : Word w) :=
      b.coreOnly_read _ m r _ room
        (loaded.read _ (p.column c) r key (columns c) _ (CoreLookup.resolve_cross (global c) x.1 x.2.1 x.2.2))
    rw [hop,core]
    simpa [externalPrice,catalystBit,lengthPrice,ColumnWires.printed,ColumnWires.quote,coreCode] using
      (natCast_ceil_eq_intCast_ceil (show 0≤ Real.sqrt 2*(M:ℝ) by positivity))
  | horizontal e l =>
    obtain ⟨f,selected,price⟩:=horiz e l
    have actual:=b.coreOnly_read (p.horizontal e l) m r (order.symm f) room selected
    change externalPrice false M 1 ((b.geometry 5).eval m ((b.coreOnly (p.horizontal e l)).eval m r)).val=len e
    rw [actual,core]
    simpa [externalPrice,lengthPrice] using price
  | extra x =>
    cases x with
    | inl v => contradiction
    | inr u =>
      change externalPrice false M 1 ((b.geometry 5).eval m ((p.probe u).eval m r)).val=1
      rw [b.unit_metric m _ room (birth u)]
      simp [externalPrice,lengthPrice,wide]

/-- Both positive catalyst hops read their own real length-M original radius.
The signed histogram quote therefore pays for their total geometric length. -/
theorem StripPorts.catalyst_toll [Fintype C] [Fintype H] [Fintype A] [Fintype B]
    (p : StripPorts S z d k C H B) (b : Board) (order : Fin b.coreRows≃Edges S z d k)
    (m : Memory w) (r : Word w) (M : ℕ) (room : b.rows<2^w) (fit : M<2^w)
    (loaded : CoreLookup.Loaded p.directory order m) (c : C) (global : Columns z d) (axis : Fin k)
    (column : ((p.column c).eval m r).val=((Fintype.equivFin _) global).val)
    (codes : ∀side : Bool,b.core.lengthCode.eval m ((order.symm (.inl (.inl (global,axis,side)))).val:Word w)=(M:Word w)) :
    let e : ColumnWires.Role C H (A⊕B) k:=.catalyst c axis
    ((b.geometry 5).eval m ((p.primary b e).eval m r)).val=M ∧
      ((b.geometry 5).eval m ((p.mate b e).eval m r)).val=M := by
  intro e
  obtain ⟨first,second⟩:=p.catalyst_hops (A:=A) b order m loaded room c global axis r column
  have metric (side : Bool) :
      ((b.geometry 5).eval m ((order.symm (.inl (.inl (global,axis,side)))).val:Word w)).val=M :=
    (congrArg Fin.val ((b.core_metric m _ room).trans (codes side))).trans (Fin.val_cast_of_lt fit)
  rw [first,second]
  exact ⟨metric false,metric true⟩

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
