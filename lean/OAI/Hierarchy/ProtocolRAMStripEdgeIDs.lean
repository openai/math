import OAI.Hierarchy.ProtocolRAMStripColumnPrograms
import OAI.Hierarchy.ProtocolRAMCoreEdgeLookup
import OAI.Hierarchy.ProtocolRAMCatalogueEdgeID
import OAI.Hierarchy.ProbeStripDirectory
import OAI.Hierarchy.ProbeColumnAccounts

namespace OAI
/-! # Resolving a typed replacement port to its physical edge or two-hop catalyst -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
variable {h d k z W R : ℕ} {S : PurchaseSampler} {C H A B : Type*}


theorem Board.coreOnly_true (b : Board) (e : Expr) (m : Memory W) (r : Word W) (i : Fin b.coreRows)
    (room : b.rows<2^W) (read : (e.eval m r).val=i.val) : (b.coreOnly e).eval m r=e.eval m r := by
  have fit : b.coreRows<2^W := by unfold rows at room;omega
  simp only [coreOnly,Expr.eval,Comparison.test,Fin.lt_def,decide_eq_true_eq,Fin.val_cast_of_lt fit,read,i.isLt,ite_true]

theorem Board.coreOnly_read (b : Board) (e : Expr) (m : Memory W) (r : Word W) (i : Fin b.coreRows)
    (room : b.rows<2^W) (read : e.eval m r=(i.val:Word W)) : (b.coreOnly e).eval m r=(i.val:Word W) := by
  have bound : i.val<2^W := by have := i.isLt;unfold rows at room;omega
  exact (b.coreOnly_true e m r i room (by rw [read,Fin.val_cast_of_lt bound])).trans read

/-- Only catalyst replacements need a second hop. -/
def StripPorts.mate (p : StripPorts S h d k C H B) (b : Board) : ColumnWires.Role C H (A⊕B) k→Expr
  | .catalyst c axis => b.coreOnly (p.radiusAt c axis true)
  | _ => .lit b.rows

def catalystBit : ColumnWires.Role C H (A⊕B) k→ℕ
  | .catalyst .. => 1
  | _ => 0

variable [Fintype C] [Fintype H] [Fintype A] [Fintype B]
local notation "Port" => ColumnWires.Role C H (A⊕B) k

/-- The native occurrence header and the histogram table use this identical
enumeration of roles. The ID receives the true original ball register, not the
flattened occurrence ordinal. -/
def StripPorts.ids (p : StripPorts S h d k C H B) (b : Board) (head : StockCommit.PortHeader)
    (j : Fin (Fintype.card Port)) : Expr :=
  (p.primary b ((Fintype.equivFin Port).symm j)).atRow head.ballTerm

def StripPorts.catalystMate (p : StripPorts S h d k C H B) (b : Board) (head : StockCommit.PortHeader) : Expr×Expr :=
  (chooseField (Fintype.card Port) 0 (fun j=>.lit (catalystBit ((Fintype.equivFin Port).symm j))) head.fieldTerm,
   chooseField (Fintype.card Port) 0 (fun j=>(p.mate b ((Fintype.equivFin Port).symm j)).atRow head.ballTerm) head.fieldTerm)

theorem StripPorts.ids_read (p : StripPorts S h d k C H B) (b : Board) (head : StockCommit.PortHeader)
    (m : Memory W) (r ball : Word W) (role : Port) (read : head.ballTerm.eval m r=ball) :
    (p.ids b head (Fintype.equivFin _ role)).eval m r=(p.primary b role).eval m ball := by
  simp [ids,eval_atRow,read]

theorem StripPorts.mate_read (p : StripPorts S h d k C H B) (b : Board) (head : StockCommit.PortHeader)
    (m : Memory W) (r ball : Word W) (role : Port) (room : Fintype.card Port≤2^W)
    (ballAt : head.ballTerm.eval m r=ball) (roleAt : (head.fieldTerm.eval m r).val=((Fintype.equivFin _) role).val) :
    (p.catalystMate (A:=A) b head).1.eval m r=(catalystBit role:Word W) ∧
    (p.catalystMate (A:=A) b head).2.eval m r=(p.mate b role).eval m ball := by
  let j:=Fintype.equivFin _ role
  have select (terms : Fin (Fintype.card Port)→Expr) :
      (chooseField _ 0 terms head.fieldTerm).eval m r=(terms j).eval m r :=
    eval_chooseField _ 0 terms _ m r j (by simpa using room) (by simpa [j] using roleAt)
  constructor <;> simp only [catalystMate,select,eval_atRow,ballAt,j,Equiv.symm_apply_apply,Expr.eval]

omit [Fintype C] [Fintype H] [Fintype A] [Fintype B] in
/-- Both bits of the physical realization of a catalyst are placed at its
actual column, one on each opposite radius of that same coordinate. -/
theorem StripPorts.catalyst_hops (p : StripPorts S h d k C H B) (board : Board)
    (order : Fin board.coreRows ≃ Edges S h d k) (m : Memory W) (loaded : CoreLookup.Loaded p.directory order m) (room : board.rows<2^W)
    (c : C) (global : Columns h d) (axis : Fin k) (r : Word W)
    (column : ((p.column c).eval m r).val=((Fintype.equivFin _) global).val) :
    let role : Port:=.catalyst c axis
    (p.primary board role).eval m r=((order.symm (.inl (.inl (global,axis,false)))).val:Word W) ∧
    (p.mate board role).eval m r=((order.symm (.inl (.inl (global,axis,true)))).val:Word W) := by
  intro role
  let j : Fin (CoreLookup.positions h d) := ⟨((Fintype.equivFin _) global).val,
    ((Fintype.equivFin _) global).isLt.trans_le (Nat.le_max_left _ _)⟩
  have hop (side : Bool) :
      (p.radiusAt c axis side).eval m r=((order.symm (.inl (.inl (global,axis,side)))).val:Word W) :=
    loaded.read _ (p.column c) r j column _ (CoreLookup.resolve_radius global axis side)
  have first (side : Bool) : (board.coreOnly (p.radiusAt c axis side)).eval m r=
      ((order.symm (.inl (.inl (global,axis,side)))).val:Word W) := by
    let i:=order.symm (.inl (.inl (global,axis,side)))
    have bounded : i.val<2^W := by have hi:=i.isLt;unfold Board.rows at room;omega
    exact (board.coreOnly_true _ m r i room (by rw [hop];exact Fin.val_cast_of_lt bounded)).trans (hop side)
  exact ⟨first false,first true⟩

omit [Fintype C] [Fintype H] [Fintype A] [Fintype B] in
theorem StripPorts.radius_read (p : StripPorts S h d k C H B) (board : Board)
    (order : Fin board.coreRows≃Edges S h d k) (m : Memory W) (loaded : CoreLookup.Loaded p.directory order m)
    (c : C) (global : Columns h d) (axis : Fin k) (side : Bool) (r : Word W) (room : board.rows<2^W)
    (column : ((p.column c).eval m r).val=((Fintype.equivFin _) global).val) :
    (p.primary board (.radius (E:=A⊕B) c axis side)).eval m r=
      ((order.symm (.inl (.inl (global,axis,side)))).val:Word W) := by
  let key : Fin (CoreLookup.positions h d) := ⟨_,((Fintype.equivFin _) global).isLt.trans_le (Nat.le_max_left _ _)⟩
  exact board.coreOnly_read _ m r _ room
    (loaded.read _ (p.column c) r key column _ (CoreLookup.resolve_radius global axis side))

omit [Fintype C] [Fintype H] [Fintype A] [Fintype B] in
theorem StripPorts.cross_read (p : StripPorts S h d k C H B) (board : Board)
    (order : Fin board.coreRows≃Edges S h d k) (m : Memory W) (loaded : CoreLookup.Loaded p.directory order m)
    (c : C) (global : Columns h d) (axes : {ab : Fin k×Fin k // ab.1≠ab.2}) (s t : Bool) (r : Word W) (room : board.rows<2^W)
    (column : ((p.column c).eval m r).val=((Fintype.equivFin _) global).val) :
    (p.primary board (.cross (E:=A⊕B) c axes s t)).eval m r=
      ((order.symm (.inl (.inr (.inl (global,crossDatum axes s t))))).val:Word W) := by
  let key : Fin (CoreLookup.positions h d) := ⟨_,((Fintype.equivFin _) global).isLt.trans_le (Nat.le_max_left _ _)⟩
  let x:=crossDatum axes s t
  exact board.coreOnly_read _ m r _ room
    (loaded.read _ (p.column c) r key column _ (CoreLookup.resolve_cross global x.1 x.2.1 x.2.2))

theorem cross_edges (c : Columns h d) (axes : {ab : Fin k×Fin k // ab.1≠ab.2}) (s t : Bool) :
    let endSites:=freeEnds (S:=S) (.inr (.inl (c,crossDatum axes s t)))
    (endSites=((c,some (axes.val.1,s)),(c,some (axes.val.2,t)))) ∨
      (endSites=((c,some (axes.val.2,t)),(c,some (axes.val.1,s)))) := by
  unfold crossDatum;split <;> first | exact .inl rfl | exact .inr rfl

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
