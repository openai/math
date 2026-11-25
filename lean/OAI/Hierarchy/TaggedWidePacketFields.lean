import OAI.Hierarchy.TaggedWirePacketMenuFields
import OAI.Hierarchy.TaggedWirePacketBanks
import OAI.Hierarchy.TaggedWirePacketGatheredCost

namespace OAI
/-! # Common dated ballot fields for both immutable packet menus -/
noncomputable section
namespace Hierarchy.WireTelescope.PacketTurns
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor AdaptiveProbe
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM TurnShelf Tagged
open scoped Fin.CommRing Classical
variable {S n t D M base W out B : ℕ} {len : Fin n→ℕ}
namespace Operands
variable (o : Operands len) (ord : Fin t≃Σi,Fin (len i))

/-- Every nonempty original degree shelf gets the active lower width of its
whole chord. Distinct original shelves may have the same opposite endpoint. -/
def lowAfter (here width nbr : Expr) : Expr :=
  .branch .eq width (.lit 0) (.lit 0)
    (o.aggregateWidth ord (.branch .lt here nbr here nbr) (.branch .lt here nbr nbr here))

/-- Common numeric ABI, with vacant rows above a smaller packet menu zeroed. -/
def controls (maxRoles : ℕ) (width nbr : Fin D→Expr) (here : Expr) (col : Fin ((maxRoles*3)*5+D)) : Expr :=
  if q:col.val<(maxRoles*3)*5 then
    if actual:col.val<(n*3)*5 then o.column (o.gatheredWords ord width nbr) here ⟨_,actual⟩ else .lit 0
  else o.lowAfter ord here (width ⟨col.val-(maxRoles*3)*5,by have:=col.isLt;omega⟩)
    (nbr ⟨col.val-(maxRoles*3)*5,by have:=col.isLt;omega⟩)

def appendControls (maxRoles : ℕ) («prefix» : Fin base→Expr) (width nbr : Fin D→Expr) (here : Expr) :
    Fin (base+((maxRoles*3)*5+D))→Expr := Fin.addCases «prefix» (o.controls ord maxRoles width nbr here)

theorem turn_at (enough : n≤M) (width nbr : Fin D→Expr) (here : Expr) (slot : Fin (n*3)) (field : Fin 5) :
    o.controls ord M width nbr here
      (Fin.castAdd D ((finProdFinEquiv (slot,field)).castLE (by omega)))=
      o.column (o.gatheredWords ord width nbr) here (finProdFinEquiv (slot,field)) := by
  have bound:=(finProdFinEquiv (slot,field)).isLt
  have fits : (finProdFinEquiv (slot,field)).val<(M*3)*5 := by omega
  simp only [controls,Fin.val_castAdd,Fin.val_castLE,dite_eq_left fits,dite_eq_left bound]

theorem vacant_turn (width nbr : Fin D→Expr) (here : Expr) (f : Fin ((M*3)*5))
    (absent : (n*3)*5≤f.val) :
    o.controls ord M width nbr here (f.castAdd D)=.lit 0 := by
  simp [controls,f.isLt,Nat.not_lt.mpr absent]

theorem low_at (width nbr : Fin D→Expr) (here : Expr) (q : Fin D) :
    o.controls ord M width nbr here (Fin.natAdd ((M*3)*5) q)=o.lowAfter ord here (width q) (nbr q) := by
  simp [controls]

theorem controls_fits (enough : o.Resident W out) (width nbr : Fin D→Expr) (here : Expr)
    (w : ∀q,(width q).Fits W out) (b : ∀q,(nbr q).Fits W out) (h : here.Fits W out)
    (f : Fin ((M*3)*5+D)) : (o.controls ord M width nbr here f).Fits W out := by
  unfold controls
  split
  · split
    · exact o.column_fits ord enough width nbr w b here h _
    · trivial
  · unfold lowAfter
    exact ⟨w _,trivial,trivial,o.low_fits ord enough _ _ ⟨h,b _,h,b _⟩ ⟨h,b _,b _,h⟩⟩

def controlWork (t D B : ℕ) := gatheredFieldWork t D B+PacketScan.rankWork t (5*(4*B+1)+5)+B+4

theorem controls_work (all : o.Bound B) (width nbr : Fin D→Expr) (here : Expr)
    (w : ∀q,(width q).work≤B) (b : ∀q,(nbr q).work≤B) (h : here.work≤B)
    (f : Fin ((M*3)*5+D)) : (o.controls ord M width nbr here f).work≤controlWork t D B := by
  unfold controls
  split
  · split
    · exact (o.gathered_field_work ord width nbr all w b here h _).trans (by unfold controlWork;omega)
    · simp [Expr.work,controlWork]
  · next no=>
    let q:Fin D:=⟨f.val-(M*3)*5,by have:=f.isLt;omega⟩
    have wf:=w q;have nf:=b q
    have ub:B≤4*B+1:=by omega
    have a:=o.low_work ord (B:=4*B+1)
      (show o.Bound (4*B+1) from ⟨fun i j=>(all.old i j).trans ub,fun i=>(all.width i).trans ub,
        fun i j=>(all.key i j).trans ub,fun i j l=>(all.site i j l).trans ub⟩)
      (.branch .lt here (nbr q) here (nbr q)) (.branch .lt here (nbr q) (nbr q) here)
      (by simp only [Expr.work];omega) (by simp only [Expr.work];omega)
    change (width q).work+1+1+(o.aggregateWidth ord (.branch .lt here (nbr q) here (nbr q))
      (.branch .lt here (nbr q) (nbr q) here)).work+1≤_
    unfold controlWork
    omega

theorem controlWork_le (t D B : ℕ) : controlWork t D B≤128*(t+D+1)*(B+1) := by
  unfold controlWork gatheredFieldWork gatheredWork PacketScan.rankWork PacketScan.firstWork
  ring_nf
  omega

end Operands
variable {m count K : ℕ} {s : Fin S} {total : (portGraph S).Port s→ℕ}
variable (old : Fin n→Chord S) (edge : Fin m→Chord S) (route : Fin n→List (Fin m))
    (bits : Fin n→ℕ) (ord : Fin t≃Σi,Fin (route i).length) (o : Operands (fun i=>(route i).length))
    (mem : Memory W) (row : Word W) (read : Reads old edge route bits o mem row) (sites : S≤2^W)
    (parts : PassiveWindow.Parts ((portGraph S).Port s) (Fin D) K total) (width nbr : Fin D→Expr)
    (mounted : NeighborReads mem row parts width nbr) (here : Expr) (atSite : here.eval mem row=(s.val:Word W))

private theorem sorted_ends (p : (portGraph S).Port s) :
    (if s.val<(PacketNeighbor.other p).val then s else PacketNeighbor.other p)=p.val.1.val.1 ∧
    (if s.val<(PacketNeighbor.other p).val then PacketNeighbor.other p else s)=p.val.1.val.2 := by
  rcases p with ⟨⟨⟨⟨a,b⟩,ab⟩,side⟩,inc⟩
  have asc : a.val<b.val := ab
  cases side <;> simp only [portGraph,PortGraph.vertex] at inc <;> subst s <;>
    simp [PacketNeighbor.other, portGraph, PortGraph.vertex, asc, not_lt_of_ge asc.le]

include read sites mounted atSite

theorem lowAfter_read (q : Fin D) :
    (o.lowAfter ord here (width q) (nbr q)).eval mem row=
      ((parts.owner q).elim 0 (fun p=>if 0<parts.width q then installedWidths edge (routeLoad route bits) p.val.1 else 0) : Word W) := by
  rw [Operands.lowAfter,PacketScan.eq_select mem row _ _ _ _ (mounted.widthAt q) rfl (mounted.fits q) (Nat.two_pow_pos W)]
  cases owner:parts.owner q with
  | none=>simp [PacketNeighbor.amount,owner,Expr.eval]
  | some p=>
    dsimp only [Option.elim_some]
    by_cases blank:parts.width q=0
    · simp [PacketNeighbor.amount,owner,blank,Expr.eval]
    · have use:=Nat.pos_of_ne_zero blank
      simp only [PacketNeighbor.amount,owner,Option.elim_some,ite_eq_right blank,ite_eq_left use]
      have nh:=mounted.siteAt q p owner use
      have ends := sorted_ends p
      have cmp (yes no : Expr):=
        lt_select mem row here (nbr q) yes no atSite nh (s.isLt.trans_le sites)
          ((PacketNeighbor.other p).isLt.trans_le sites)
      let word := fun u : Fin S=>(u.val : Word W)
      apply width_eval old edge route bits ord o mem row read sites _ _ p.val.1
      · rw [cmp]
        by_cases asc : s.val<(PacketNeighbor.other p).val
        · rw [ite_eq_left asc]
          exact atSite.trans (congrArg word (by simpa only [ite_eq_left asc] using ends.1))
        · rw [ite_eq_right asc]
          exact nh.trans (congrArg word (by simpa only [ite_eq_right asc] using ends.1))
      · rw [cmp]
        by_cases asc : s.val<(PacketNeighbor.other p).val
        · rw [ite_eq_left asc]
          exact nh.trans (congrArg word (by simpa only [ite_eq_left asc] using ends.2))
        · rw [ite_eq_right asc]
          exact atSite.trans (congrArg word (by simpa only [ite_eq_right asc] using ends.2))

theorem active_turn_read (room : m≤2^W) (enough : n≤M)
    (short : ∀i,(route i).length≤2) (turns : Fin count≃Positions route) (wide : ∀i,bits i<2^W)
    (slot : Fin (n*3)) (f : Fin 5) :
    let prior:=fun (i : Fin n) (b : Bool)=>(ChosenPackets.RowRouting.halfCode i b).val
    let post:=fun (e : Fin m) (b : Bool)=>n*2+PacketNeighbor.index parts ((rowGraph edge).vertex e (!b))
    let shift:=AggregatePrefix.paidShift route bits ord edge
    (o.controls ord M width nbr here (Fin.castAdd D ((finProdFinEquiv (slot,f)).castLE (by omega)))).eval mem row=
      ProtocolRAMTurnShelf.entry (shiftedFields old edge route bits ord shift prior post short turns)
        (put old edge route bits ord prior post short turns) f (s,slot) := by
  rw [Operands.turn_at o ord enough]
  exact gathered_column old edge route bits ord o mem row read sites room parts width nbr mounted
    short turns here atSite wide slot f

theorem active_low_read (q : Fin D) :
    (o.controls ord M width nbr here (Fin.natAdd ((M*3)*5) q)).eval mem row=
      ((parts.owner q).elim 0 (fun p=>if 0<parts.width q then installedWidths edge (routeLoad route bits) p.val.1 else 0) : Word W) := by
  rw [Operands.low_at]
  exact lowAfter_read old edge route bits ord o mem row read sites parts width nbr mounted here atSite q

end Hierarchy.WireTelescope.PacketTurns

end
end OAI
