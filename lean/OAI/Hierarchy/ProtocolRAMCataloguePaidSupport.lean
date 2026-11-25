import OAI.Hierarchy.ProtocolRAMCatalogueEdgeID
import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices

namespace OAI
/-! # Positive installed widths refer to a committed original acquisition -/

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM
open scoped Fin.CommRing BigOperators
noncomputable section
variable {W z d k goods q r : ℕ}

def Board.guardWalk (b : Board) (t : Traversals) : Traversals :=
  {t with edge:=b.checkedEdge t.edge, catalystMate:=t.catalystMate.map (fun m=>(m.1,b.checkedEdge m.2))}

/-- Each parent-committed candidate is a permanently named edge of the physical
graph. The disposable scatter position lies outside this set. -/
def Board.Supported (b : Board) (s : PaidWidths.Slice) (m : Memory W) : Prop :=
  ∀ (i : Fin s.count) (j : Fin b.boughtRows), (s.edge.eval m (i.val:Word W)).val=(b.boughtIndex j).val →
    b.bought.flag.eval m (j.val:Word W)≠0

theorem Board.selected_common (b : Board) (role : Expr) (edge : Fin goods→Expr)
    (m : Memory W) (r : Word W) (j : Fin b.boughtRows) (room : b.idBase+b.rows<2^W)
    (ports : goods≤2^W) (positiveCore : 0<b.coreRows)
    (hit : (((chooseField goods 0 (fun i=>b.commonID (edge i)) role).eval m r-(b.idBase:Word W))).val=(b.boughtIndex j).val) :
    b.bought.flag.eval m (j.val:Word W)≠0 := by
  have last := (b.boughtIndex j).isLt
  by_cases inside : (role.eval m r).val<goods
  · let f : Fin goods := ⟨_,inside⟩
    have pick := eval_chooseField goods 0 (fun i=>b.commonID (edge i)) role m r f (by simpa using ports) (by simp [f])
    rw [pick,b.commonID_sub] at hit
    exact b.checked_hit _ m r j (by omega) hit
  · have none := eval_chooseField_outside goods 0 (fun i=>b.commonID (edge i)) role m r
      (by simpa using ports) (by simpa using Nat.le_of_not_gt inside)
    rw [none] at hit
    have wrapped : (0:Word W)-(b.idBase:Word W)=((b.boughtIndex j).val:Word W) :=
      Fin.ext (hit.trans (Fin.val_cast_of_lt (show (b.boughtIndex j).val<2^W by omega)).symm)
    have add := congrArg (fun t : Word W=> (b.idBase:Word W)+t) wrapped
    have hzero : (0:Word W)=((b.idBase+(b.boughtIndex j).val:ℕ):Word W) := by
      rw [Nat.cast_add,←add];abel
    have zero := congrArg Fin.val hzero
    rw [Fin.val_cast_of_lt (show b.idBase+(b.boughtIndex j).val<2^W by omega)] at zero
    change 0=b.idBase+(b.coreRows+j.val) at zero
    omega

theorem Board.walk_supported (b : Board) (s : PaidWidths.Slice) (t : Traversals) (m : Memory W)
    (room : b.rows<2^W) (edge : s.edge=(b.guardWalk t).edge) : b.Supported s m := by
  intro i j same
  rw [edge] at same
  exact b.checked_hit t.edge m (i.val:Word W) j room same

theorem Board.attempt_supported (b : Board) (p : Format z d k q goods) (sink : Sink r b.rows)
    (role : Expr) (ids : Fin goods→Expr) (tree core : Traversals) (maxBits : ℕ)
    (m : Memory W) (room : b.idBase+b.rows<2^W) (ports : goods≤2^W) (positiveCore : 0<b.coreRows) :
    ∀ s∈p.paidSlices sink b.idBase role (fun i=>b.commonID (ids i)) (b.guardWalk tree) (b.guardWalk core) maxBits,
      b.Supported s m := by
  intro s member
  have cases' : s=PaidWidths.paidDirect p.pricedArea p.stockSource (p.labelSource sink b.idBase role (fun i=>b.commonID (ids i))) ∨
      s∈p.mateSlices (b.guardWalk tree) ∨
      s=PaidWidths.paidBroadcast p.pricedArea tree.positions tree.owner tree.parity (b.checkedEdge tree.edge) tree.sourceRow p.board.batch.copies maxBits ∨
      s=PaidWidths.paidSpill p.pricedArea core.positions core.owner core.parity (b.checkedEdge core.edge) core.sourceRow := by
    simpa only [Format.paidSlices,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,guardWalk,or_assoc] using member
  rcases cases' with rfl|mate|rfl|rfl
  · intro i j hit
    exact b.selected_common role ids m (i.val:Word W) j room ports positiveCore hit
  · cases h : tree.catalystMate with
    | none => simp [Format.mateSlices,guardWalk,h] at mate
    | some t =>
      simp [Format.mateSlices,guardWalk,h] at mate
      subst s
      intro i j hit
      exact b.checked_hit t.2 m (i.val:Word W) j (by omega) hit
  · exact b.walk_supported _ tree m (by omega) rfl
  · exact b.walk_supported _ core m (by omega) rfl

theorem Board.history_supported (b : Board) (mesh : Mesh) (format : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r b.rows) (role : Attempt→Expr)
    (ids : Attempt→Fin goods→Expr) (tree core : Attempt→Traversals) (boundary : Boundary → CommodityColumn→Traversals)
    (maxBits : ℕ) (m : Memory W) (room : b.idBase+b.rows<2^W) (ports : goods≤2^W) (positiveCore : 0<b.coreRows) :
    ∀ s∈paidSlices mesh format feeds sink b.idBase role (fun a i=>b.commonID (ids a i))
      (fun a=>b.guardWalk (tree a)) (fun a=>b.guardWalk (core a)) (fun a c=>b.guardWalk (boundary a c)) maxBits,
        b.Supported s m := by
  intro s member
  obtain ⟨ev,_,inside⟩ := List.mem_flatMap.mp member
  cases ev with
  | attempt a => exact b.attempt_supported (format a) sink (role a) (ids a) (tree a) (core a) maxBits m room ports positiveCore s inside
  | feed a =>
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp inside
    exact b.walk_supported _ (boundary a c) m (by omega) rfl

theorem Board.no_dormant_load (b : Board) (ss : List PaidWidths.Slice) (m : Memory W) (j : Fin b.boughtRows)
    (support : ∀ s∈ss,b.Supported s m) (off : b.bought.flag.eval m (j.val:Word W)=0) :
    PaidWidths.total ss m (b.boughtIndex j)=0 := by
  induction ss with
  | nil => rfl
  | cons s rest ih =>
    have zero : s.load m (b.boughtIndex j)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact ite_eq_right (fun eq => support s (by simp) i j eq off)
    have tail := ih (fun t ht=>support t (List.mem_cons_of_mem _ ht))
    change s.load m (b.boughtIndex j)+PaidWidths.total rest m (b.boughtIndex j)=0
    rw [zero,tail,Nat.zero_add]

theorem Board.core_route_disjoint (b : Board) {T : Type*} [Fintype T] (routes : T→List (Fin b.coreRows))
    (bits : T→ℕ) (j : Fin b.boughtRows) :
    routeLoad (fun t=>(routes t).map b.coreIndex) bits (b.boughtIndex j)=0 := by
  apply Finset.sum_eq_zero
  intro t _
  have missing : b.boughtIndex j∉(routes t).map b.coreIndex := by
    intro inside
    obtain ⟨e,_,eq⟩ := List.mem_map.mp inside
    have pos := congrArg Fin.val eq
    change e.val=b.coreRows+j.val at pos
    have := e.isLt
    omega
  simp only [List.count_eq_zero_of_not_mem missing,Nat.zero_mul]


end
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end OAI
