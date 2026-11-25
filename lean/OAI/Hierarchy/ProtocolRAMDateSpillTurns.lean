import OAI.Hierarchy.ProtocolRAMDateSpillRelocate
import OAI.Hierarchy.ProtocolRAMTurnWindowRun
import OAI.Hierarchy.ProtocolRAMTurnText

namespace OAI
/-! # Native chronological publication with the absolute chord digit on both sides -/
noncomputable section
namespace Hierarchy.ProtocolRAM.DateSpill.Turns
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAMTurnItinerary ProtocolRAMTurnChart ProtocolRAMTurnInstalled
open scoped Classical Fin.CommRing

structure Offsets where
  old : Bank
  new : Bank

def extra (p : Chart) (b : Banks) (off : Offsets) (side : Bool) : Expr :=
  onEnd p side (.lookup off.old p.item) (.lookup off.new (.lookup b.edge (occurrence p side)))

def absolute (p : Chart) (b : Banks) (off : Offsets) (side : Bool) : Expr :=
  .op .add (extra p b off side) (start p b side)

def fields (p : Chart) (b : Banks) (off : Offsets) : Fin 7→Expr :=
  ![role p b false,role p b true,absolute p b off false,absolute p b off true,live p,p.site,p.seat]

def fieldWords (t : Turn) (v : Values) (oldBase newBase : ℕ→ℕ) : Fin 7→ℕ :=
  let digit (side : Bool):= (if t.boundary side then oldBase t.item else newBase (v.edge (t.occurrence side)))+t.start v side
  ![t.role v false,t.role v true,digit false,digit true,t.field v 4,t.site,t.seat]

variable {W N : ℕ}

theorem absolute_at (p : Chart) (b : Banks) (off : Offsets) (m : Memory W) (x : Word W)
    (t : Turn) (v : Values) (rd : p.Row m x t) (adj : b.Adjacent v m t) (one : 1<2^W)
    (inside : t.position≤t.length) (len : t.length<2^W) (oldBase newBase : ℕ→ℕ) (s : Bool)
    (old : t.boundary s→ off.old.read m (t.item:Word W)=(oldBase t.item:Word W))
    (new : ¬t.boundary s→ off.new.read m (v.edge (t.occurrence s):Word W)=(newBase (v.edge (t.occurrence s)):Word W)) :
    (absolute p b off s).eval m x=
      (((if t.boundary s then oldBase t.item else newBase (v.edge (t.occurrence s)))+t.start v s:ℕ):Word W) := by
  have base : (extra p b off s).eval m x =
      (((if t.boundary s then oldBase t.item else newBase (v.edge (t.occurrence s))) : ℕ) : Word W) := by
    rw [extra, boundary_at rd s _ _ (inside.trans_lt len) len]
    by_cases edge : t.boundary s
    · have on : t.position = (if s then t.length else 0) := edge
      simp only [ite_eq_left on, ite_eq_left edge, Expr.eval, rd.item, old edge]
    · have offEnd : t.position ≠ (if s then t.length else 0) := edge
      simp only [ite_eq_right offEnd, ite_eq_right edge, Expr.eval, occurrence_at rd s one inside edge,
        adj.edge s edge, new edge]
  change (extra p b off s).eval m x + (start p b s).eval m x = _
  rw [base, start_at rd adj s one inside len, Nat.cast_add]

theorem observed (src : ℕ) (p : Chart) (b : Banks) (off : Offsets) (r : Fin N→Turn) (v : Values)
    (oldBase newBase : ℕ→ℕ) (m : Memory W) (one : 1<2^W)
    (fit : ∀f,(fields p b off f).Fits W src) (room : src+7*N<2^W)
    (within : ∀i,(r i).position≤(r i).length)
    (weights : ∀i,(live p).eval m (i.val:Word W)=((r i).width:Word W))
    (active : ∀i,0<(r i).width→p.Row m (i.val:Word W) (r i) ∧ b.Adjacent v m (r i) ∧
      (r i).length<2^W ∧ (r i).site<2^W)
    (old : ∀i,0<(r i).width→∀s,(r i).boundary s→ off.old.read m ((r i).item:Word W)=(oldBase (r i).item:Word W))
    (new : ∀i,0<(r i).width→∀s,¬(r i).boundary s→
      off.new.read m (v.edge ((r i).occurrence s):Word W)=(newBase (v.edge ((r i).occurrence s)):Word W)) :
    let ps:=Columns.passes src N (fields p b off)
    ∃out,(ProtocolRAM.program W ps).Exec m out (clock ps) ∧
      ProtocolRAMTurnShelf.Source out src (fun i=>fieldWords (r i) v oldBase newBase) ∧
      ∀a,a< src ∨ src+7*N≤a→ out a=m a := by
  intro ps
  obtain ⟨ran,read,frame⟩:=Columns.run src (fields p b off) m fit room
  refine ⟨result ps m,ran,?_,frame⟩
  intro i f relevant
  have width : fieldWords (r i) v oldBase newBase 4=(r i).width := ite_eq_right (Nat.not_lt_of_ge (within i))
  rw [read]
  rcases relevant with rfl|on
  · change (live p).eval m (i.val : Word W) = (fieldWords (r i) v oldBase newBase 4 : Word W)
    rw [width]
    exact weights i
  change fieldWords (r i) v oldBase newBase 4 ≠ 0 at on
  rw [width] at on
  have pos:=Nat.pos_of_ne_zero on
  obtain ⟨rd,adj,len,site⟩:=active i pos
  fin_cases f
  · exact role_at rd adj false one (within i) len site
  · exact role_at rd adj true one (within i) len site
  · exact absolute_at p b off m _ (r i) v rd adj one (within i) len oldBase newBase false (old i pos false) (new i pos false)
  · exact absolute_at p b off m _ (r i) v rd adj one (within i) len oldBase newBase true (old i pos true) (new i pos true)
  · change (live p).eval m (i.val : Word W) = (fieldWords (r i) v oldBase newBase 4 : Word W)
    rw [width]
    exact weights i
  · exact rd.site
  · exact rd.seat


end Hierarchy.ProtocolRAM.DateSpill.Turns

end
end OAI
