import OAI.Hierarchy.ProbeCatalystArchiveGeometry
import OAI.Hierarchy.ProtocolRAMPortPaddingCore
import OAI.Hierarchy.ProtocolRAMSchedule
import OAI.Hierarchy.ProtocolRAMHistogram
import OAI.Hierarchy.ProtocolRAMRowChoice
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Computing reserve owners from the same strip columns as the two radius hops -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing Classical

variable {C H E G : Type*} [Fintype C] [Fintype H] [Fintype E] [Fintype G]
variable {k D w : ℕ}
local notation "Roles" => Role C H E k

def ownerExpr (column : C→Expr) : Roles→Expr
  | .catalyst c j => .op .add (.lit j.val) (scale k (column c))
  | _ => .lit 0

def releaseExpr : Roles→Expr
  | .catalyst .. => .lit 1
  | _ => .lit 0

/-- Each table is indexed by the physical field at the common padded stride.
Its genuine entries evaluate at the stored ball word. -/
def select (field ball : Expr) (table : Roles→Expr) : Expr :=
  chooseField D 0 (PortPadding.extend (fun i=> (table ((Fintype.equivFin Roles).symm i)).atRow ball)
    (.lit 0)) field

theorem select_real (field ball : Expr) (table : Roles→Expr) (mem : Memory w) (r : Word w)
    (bound : Fintype.card Roles ≤ D) (room : D ≤ 2^w) (v : Roles)
    (hit : (field.eval mem r).val=((Fintype.equivFin Roles) v).val) :
    (select (D:=D) field ball table).eval mem r=(table v).eval mem (ball.eval mem r) := by
  let i := PortPadding.inject bound ((Fintype.equivFin Roles) v)
  rw [select,eval_chooseField _ _ _ _ _ _ i (by simpa using room) (by simpa [i,PortPadding.inject] using hit)]
  simp [i,PortPadding.extend_real,eval_atRow]

theorem select_padding (field ball : Expr) (table : Roles→Expr) (mem : Memory w) (r : Word w)
    (room : D ≤ 2^w) (i : Fin D) (hit : (field.eval mem r).val=i.val)
    (tailRow : Fintype.card Roles ≤ i.val) :
    (select (D:=D) field ball table).eval mem r=0 := by
  rw [select,eval_chooseField _ _ _ _ _ _ i (by simpa using room) (by simpa using hit),
    PortPadding.extend_tail _ _ _ tailRow]
  rfl

theorem owner_read (column : C→Expr) (field ball : Expr) (mem : Memory w) (r : Word w)
    (bound : Fintype.card Roles ≤ D) (room : D ≤ 2^w) (c : C) (axis : Fin k) (g : G)
    (hit : (field.eval mem r).val=((Fintype.equivFin Roles) (.catalyst c axis)).val)
    (placed : (column c).eval mem (ball.eval mem r)=(((Fintype.equivFin G) g).val:Word w)) :
    (select (D:=D) (k:=k) field ball (ownerExpr (H:=H) (E:=E) column)).eval mem r =
      ((pairKeys G k (g,axis)).val:Word w) := by
  rw [select_real field ball _ mem r bound room _ hit]
  simp only [ownerExpr,Expr.eval,eval_scale,placed,pairKeys_val,Nat.cast_add,Nat.cast_mul]
  rfl

/-- Only a catalyst occurrence can release external bits. Its amount is the
observed consumed word, once for the pair of radius edges. -/
def debitExpr (field ball take : Expr) : Expr :=
  .branch .eq (select (D:=D) field ball (releaseExpr (C:=C) (H:=H) (E:=E) (k:=k))) (.lit 1) take (.lit 0)

def ownerPass (base cells : ℕ) (column : C→Expr) (field ball : Expr) : Pass :=
  ⟨base,cells,select (D:=D) field ball (ownerExpr (H:=H) (E:=E) (k:=k) column)⟩

/-- The owner scan runs at any dated or terminal address with a disjoint
output interval. Its exact cost counts the actual finite role selector. -/
theorem execute_owner (base cells : ℕ) (column : C→Expr) (field ball : Expr) (mem : Memory w)
    (fit : (ownerPass (D:=D) (H:=H) (E:=E) (k:=k) base cells column field ball).Fits w) :
    let p := ownerPass (D:=D) (H:=H) (E:=E) (k:=k) base cells column field ball
    (scan w base cells p.term).Exec mem (p.apply mem) (4+cells*(2*p.term.work+4)) := by
  exact scan_exec base cells _ mem fit.1 fit.2

theorem stored_owner (base cells : ℕ) (column : C→Expr) (field ball : Expr) (mem : Memory w)
    (row : Fin cells) (bound : Fintype.card Roles ≤ D) (room : D ≤ 2^w) (c : C) (axis : Fin k) (g : G)
    (hit : (field.eval mem (row.val:Word w)).val=((Fintype.equivFin Roles) (.catalyst c axis)).val)
    (placed : (column c).eval mem (ball.eval mem (row.val:Word w))=(((Fintype.equivFin G) g).val:Word w)) :
    ((ownerPass (D:=D) (H:=H) (E:=E) (k:=k) base cells column field ball).apply mem) (base+row.val)=
      ((pairKeys G k (g,axis)).val:Word w) := by
  exact (ProtocolRAMGeneratedWrite.read_image ..).trans
    (owner_read column field ball mem (row.val:Word w) bound room c axis g hit placed)

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
