import OAI.Hierarchy.ProbeSiteAddress
import OAI.Hierarchy.TaggedWireRolePageCore

namespace OAI
/-! # Public inverse of the actual blown-up site to column projection -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.SiteDirectory
open AdaptiveProbe ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {h d k W : ℕ}

def size (h d k : ℕ) := Fintype.card (ColumnLayer k)*Fintype.card (Columns h d)

def slot (c : Columns h d) (layer : ColumnLayer k) : Fin (size h d k) :=
  finProdFinEquiv ((Fintype.equivFin _ layer),(Fintype.equivFin _ c))

def table (h d k : ℕ) (i : Fin (size h d k)) : ℕ :=
  let q : Fin (Fintype.card (ColumnLayer k)) × Fin (Fintype.card (Columns h d)) := finProdFinEquiv.symm i
  (siteNumber h d k ((Fintype.equivFin _).symm q.2,(Fintype.equivFin _).symm q.1)).val

theorem table_slot (c : Columns h d) (layer : ColumnLayer k) :
    table h d k (slot c layer)=(siteNumber h d k (c,layer)).val := by simp [table,slot]

def mount (base h d k : ℕ) (m : Memory W) : Memory W :=
  HistoryRoles.RoleROM.init base (table h d k) m

theorem mounted (base h d k : ℕ) (m : Memory W) :
    HistoryRoles.RoleROM.Mounted base (table h d k) (mount base h d k m) :=
  HistoryRoles.RoleROM.mount base (table h d k) m

/-- The column is a measured runtime result; the layer is fixed by the
local party in the finite native strip format. No private permutation enters
the ROM. -/
def cell (base h d : ℕ) (layer : ColumnLayer k) (col : Expr) : Expr :=
  HistoryRoles.RoleROM.expr base (size h d k)
    (.op .add (.lit ((Fintype.equivFin _ layer).val*Fintype.card (Columns h d))) col)

theorem read {base : ℕ} (m : Memory W) (rom : HistoryRoles.RoleROM.Mounted base (table h d k) m)
    (layer : ColumnLayer k) (col : Expr) (r : Word W) (c : Columns h d) (room : size h d k≤2^W)
    (measured : col.eval m r=((Fintype.equivFin _ c).val:Word W)) :
    (cell base h d layer col).eval m r=((siteNumber h d k (c,layer)).val:Word W) := by
  rw [←table_slot]
  apply HistoryRoles.RoleROM.read rom _ r (slot c layer) room
  change (((Fintype.equivFin _ layer).val*Fintype.card (Columns h d):ℕ):Word W)+col.eval m r=((slot c layer).val:Word W)
  rw [measured,←Nat.cast_add]
  apply congrArg (fun n:ℕ=>(n:Word W))
  simp only [slot,finProdFinEquiv_apply_val]
  ring

theorem words (h d k : ℕ) (positive : 1 ≤ d) : size h d k ≤ siteFactor d k*2^h := by
  have count := site_count h d k positive
  rw [←Fintype.card_fin (n:=siteLast h d k+1),←Fintype.card_congr (siteNumber h d k)] at count
  simpa only [size,Site,ColumnSite,Fintype.card_prod,Nat.mul_comm] using count

end Hierarchy.ProbeStage.CoreBoard.SiteDirectory

end
end OAI
