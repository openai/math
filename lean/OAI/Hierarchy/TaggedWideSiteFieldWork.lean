import OAI.Hierarchy.TaggedWideSiteReplay
import OAI.Hierarchy.ProtocolRAMRowChoiceWork
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # Fixed costs for physical participant selection and its dated scatter address -/
noncomputable section
namespace Hierarchy.ProtocolRAM.NativeSiteWork
open Computability.VPVNP.BurstRAM PrivateRAM
open ProbeStage.CoreBoard.HistoryRoles
open scoped Classical

def chooseCost (n B : ℕ) := 1+n*(7+B+2)

theorem column (base I L C : ℕ) (j : Fin 3) : (SiteScatter.column base I L C j).work=7 := rfl

theorem localTag {L : ℕ} (base I C B : ℕ) (site : Fin L→Expr) (cheap : ∀i,(site i).work≤B) :
    (SiteScatter.localTag (I:=I) (C:=C) base site).work ≤ chooseCost L (8*B) := by
  unfold SiteScatter.localTag
  apply BoughtSockets.choose_work_bound
  intro i
  have h := Calendar.CatalogueRows.substitute_work (site i) (SiteScatter.column base I L C 0)
  rw [column] at h
  have := cheap i
  omega

theorem fieldValue {L C : ℕ} (base I B : ℕ) (field : Fin L→Fin C→Expr) (cheap : ∀i j,(field i j).work≤B) :
    (SiteScatter.fieldValue (I:=I) base field).work≤chooseCost L (chooseCost C (8*B)) := by
  unfold SiteScatter.fieldValue
  apply BoughtSockets.choose_work_bound
  intro i
  apply BoughtSockets.choose_work_bound
  intro j
  have h := Calendar.CatalogueRows.substitute_work (field i j) (SiteScatter.column base I L C 0)
  rw [column] at h
  have := cheap i j
  omega

theorem selectedValue {L C : ℕ} (base I B : ℕ) (site : Fin L→Expr) (field : Fin L→Fin C→Expr)
    (cheap : ∀i,(site i).work≤B) (cost : ∀i j,(field i j).work≤B) :
    (SiteScatter.selectedValue (I:=I) base site field).work ≤
      chooseCost L (8*B)+chooseCost L (chooseCost C (8*B))+3 := by
  have x := localTag base I C B site cheap
  have y := fieldValue base I B field cost
  simp only [SiteScatter.selectedValue,Expr.work]
  omega

theorem role_offset (stride : Bank) (site role : Expr) :
    (RoleWidths.offset stride site role).work=site.work+role.work+6 := by
  simp only [RoleWidths.offset,Expr.work]
  omega

theorem fieldIndex {L : ℕ} (base I C B : ℕ) (stride : Bank) (site : Fin L→Expr) (cheap : ∀i,(site i).work≤B) :
    (SiteScatter.fieldIndex (I:=I) (C:=C) base stride site).work≤chooseCost L (8*B)+13 := by
  have := localTag base I C B site cheap
  simp only [SiteScatter.fieldIndex,role_offset,column]
  omega

theorem role_destination (base sink : ℕ) (size index : Expr) :
    (RoleWidths.destination base sink size index).work=size.work+index.work+5 := by
  simp only [RoleWidths.destination,Expr.work]
  omega

end Hierarchy.ProtocolRAM.NativeSiteWork

end
end OAI
