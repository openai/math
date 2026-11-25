import OAI.Hierarchy.TaggedWireSocketWork
import OAI.Hierarchy.TaggedWideDatedRoleSheetCost
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! Expression work of both orientations on a two-sided dated row sheet. -/
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows
open ProtocolRAM RoleProgram
theorem each_work (n : ℕ) (x y : Expr) {U : ℕ} (hx : x.work≤U) (hy : y.work≤U) :
    (each n x y).work≤22*U+4 := by
  have X:=Calendar.CatalogueRows.substitute_work x (index n)
  have Y:=Calendar.CatalogueRows.substitute_work y (index n)
  have J : (index n).work=10:=rfl
  rw [J] at X Y
  change 2+1+(x.atRow (index n)).work+(y.atRow (index n)).work+1≤_
  omega

theorem split_work (n : ℕ) (s : Bool→Socket) {U : ℕ} (raw : ∀b,(s b).Work U) (b : Bool) :
    (split n s b).Work (22*U+4) :=
  ⟨each_work n _ _ (raw b).positive (raw (!b)).positive,each_work n _ _ (raw b).ordinal (raw (!b)).ordinal,
    each_work n _ _ (raw b).group (raw (!b)).group,each_work n _ _ (raw b).slot (raw (!b)).slot⟩

theorem input_work (n : ℕ) (L : Chart) (s : Bool→Socket) (wid num : Expr) {U V : ℕ}
    (raw : ∀b,(s b).Work U) (h₁ : wid.work≤V) (h₂ : num.work≤V) :
    DatedRoleSheets.InputWork n L s wid num (max (22*V+4) (4*(22*U+4)+18)) := by
  have before:=Nat.le_max_right (22*V+4) (4*(22*U+4)+18)
  exact ⟨(each_work n _ _ h₁ h₁).trans (Nat.le_max_left ..),
    (each_work n _ _ h₂ h₂).trans (Nat.le_max_left ..),
    (socket_work L _ (split_work n s raw false)).1.trans before,
    (socket_work L _ (split_work n s raw false)).2.trans before,
    (socket_work L _ (split_work n s raw true)).1.trans before⟩
end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows

end OAI
