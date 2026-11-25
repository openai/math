import OAI.Hierarchy.TaggedWideDatedEmitters
import OAI.Hierarchy.TaggedWireSocketFits
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # Native operand ranges of the two opposite copies of every role record -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM RoleProgram
variable {W out : ℕ}

theorem each_fits (n : ℕ) (left right : Expr) (l : left.Fits W out) (r : right.Fits W out) :
    (each n left right).Fits W out := by
  have row : (index n).Fits W out := ⟨trivial,trivial,trivial,trivial,trivial⟩
  exact ⟨trivial,trivial,Calendar.CatalogueRows.fits_atRow _ _ l row,Calendar.CatalogueRows.fits_atRow _ _ r row⟩

theorem split_fits (n : ℕ) (s : Bool→Socket) (raw : ∀b,(s b).Fits W out) (b : Bool) :
    (split n s b).Fits W out :=
  ⟨each_fits n _ _ (raw b).positive (raw (!b)).positive,
    each_fits n _ _ (raw b).ordinal (raw (!b)).ordinal,each_fits n _ _ (raw b).group (raw (!b)).group,
    each_fits n _ _ (raw b).slot (raw (!b)).slot⟩

theorem role_fits (n : ℕ) (z : RoleRoom.Sizes) (start : ℕ) (s : Bool→Socket)
    (size number : Expr) (table : Bank) (raw : ∀b,(s b).Fits W out) (before : z.ceiling start≤out)
    (room : z.ceiling start<2^W) (wid : size.Fits W out) (idWord : number.Fits W out) (site : table.Fits W out) :
    DatedRoleSheets.Fits n (z.chart start) s table size number W out := by
  have okay (b : Bool):=RoleRoom.socket_fits z _ (split_fits n s raw b) before room
  exact ⟨each_fits n _ _ wid wid,each_fits n _ _ idWord idWord,(okay false).1,(okay false).2,
    (okay true).1,(okay true).2,site⟩

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows

end
end OAI
