import OAI.Hierarchy.TaggedWireOriginalFits
import OAI.Hierarchy.TaggedWirePaidRoleRead
import OAI.Hierarchy.ProtocolRAMCoreCatalogueSource
import OAI.Hierarchy.ProtocolRAMBoughtCatalogue

namespace OAI
/-! # The native paid socket expressions fit in the actual catalogue read range -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open AdaptiveProbe ReportSockets ProtocolRAM Calendar
variable {w out : ℕ}

private theorem site_operands {base G H : ℕ} {group slot : Expr}
    (ready : (SiteROM.siteExpr base G H group slot).Fits w out) : group.Fits w out ∧ slot.Fits w out :=
  ⟨ready.2.1.2,ready.2.2⟩

theorem core_fits (z : Sizes) (base R bits siteBase superBase K G H k attempts start : ℕ)
    (source : (CoreCatalogue.source base R bits siteBase superBase K G H k attempts).All (Expr.Fits w out))
    (rows : z.freeRows=R) (before : z.ceiling start≤out) (room : z.ceiling start<2^w) (side : Bool) :
    (coreInputs base (z.free start) R bits superBase K k attempts side).Fits w out := by
  have table : (RoleROM.bank (z.free start+(if side then 1 else 0)*R) R).Fits w out := by
    apply bank_fits z _ before room
    rw [←rows]
    dsimp [Sizes.stop,Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext]
    cases side <;> simp <;> omega
  have flag : (CoreCatalogue.field base R 0).Fits w out := source.1.1
  cases side
  · have seen := site_operands source.2.1.2.2.2
    exact ⟨flag,⟨table,trivial⟩,seen.1,seen.2⟩
  · have seen := site_operands source.2.2.1.2.2.2
    exact ⟨flag,⟨table,trivial⟩,seen.1,seen.2⟩

theorem bought_fits {attempts : ℕ} (v : BoughtSockets.Directory attempts) (S : PurchaseSampler)
    (h W k depth K G H : ℕ)
    (source : (v.source S h W k depth K G H).All (Expr.Fits w out)) (side : Bool) :
    (boughtInputs v S h W k depth K side).Fits w out := by
  cases side
  · have seen := site_operands source.2.1
    exact ⟨trivial,trivial,seen.1,seen.2⟩
  · have seen := site_operands source.2.2.1
    exact ⟨trivial,trivial,seen.1,seen.2⟩

/-- The padded branch-select and each nested native indirection are all safe on
the complete paid ordinal range. These assumptions are the original catalogue
fits already used by its own geometry serializer. -/
theorem catalogue_fits {attempts : ℕ} (z : Sizes) (b : CatalogueRows.Board)
    (v : BoughtSockets.Directory attempts) (S : PurchaseSampler) (h W k depth K G H : ℕ)
    (base R bits siteBase superBase start : ℕ)
    (core : (CoreCatalogue.source base R bits siteBase superBase K G H k attempts).All (Expr.Fits w out))
    (bought : (v.source S h W k depth K G H).All (Expr.Fits w out))
    (rows : z.freeRows=R) (before : z.ceiling start≤out) (room : z.ceiling start<2^w) (side : Bool) :
    (paidInputs b (coreInputs base (z.free start) R bits superBase K k attempts)
      (boughtInputs v S h W k depth K) side).Fits w out :=
  paid_fits b _ _ (core_fits z base R bits siteBase superBase K G H k attempts start core rows before room)
    (bought_fits v S h W k depth K G H bought) side

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom

end
end OAI
