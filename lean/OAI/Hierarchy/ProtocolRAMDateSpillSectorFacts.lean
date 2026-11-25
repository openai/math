import OAI.Hierarchy.TaggedWideChronologicalOrder
import OAI.Hierarchy.TaggedWideRoleSheetRun
import OAI.Hierarchy.TaggedWireRolePageCore

namespace OAI
/-! # The two mounted chronological role sheets and their stride table -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open AdaptiveProbe ProbeStage ReportSockets CoreBoard CoreBoard.HistoryRoles RoleProgram
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators

variable {h W k attempts native axes : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k attempts) (unique : Exclusive marks) (b : CatalogueRows.Board)
    (order : Fin b.coreRows≃Edges S h (2^W) k)
    (sized : attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)=b.boughtRows)
    (axis : Catalysts h W k≃Fin axes)
variable (n full only rom : ℕ) (whole qty : Fin (Fintype.card (Source S π depth marks))→ℕ) (m : Memory native)

/-- Both sheets consist of the actual scattered triples. Only readable coordinates,
field value ranges, and the stride ROM are required. -/
structure SectorRead : Prop where
  entire : ∀f,DatedRoleSheets.roleFact n S π depth marks unique (timeRows S π depth marks b order sized axis) full whole (fun i=>(sparseKey S π depth marks b order sized
      (PurchaseInventory.slotEquiv h (Stages h (2^W)) k) axis ((timeRows S π depth marks b order sized axis) i)).val) m f
  sparse : ∀f,DatedRoleSheets.roleFact n S π depth marks unique (timeRows S π depth marks b order sized axis) only qty (fun i=>(sparseKey S π depth marks b order sized
      (PurchaseInventory.slotEquiv h (Stages h (2^W)) k) axis ((timeRows S π depth marks b order sized axis) i)).val) m f
  strides : RoleROM.Mounted rom (fun i : Fin (siteLast h (2^W) k+1)=>i.val*stride k S.degree attempts) m
  wholeSmall : ∀i,whole i<2^native
  sparseSmall : ∀i,qty i<2^native
  idSmall : ∀i,((fun i=>(sparseKey S π depth marks b order sized
      (PurchaseInventory.slotEquiv h (Stages h (2^W)) k) axis ((timeRows S π depth marks b order sized axis) i)).val) i)<2^native
  siteRoom : siteLast h (2^W) k+1≤2^native
  roleRoom : 2*(stride k S.degree attempts)≤2^native
  spanRoom : (siteLast h (2^W) k+1)*(stride k S.degree attempts)≤2^native
  wide : 1<2^native

end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets

end
end OAI
