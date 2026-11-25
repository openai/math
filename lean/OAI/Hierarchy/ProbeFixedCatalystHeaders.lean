import OAI.Hierarchy.ProbeFixedNativeBoards
import OAI.Hierarchy.ProtocolRAMCatalystDateHeader

namespace OAI
/-! # The signed role table and physical core layout of the fixed native chart -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage StripChart CatalogueRows CoreBoard
open scoped Classical Fin.CommRing

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel

/-- Only public index counts, the original stratum directory and its fixed layout are
installed. The selector outputs and occurrence amounts are subsequently read by the program. -/
def catalystPlacement (z K G H R : ℕ) (b : JointHeader.Board) (cat : CatalogueRows.Board)
    (original : BoughtSockets.Directory n) : v.Placement where
  joint:=b
  catalogue:=cat
  routes:=⟨BoughtSockets.Public.join original v.sampler z v.W k v.depth K G H R,
    CoreRoute.directoryBase v.sampler z v.W k n v.depth K G H R,CoreCatalogue.top z v.W K G H R,K,G,H⟩

theorem catalystPlacement_addresses (z K G H R : ℕ) (b : JointHeader.Board) (cat : CatalogueRows.Board)
    (original : BoughtSockets.Directory n) :
    let x:=(v.catalystPlacement z K G H R b cat original).routes
    x.column=CoreCatalogue.top z v.W K G H R ∧
      x.directory.remapBase=CoreCatalogue.groupStart z v.W ∧
      x.directory.sitesBase=CoreCatalogue.siteBase z v.W K ∧ x.directory.superBase=CoreCatalogue.superStart z v.W ∧
      x.core=CoreRoute.directoryBase v.sampler z v.W k n v.depth K G H R ∧ x.bins=G := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Both priced strips use exactly the same padded role header that the public economic
boot loads. Its domain has the common number of strip rows at the current height. -/
theorem catalyst_header (P : v.Placement) (z width : ℕ) (a : Attempt) :
    ((v.publicHeader P z width).ports.header 0)=
      StripChart.header F (withPorts (v.nativeBoards P z width) v.mesh P.catalogue P.routes) a := by
  cases a <;> simp only [PortROM.Table.header,Fin.val_zero,Nat.zero_mul,Nat.add_zero] <;> rfl

/-- Applying the signed reporter to its original calibrated native boards leaves their native
roles and purchase shelf literally equal to the ones used by the market. -/
theorem catalyst_boards (P : v.Placement) (z width : ℕ) :
    withPorts (v.nativeBoards P z width) v.mesh P.catalogue P.routes=v.nativeBoards P z width := by
  rfl

theorem catalyst_chart (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks)
    (src table dst : ℕ) (owners : Bank) :
    StripChart.chart F v.mesh (v.privateArena P z width) P.joint.initial width v.keepLimit
        (withPorts (v.nativeBoards P z width) v.mesh P.catalogue P.routes) v.finish (v.basePhase width)
        P.catalogue r banks src table dst owners=v.nativeChart P z width r banks src table dst owners := by
  simp only [v.catalyst_boards, nativeChart]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
