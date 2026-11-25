import OAI.Hierarchy.ProbeFixedCatalystHeaders
import OAI.Hierarchy.ProtocolRAMCatalystStripAllocated

namespace OAI
/-! # Signed settlement for the two menus and the input tape of the fixed protocol -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CatalystArchive StripChart CatalogueRows StripDirectory
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
variable {K G H R K₁ jobs size : ℕ} (z width : ℕ) (b : JointHeader.Board) (cat : CatalogueRows.Board)
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "N" => Stages z (2^v.W)
variable (order : Fin R≃Edges v.sampler z (2^v.W) k) (M : ℕ) (groups : Fin K≃AllGroups z (2^v.W))
  (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z v.W (ReportSockets.copies k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))) H)
  (sockets : BoughtSockets.Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)) (π : Equiv.Perm (Fin (2^z))) (place : Site z (2^v.W) k→Fin K₁)
  (B : Mount (S:=v.sampler) π place cat.rows)
local notation "P" => v.catalystPlacement z K dir.groups H R b cat sockets
local notation "s" => v.nativeBoards P z width
local notation "E" => v.publicHeader P z width
local notation "A" => v.privateArena P z width
local notation "szBoard" => v.sized (v.seed P z width) width
local notation "prices" => v.basePhase width

/-- Install the genuine economic pages and pass their starting pointers, both public
catalogues and all the signed-report coordinates to the allocated execution theorem. -/
abbrev catalyst_settlement (stock : Bank) (start : ℕ) (slices : List PaidWidths.Slice)
    (o : CoreRoute.Orders z (2^v.W) k) (markets : Fin jobs→Market z (2^v.W) k) (raw : Boot.Tape z (2^v.W))
    (boot : Boot.Layout markets size) :=
  letI : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  let charges:=StripChart.charges F szBoard v.cost (E).stop
  let paid:=purchasedMenu F v.depth k v.positive v.radius (Nat.cast_nonneg _)
    v.toleranceAt v.geometry.cutoff.1 v.cost.purchase v.cost.purchase_nonneg 0
  letI : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  let room : (E).Ordered:=economic_ordered F szBoard v.cost v.mesh b cat (P).routes v.finish prices
    v.digitRadix v.digitRadix v.precision v.precision
  let address:=v.catalystPlacement_addresses z K dir.groups H R b cat sockets
  fun tail staticLow geometry height tape marketLow first heap core =>
    boot_settlement_allocated (scale:=v.copyScale) (payload:=width) F s v.mesh cat (P).routes A stock start b.initial
      width v.keepLimit v.finish prices slices o order M groups dir sockets π place B E charges (v.emptyReserve P z width)
      b N (DeadlineROM.prices v.mesh v.finish prices) markets raw room rfl rfl rfl boot
      (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) tail staticLow geometry height tape marketLow first le_rfl
      heap core (PacketWidths.ofMenu paid) address.1 address.2.1 address.2.2.1 address.2.2.2.1 address.2.2.2.2.2
      (v.catalyst_header P z width)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
