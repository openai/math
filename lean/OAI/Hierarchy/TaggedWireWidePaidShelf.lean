import OAI.Hierarchy.TaggedWireTerminalPortRead
import OAI.Hierarchy.ProbeFixedWidePurchasedBefore
import OAI.Hierarchy.ProbeFixedWideSignedCore

namespace OAI
/-! # The real flat purchased shelf on the terminal replay -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h


local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "f" => v.nativeFormats P h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "g" => v.stamp P h width r banks source table target owners
local notation "slots" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "order" => wideRouteOrder h D k


local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "G" => (WideMemory.dir h v.W k v.wideJobs).groups
local notation "sourceBoard" => (v.wideSources h width).2
local notation "pub" => BoughtSockets.Public.join sourceBoard v.sampler h v.W k v.depth K G H R

/-- The original flat bought-row ordinal selects its actual outer shelf in the
final memory. Both copies of the CT endpoints and all oriented DFS digits are
preserved through calendar checkout, settlement and prefix replay. -/
theorem wide_paid_shelf_read (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (M : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D) (m : Boot.Tape h D)
    (room : (A).endAddress v.mesh<2^w)
    (whole : Calendar.mounted C (events v.mesh) (v.wideSignedMidAt h width size stock M π order raw))
    (keep : ∀x,x<(A).endAddress v.mesh→m x=v.wideSignedCheckoutAt h width size stock M π order raw x)
    (j : Fin v.wideJobs) (i : PurchaseFrozen.Key h D k) : ((pub).shelf j).PortData v.sampler π v.depth i m := by
  let current:=v.wideSignedMidAt h width size stock M π order raw
  let token:=v.wide_signed_boot_at h width size extent stock M π order raw room
  let keys:=BoughtSockets.Public.keyHead v.sampler (P).routes.column h v.W k v.depth
  have pos:=v.wideGeometryPrefix h width
  have low:=v.catalyst_initial_le_first P h width
  have sides:=(BoughtSockets.Public.borders v.sampler (P).routes.column h v.W k v.wideJobs v.depth).2
  have keyEnd : keys.stop≤(A).first := sides.trans ((Nat.le_add_right ..).trans (pos.2.2.trans low))
  let coord : Fin (v.mesh.inject+v.mesh.cool)×Fin v.mesh.outerFuel≃Fin v.wideJobs:=finProdFinEquiv
  obtain ⟨⟨phase,trial⟩,rfl⟩:=coord.surjective j
  have names:=v.sourcePair_uses h width K G H R (CoreCatalogue.pointBits h v.W) 0 (v.wideJoint h width)
    r banks source table target owners phase trial
  have shelf_eq : (sourceBoard).shelf (finProdFinEquiv (phase,trial)) =
      ((s).outer phase trial).market.shelf := names.1
  change ((sourceBoard).shelf (finProdFinEquiv (phase,trial))).PortData _ _ _ _ _
  rw [shelf_eq]
  apply v.terminal_port_read P h width r banks source table target owners current π phase trial
    whole token.2.1.geometry (pos.2.1.trans low) keyEnd token.2.2.1.board.rom.keys m _ i
  intro x before
  rw [keep x before]
  exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl before)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
