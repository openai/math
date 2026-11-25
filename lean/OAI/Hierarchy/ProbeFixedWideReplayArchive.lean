import OAI.Hierarchy.ProbeFixedWidePrefixLayouts
import OAI.Hierarchy.ProbeFixedCatalystStaticEnd

namespace OAI
/-! # The reserve archive used to replay the dated width prefix -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CatalystArchive StripChart
open scoped Classical Fin.CommRing
variable {F : Type} [_root_.Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)

local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "original" => TerminalLayout.reserve start cnt page

def wideReplayArchive (ss : List PaidWidths.Slice) : ReserveUse.Archive :=
  {original with scratch:=(v.wideReserveLayout h width ss).scratch}

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
