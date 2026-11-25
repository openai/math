import OAI.Hierarchy.TaggedWideInstalledLayout

namespace OAI
/-! # Exact terminal-ROM contents of the fully assembled static input -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard HistoryRoles Tagged
open ProtocolRAMFrozenWindow ProtocolRAMSupergroupDirectory ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A : ℝ} (x : WideParent κ A) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
  (dated : WideCPU.Dated (events v.mesh).length)
local notation "cap" => v.wideInstalledCap unitCost
local notation "rom" => v.wideInstalledRoot x
local notation "S" => v.wideInstalledSize x m ell unitCost dated
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
local notation "bits" => v.maxBits
local notation "P" => v.widePlacement x.h x.w

variable (sites : dated.siteDirectorySize=SiteDirectory.size x.h (2^v.W) k)
  (edges : dated.rawEdges=(v.widePlacement x.h x.w).catalogue.rows)
local notation "image" => v.wideInstalledHeader x m ell short u δ ξ unitCost dated sites edges


/-- This is the preimage supplied to the terminal's ROM installer in the actual finite header. -/
def wideTerminalPreimage
    (siteCount : dated.siteDirectorySize=SiteDirectory.size x.h (2^v.W) k)
    (edgeCount : dated.rawEdges=(v.widePlacement x.h x.w).catalogue.rows)
    (raw : Memory (Native.wordBits x.h (2^v.W) Native.copies)) : Memory (Native.wordBits x.h (2^v.W) Native.copies) :=
  let data:=fun j=>SiteDirectory.table x.h (2^v.W) k (Fin.cast siteCount j)
  let stage:=fun j=>decide ((P).catalogue.transport (v.wideOrder x.h x.w) (Fin.cast edgeCount j))
  dated.words (v.wideInstalledRoot x) data stage raw

theorem wideInstalledHeader_terminal (raw : Memory W) (a : ℕ)
    (before : a<v.wideTerminalROMEnd x.h x.w bits (dated.romEnd rom) (dated.workEnd S)) :
    image raw a=v.wideTerminalWords x.h x.w bits (dated.romEnd rom) (dated.workEnd S)
        (v.wideTerminalPreimage x dated sites edges raw) a := by
  let mid:=v.wideTerminalWords x.h x.w bits (dated.romEnd rom) (dated.workEnd S)
    (v.wideTerminalPreimage x dated sites edges raw)
  change v.wideWindowWords x m ell short u δ ξ cap dated bits rom mid a=mid a
  apply v.wideWindowWords_before
  exact before.trans_le (v.wide_terminal_before_groups x dated bits rom (dated.workEnd S))

/-- It suffices to preserve the input on the terminal's own subinterval. Each caller can
transport the installed data through its actual prefix while freely writing other intervals. -/
theorem wideInstalledHeader_terminal_cut (raw state : Memory W)
    (keep : ∀a,dated.romEnd rom≤a→a<v.wideGroupROM x dated bits rom→state a=image raw a)
    (a : ℕ) (low : dated.romEnd rom≤a)
    (high : a<v.wideTerminalROMEnd x.h x.w bits (dated.romEnd rom) (dated.workEnd S)) :
    state a=v.wideTerminalWords x.h x.w bits (dated.romEnd rom) (dated.workEnd S)
        (v.wideTerminalPreimage x dated sites edges raw) a :=
  (keep a low (high.trans_le (v.wide_terminal_before_groups x dated bits rom (dated.workEnd S)))).trans (v.wideInstalledHeader_terminal x m ell short u δ ξ unitCost dated sites edges raw a high)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
