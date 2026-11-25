import OAI.Hierarchy.ProtocolRAMPaidCatalogueBoard
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueImage
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueArena

namespace OAI
/-! # True register ranges of the joined native catalogue at the terminal pass -/

noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets.Public
open ProbeStage PurchaseFrozen AdaptiveProbe Calendar CatalogueRows
open scoped Classical
variable {w h W k attempts K G H R depth out : ℕ} (v : Directory attempts) (S : PurchaseSampler)
local notation "D" => 2^W
local notation "base" => CoreCatalogue.top h W K G H R
local notation "v'" => join v S h W k depth K G H R
local notation "cap" => ProtocolRAMPurchaseSampler.span (count h D k*paths h S.degree depth)

/-- All event-dependent addresses of the original purchased reader come from its
shelf, its kept flag and the sixth reported field. All other addresses are
fixed by the chronological header or the actual native core layout. -/
theorem joined_top (header : endAddress S base h W k attempts depth≤out)
    (shelf : ∀a,(v.shelf a).firstBase+count h D k*blockSize h D S.degree depth≤out)
    (flags : ∀a,v.flagBase a+cap≤out) (menus : ∀a,v.menuBase a+cap≤out) :
    (v').jointTop S h W k depth K G H R≤out := by
  have border:=borders S base h W k attempts depth
  change max base (max ((v').header h D k S.degree depth).stop
    (max (StripDirectory.stratumHeader h D k S.degree depth (v').keysBase).stop
      (Finset.univ.sup ((v').eventEnds S h D k depth))))≤out
  refine max_le ?_ (max_le ?_ (max_le ?_ (Finset.sup_le ?_)))
  · exact ((Nat.le_add_right _ _).trans border.1).trans (border.2.trans header)
  · exact header
  · exact border.2.trans header
  · intro a _
    exact max_le (shelf a) (max_le (flags a) (menus a))

theorem joined_sources (header : endAddress S base h W k attempts depth≤out)
    (shelf : ∀a,(v.shelf a).firstBase+count h D k*blockSize h D S.degree depth≤out)
    (flags : ∀a,v.flagBase a+cap≤out) (menus : ∀a,v.menuBase a+cap≤out) (word : out<2^w) :
    (CoreCatalogue.sourceAt h W k attempts R K G H (CoreCatalogue.pointBits h W)).All (Expr.Fits w out) ∧
      ((v').source S h W k depth K G H).All (Expr.Fits w out) := by
  have found:=(v').joint_fits S h W k depth K G H R w out (joined_top v S header shelf flags menus) word
  exact found

theorem geometry_fits (idBase : ℕ) (header : endAddress S base h W k attempts depth≤out)
    (shelf : ∀a,(v.shelf a).firstBase+count h D k*blockSize h D S.degree depth≤out)
    (flags : ∀a,v.flagBase a+cap≤out) (menus : ∀a,v.menuBase a+cap≤out) (word : out<2^w) (i : Fin 7) :
    ((liveBoard v' S h W k depth R K G H (CoreCatalogue.pointBits h W) idBase).geometry i).Fits w out := by
  have found:=joined_sources v S header shelf flags menus word
  exact Board.geometry_fits _ _ found.1 found.2

end Hierarchy.ProtocolRAM.BoughtSockets.Public

end
end OAI
