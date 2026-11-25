import OAI.Hierarchy.ProtocolRAMDiagnosticFits
import OAI.Hierarchy.ProbeFixedFailureWords

namespace OAI
/-! # Historical geometric operands of the complete fixed priced chart -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard PurchaseFrozen
open StripChart StripDirectory CatalogueRows BoughtSockets
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "W" => wordBits z (2^v.W) copies
local notation "geo" => v.located (v.seed P z width) P width
local notation "G" => P.routes
local notation "d" => (G).directory
variable (bound phase trial : ℕ) (space : bound<2^(wordBits z (2^v.W) copies))
    (core : P.catalogue.core.All (Expr.Fits (wordBits z (2^v.W) copies) bound))
    (orig : (P.routes).core+CoreLookup.words v.sampler z (2^v.W) k≤bound)
    (col : (P.routes).column+ColumnROM.words z (2^v.W) k≤bound)
    (cover : ColumnROM.Cover z v.W (P.routes.directory).remapBase (P.routes.directory).sitesBase (P.routes.directory).superBase (P.routes).oldGroups (P.routes).bins (P.routes).height bound)

include space core orig col cover in
theorem payload_link_fits : LinkOperands (repair C (.outer phase trial)).link W bound :=
  payload_diagnostic_fits geo v.mesh P.catalogue G phase trial space core orig col cover

include space core orig col cover in
theorem purchased_link_fits (j t : ℕ)
    (keys : (stratumHeader z (2^v.W) k v.sampler.degree v.depth (d).keysBase).stop≤bound)
    (slab : ∀i : Key z (2^v.W) k,(((geo).outer phase trial).market.shelf.L v.sampler v.depth i).endAddress≤bound) :
    LinkOperands (repair C (.inner phase trial j t)).link W bound :=
  purchased_diagnostic_fits geo v.mesh P.catalogue G phase trial j t space core orig col cover keys slab

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
