import OAI.Hierarchy.TaggedWireEarnedReads
import OAI.Hierarchy.TaggedWireEarnedTender
import OAI.Hierarchy.TaggedWireEarnedSites

namespace OAI
/-! Earned-role operands of the actual selected native calendar rows. -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Strip
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets PurchaseStage
open WireTelescope.ChosenPackets.RowRouting LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical Fin.CommRing

private theorem purchase_site_number {h d k depth : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (mark : StageAt h d → (Fin k × Bool) → Finset (Fin (2^h)))
    (unique : ∀ t j j' x, x ∈ mark t j → x ∈ mark t j' → j = j')
    (path : LiveChains S π depth mark) (x : ColumnSite (ChainStrip.Columns depth) k) :
    SiteDirectory.boughtParties (depth:=depth) π S mark unique (path,x) =
      siteNumber h d k (Prod.map (retainedCol π mark path) _root_.id x) :=
  congrArg (fun y : ColumnSite (StageColumns h d) k => siteNumber h d k (stageSitesIntoPayload k y))
    (allTreeSites_single S π depth mark unique path x)

variable {F : Type} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (h width : ℕ)
local notation "W" => wordBits h (2^v.W) copies
local notation "N" => Stages h (2^v.W)
local notation "s" => v.located (v.seed P h width) P width
local notation "name" => (siteNumber h (2^v.W) k).toEmbedding
variable (π : Equiv.Perm (Fin (2^h))) (groups : Fin P.routes.oldGroups≃AllGroups h (2^v.W))
  (packed : TaggedShorterSupergroups.Directory
    (TaggedShorterSupergroups.reserved h v.W (ReportSockets.copies k
      ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))) P.routes.height)
  (bins : P.routes.bins=packed.groups)
  (keyBase : P.routes.directory.keysBase = P.routes.column + ColumnROM.words h (2^v.W) k)
  (order : Fin P.catalogue.coreRows≃Edges v.sampler h (2^v.W) k)
  (m : Memory (Native.wordBits h (2^v.W) Native.copies))
  (marks : ReportSockets.Marks h v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
  (capacity : (P.routes.directory.header h (2^v.W) k v.sampler.degree v.depth).count=P.catalogue.boughtRows)
  (loaded : CoreLookup.Loaded P.routes.core order m)
  (cols : Fintype.card (Columns h (2^v.W))≤2^(Native.wordBits h (2^v.W) Native.copies))
  (rows : 2^h≤2^(Native.wordBits h (2^v.W) Native.copies))
  (catalogueRoom : P.catalogue.rows<2^(Native.wordBits h (2^v.W) Native.copies))
local notation "endRow" => P.catalogue.physicalEnds (π:=π) (marks:=marks) P.routes.directory order capacity

include bins loaded cols rows catalogueRoom in
def widePayloadInstall (phase trial : ℕ) (r : Fin (2^h))
    (board : DatedBoard (z:=h) («W»:=v.W) (k:=k) (depth:=v.depth) F s v.mesh P.catalogue P.routes
      π groups packed (.outer phase trial) m) :
    EarnedInstall (sam:=v.sampler) (h:=h) (d:=2^v.W) (k:=k) (n:=PayloadStrip.edgeCount N)
      (K:=siteLast h (2^v.W) k+1) (w:=W) (A:=PayloadStrip.Quotes N k) (B:=Empty) (Ball:=Fin (2^h))
      (v.payloadPricePorts P h width) P.catalogue π
      (LocalCommodity.extraEnds (PayloadStrip.commodity N k) (PayloadStrip.noProbe N))
      (SiteDirectory.payloadParties (d:=2^v.W) (k:=k) π) r endRow name (PayloadStrip.rowAddress r) m (r.val:Word W) where
  lookup:=order
  loaded:=loaded
  wide:=catalogueRoom
  col:=payloadPlace (d:=2^v.W) π r
  placed:=by
    have actual := v.payload_earned_placement P h width π groups packed bins order m marks capacity
      phase trial board loaded cols r rows catalogueRoom
    exact actual
  core:=P.catalogue.physicalEnds_core (π:=π) (marks:=marks) P.routes.directory order capacity
  mapped:=fun _=>rfl
  goods:=earned_payload_goods (h:=h) (d:=2^v.W) (k:=k) π r

section Purchased
variable (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel) (slice inner : ℕ)
local notation "born" => finProdFinEquiv (phase,trial)
variable (unique : ∀ (t : StageAt h (2^v.W)) (j j' : Fin k×Bool) (x : Fin (2^h)),
    x∈marks (finProdFinEquiv (phase,trial)) t j→x∈marks (finProdFinEquiv (phase,trial)) t j'→j=j')
  (path : LiveChains v.sampler π v.depth (marks (finProdFinEquiv (phase,trial))))
include bins keyBase loaded cols rows catalogueRoom in
def widePurchaseInstall
    (board : DatedBoard (z:=h) («W»:=v.W) (k:=k) (depth:=v.depth) F s v.mesh P.catalogue P.routes
      π groups packed (.inner phase trial slice inner) m)
    (records : (((s).outer phase trial).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (keyFit : count h (2^v.W) k≤2^W) (tilesFit : (v.depth+1)*paths h v.sampler.degree v.depth≤2^W)
    (stageFit : N≤2^W) (degreeFit : v.sampler.degree≤2^W) :
    EarnedInstall (sam:=v.sampler) (h:=h) (d:=2^v.W) (k:=k) (n:=ChainStrip.edgeCount v.depth)
      (K:=siteLast h (2^v.W) k+1) (w:=W) (A:=ChainStrip.Axes v.depth k) (B:=Unit)
      (Ball:=LiveChains v.sampler π v.depth (marks born)) (v.purchasedPricePorts P h width phase trial) P.catalogue π
      (LocalCommodity.extraEnds (ChainStrip.commodity v.depth k) (ChainStrip.probe v.depth))
      (SiteDirectory.boughtParties (depth:=v.depth) π v.sampler (marks born) unique) path endRow name
      (stripAddress v.sampler π v.depth (marks born) path) m ((BoughtLocation.relative path).val:Word W) where
  lookup:=order
  loaded:=loaded
  wide:=catalogueRoom
  col:=retainedCol π (marks born) path
  placed:=v.purchased_earned_placement P h width π groups packed bins keyBase order m marks capacity phase trial
    slice inner board loaded cols unique path records keyFit tilesFit stageFit degreeFit rows catalogueRoom
  core:=P.catalogue.physicalEnds_core (π:=π) (marks:=marks) P.routes.directory order capacity
  mapped:=purchase_site_number v.sampler π (marks born) unique path
  goods:=earned_purchase_goods (h:=h) (d:=2^v.W) (k:=k) π v.sampler v.depth (marks born) path
end Purchased

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
