import OAI.Hierarchy.ProbePaidForestInvoice
import OAI.Hierarchy.ProbeFixedOriginalPrice
import OAI.Hierarchy.ProbeFixedRowFaces
import OAI.Hierarchy.ProbePaidOriginalFaces
import OAI.Hierarchy.ProtocolRAMCatalystDateHeader
import OAI.Hierarchy.ProtocolRAMCatalystStripOwners

namespace OAI
/-! # Original metric charges on both true strip forest traversals -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets
open ReportSockets
open scoped Classical Fin.CommRing

variable {F : Type*} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "s" => v.located (v.seed P z width) P width
local notation "b" => P.catalogue
local notation "G" => P.routes
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
variable (π : Equiv.Perm (Fin (2^z))) (groups : Fin P.routes.oldGroups≃AllGroups z (2^v.W))
  (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z v.W (ReportSockets.copies k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))) P.routes.height)
  (bins : P.routes.bins=packed.groups)
  (keyBase : P.routes.directory.keysBase = P.routes.column + ColumnROM.words z (2^v.W) k)
  (order : Fin P.catalogue.coreRows≃Edges v.sampler z (2^v.W) k) (m : Memory (wordBits z (2^v.W) copies))

include bins in
omit [Nonempty (Fin k)] in
theorem payload_forest_invoice_of_fields (phase trial : ℕ)
    (tables : ColumnROM.Tables z v.W k n (G).column (G).directory.remapBase (G).directory.sitesBase
      (G).directory.superBase groups packed π m)
    (input : Native.Resident (Native.initialOutput z) m (fun u : Fin (2^z) => (π u).val))
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns z (2^v.W))≤2^W)
    (r : Fin (2^z)) (wide : 2^z≤2^W) (word : (b).rows<2^W)
    (mask : Marks z v.W k n)
    (shape : n*(count z (2^v.W) k*paths z v.sampler.degree v.depth)=(b).boughtRows) (positiveCore : 0<(b).coreRows)
    :
    let ord:=(b).ordinal v.sampler π v.depth mask order shape
    ((treeWalk s v.mesh b G (.outer phase trial) m r.val positiveCore).map
       (extendedLength ord (lenCode v.sampler π v.depth mask v.radius))).sum≤v.cost.atAttempt (.outer phase trial) := by
  intro ord
  obtain ⟨col,faces⟩:=v.payload_row_placement_of_fields P z width π groups packed bins order m
    tables input loaded columnsFit r wide
  have charge (f : Edges v.sampler z (2^v.W) k) :
      extendedLength ord (lenCode v.sampler π v.depth mask v.radius) ((b).coreIndex (order.symm f))=coreCode v.sampler v.radius f :=
    extendedLength_apply ord _ (.inl f)
  have bill:=original_tree_invoice (v.payloadPricePorts P z width) b order m r.val positiveCore word loaded
    (payloadPlace π r) col v.radius (fun e=>by
      obtain ⟨f,hit,metric,_⟩:=faces e none
      exact ⟨f,hit,metric.le.trans (by unfold PayloadStrip.length;split <;> norm_num)⟩)
    (extendedLength ord (lenCode v.sampler π v.depth mask v.radius)) charge
  change _≤(Fintype.card (Strip.TreeLink (PayloadStrip.edgeCount (publicStages v.W)) k):ℝ)*max (v.radius:ℝ) 1
  rw [←fixed_stage_count z v.W]
  exact bill

include bins in
omit [Nonempty (Fin k)] in
theorem payload_forest_invoice (phase trial : ℕ) (board : DatedBoard F s v.mesh b G π groups packed (.outer phase trial) m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns z (2^v.W))≤2^W)
    (r : Fin (2^z)) (wide : 2^z≤2^W) (word : (b).rows<2^W)
    (mask : Marks z v.W k n)
    (shape : n*(count z (2^v.W) k*paths z v.sampler.degree v.depth)=(b).boughtRows) (positiveCore : 0<(b).coreRows)
    :
    let ord:=(b).ordinal v.sampler π v.depth mask order shape
    ((treeWalk s v.mesh b G (.outer phase trial) m r.val positiveCore).map
       (extendedLength ord (lenCode v.sampler π v.depth mask v.radius))).sum≤v.cost.atAttempt (.outer phase trial) :=
  v.payload_forest_invoice_of_fields P z width π groups packed bins order m phase trial
    board.columns board.input loaded columnsFit r wide word mask shape positiveCore

include bins keyBase in
omit [Nonempty (Fin k)] in
theorem purchased_forest_invoice_of_fields (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (slice inner : ℕ)
    (tables : ColumnROM.Tables z v.W k n (G).column (G).directory.remapBase (G).directory.sitesBase
      (G).directory.superBase groups packed π m)
    (strata : (BoughtSockets.Public.keyHead (s).sampler (G).column z v.W k v.depth).Loaded m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns z (2^v.W))≤2^W)
    (marks : StageAt z (2^v.W)→(Fin k×Bool)→Finset (Fin (2^z)))
    (unique : ∀t j j' x,x∈marks t j→x∈marks t j'→j=j') (path : LiveChains v.sampler π v.depth marks)
    (records : (((s).outer phase trial).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (keyRoom : count z (2^v.W) k≤2^W) (tilesFit : (v.depth+1)*paths z v.sampler.degree v.depth≤2^W)
    (stageFit : N≤2^W) (degreeFit : v.sampler.degree≤2^W) (rowsFit : 2^z≤2^W)
    (capacity : ((G).directory.header z (2^v.W) k v.sampler.degree v.depth).count≤(b).boughtRows) (word : (b).rows<2^W)
    (mask : Marks z v.W k n)
    (shape : n*(count z (2^v.W) k*paths z v.sampler.degree v.depth)=(b).boughtRows) (positiveCore : 0<(b).coreRows)
    :
    let ord:=(b).ordinal v.sampler π v.depth mask order shape
    ((treeWalk s v.mesh b G (.inner phase trial slice inner) m (BoughtLocation.relative path).val positiveCore).map
       (extendedLength ord (lenCode v.sampler π v.depth mask v.radius))).sum≤v.cost.atAttempt (.inner phase trial slice inner) := by
  intro ord
  obtain ⟨col,faces,_⟩:=v.purchased_row_placement_of_fields P z width π groups packed bins keyBase order m phase trial
    tables strata loaded columnsFit marks unique path records keyRoom tilesFit stageFit degreeFit rowsFit capacity word
  have charge (f : Edges v.sampler z (2^v.W) k) :
      extendedLength ord (lenCode v.sampler π v.depth mask v.radius) ((b).coreIndex (order.symm f))=coreCode v.sampler v.radius f :=
    extendedLength_apply ord _ (.inl f)
  exact original_tree_invoice (v.purchasedPricePorts P z width phase trial) b order m (BoughtLocation.relative path).val
    positiveCore word loaded (retainedCol π marks path) col v.radius (fun e=>by
      obtain ⟨f,hit,metric,_⟩:=faces e none
      exact ⟨f,hit,metric.le.trans (by unfold ChainStrip.length;split <;> norm_num)⟩)
    (extendedLength ord (lenCode v.sampler π v.depth mask v.radius)) charge

include bins keyBase in
omit [Nonempty (Fin k)] in
theorem purchased_forest_invoice (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (slice inner : ℕ) (board : DatedBoard F s v.mesh b G π groups packed (.inner phase trial slice inner) m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns z (2^v.W))≤2^W)
    (marks : StageAt z (2^v.W)→(Fin k×Bool)→Finset (Fin (2^z)))
    (unique : ∀t j j' x,x∈marks t j→x∈marks t j'→j=j') (path : LiveChains v.sampler π v.depth marks)
    (records : (((s).outer phase trial).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (keyRoom : count z (2^v.W) k≤2^W) (tilesFit : (v.depth+1)*paths z v.sampler.degree v.depth≤2^W)
    (stageFit : N≤2^W) (degreeFit : v.sampler.degree≤2^W) (rowsFit : 2^z≤2^W)
    (capacity : ((G).directory.header z (2^v.W) k v.sampler.degree v.depth).count≤(b).boughtRows) (word : (b).rows<2^W)
    (mask : Marks z v.W k n)
    (shape : n*(count z (2^v.W) k*paths z v.sampler.degree v.depth)=(b).boughtRows) (positiveCore : 0<(b).coreRows)
    :
    let ord:=(b).ordinal v.sampler π v.depth mask order shape
    ((treeWalk s v.mesh b G (.inner phase trial slice inner) m (BoughtLocation.relative path).val positiveCore).map
       (extendedLength ord (lenCode v.sampler π v.depth mask v.radius))).sum≤v.cost.atAttempt (.inner phase trial slice inner) :=
  v.purchased_forest_invoice_of_fields P z width π groups packed bins keyBase order m phase trial slice inner
    board.columns board.strata loaded columnsFit marks unique path records keyRoom tilesFit stageFit degreeFit
    rowsFit capacity word mask shape positiveCore

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
