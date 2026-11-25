import OAI.Hierarchy.ProbeFixedForestTariffs
import OAI.Hierarchy.ProbePaidActualForest
import OAI.Hierarchy.ProbeSiteAddress
import OAI.Hierarchy.ProtocolRAMCatalystDateHeader
import OAI.Hierarchy.ProtocolRAMCatalystStripOwners

namespace OAI
/-! # Physical per-edge bandwidth of the original two strip forests -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open Probe Strip StockCommit
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets
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


/-- Two distinct original layers in the first exterior column supply a value
on vacant reporter entries. Paid tree rows always resolve to genuine edges. -/
private def vacant : LinearAlgebra.SpectralBooks.ChordGraph.Chord (siteLast z (2^v.W) k+1) :=
  let ν:=siteNumber z (2^v.W) k
  let left : Site z (2^v.W) k:=(.inl ⟨0,by positivity⟩,none)
  let right : Site z (2^v.W) k:=(left.1,some (Classical.arbitrary (Fin k),false))
  orderedEnds (ν left) (ν right) (ν.injective.ne (by
    intro equalSites
    have layers : (none : Option (Fin k × Bool)) = some (Classical.arbitrary (Fin k), false) :=
      congrArg (fun x : Site z (2^v.W) k => x.2) equalSites
    cases layers))

include bins in
theorem payload_forest_bandwidth_of_fields (phase trial : ℕ)
    (tables : ColumnROM.Tables z v.W k n (G).column (G).directory.remapBase (G).directory.sitesBase
      (G).directory.superBase groups packed π m)
    (input : Native.Resident (Native.initialOutput z) m (fun u : Fin (2^z) => (π u).val))
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns z (2^v.W))≤2^W)
    (wide : 2^z≤2^W) (word : (b).rows<2^W)
    (A : Area) (j : Fin (b).rows) (t : Traversals) (pos : 0<(b).coreRows)
    (copies maxBits : ℕ) (size : maxBits<2^W) (copySize : copies<2^W)
    (bounded : ∀i : Fin A.rows,(m (A.broadcast+i.val)).val≤ maxBits) (full : copies*maxBits<2^W)
    (room : 2^z≤A.rows)
    (head : t.Reads m (fun i : Fin A.rows=>treeWalk s v.mesh b G (.outer phase trial) m i.val pos))
    (live : ∀i : Fin A.rows,0<(m (A.broadcast+i.val)).val→i.val<2^z) :
    (PaidWidths.paidBroadcast A t.positions t.owner t.parity t.edge t.sourceRow copies maxBits).load m j≤
     (PayloadStrip.edgeCount N+(PayloadStrip.edgeCount N+1)*(k*2))*(copies*maxBits) := by
  let atRow : Fin (2^z) ↪ Fin A.rows:=⟨fun u=>u.castLE room,fun _ _ eq=>Fin.ext (congrArg (fun x : Fin A.rows => x.val) eq)⟩
  let ν:=(siteNumber z (2^v.W) k).toEmbedding
  let place:=(payloadSitesAll (d:=2^v.W) π k).trans ν
  have actual (u : Fin (2^z)):=v.payload_row_placement_of_fields P z width π groups packed bins order m
    tables input loaded columnsFit u wide
  refine actual_forest_from_reads (v.payloadPricePorts P z width) b A m pos order π ν (vacant v z) j atRow place
    (fun u c => payloadPlace (d := 2^v.W) π u c) (fun _ _=>rfl) loaded (fun u c=>(actual u).1 c)
    (fun u e => by
      obtain ⟨f, read, _, faces⟩ := (actual u).2 e none
      exact ⟨f, read, faces⟩)
    t head word copies maxBits size copySize bounded full ?_
  · exact fun i hi=>⟨⟨i.val,live i hi⟩,Fin.ext rfl⟩

include bins in
theorem payload_forest_bandwidth (phase trial : ℕ) (board : DatedBoard F s v.mesh b G π groups packed (.outer phase trial) m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns z (2^v.W))≤2^W)
    (wide : 2^z≤2^W) (word : (b).rows<2^W)
    (A : Area) (j : Fin (b).rows) (t : Traversals) (pos : 0<(b).coreRows)
    (copies maxBits : ℕ) (size : maxBits<2^W) (copySize : copies<2^W)
    (bounded : ∀i : Fin A.rows,(m (A.broadcast+i.val)).val≤ maxBits) (full : copies*maxBits<2^W)
    (room : 2^z≤A.rows)
    (head : t.Reads m (fun i : Fin A.rows=>treeWalk s v.mesh b G (.outer phase trial) m i.val pos))
    (live : ∀i : Fin A.rows,0<(m (A.broadcast+i.val)).val→i.val<2^z) :
    (PaidWidths.paidBroadcast A t.positions t.owner t.parity t.edge t.sourceRow copies maxBits).load m j≤
     (PayloadStrip.edgeCount N+(PayloadStrip.edgeCount N+1)*(k*2))*(copies*maxBits) :=
  v.payload_forest_bandwidth_of_fields P z width π groups packed bins order m phase trial
    board.columns board.input loaded columnsFit wide word A j t pos copies maxBits size copySize bounded full room head live

include bins keyBase in
theorem purchased_forest_bandwidth_of_fields (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (slice inner : ℕ)
    (tables : ColumnROM.Tables z v.W k n (G).column (G).directory.remapBase (G).directory.sitesBase
      (G).directory.superBase groups packed π m)
    (strata : (BoughtSockets.Public.keyHead (s).sampler (G).column z v.W k v.depth).Loaded m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns z (2^v.W))≤2^W)
    (marks : StageAt z (2^v.W)→(Fin k×Bool)→Finset (Fin (2^z)))
    (unique : ∀t j j' x,x∈marks t j→x∈marks t j'→j=j')
    (records : ∀ path : LiveChains v.sampler π v.depth marks,(((s).outer phase trial).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (keyRoom : count z (2^v.W) k≤2^W) (tilesFit : (v.depth+1)*paths z v.sampler.degree v.depth≤2^W)
    (stageFit : N≤2^W) (degreeFit : v.sampler.degree≤2^W) (rowsFit : 2^z≤2^W)
    (capacity : ((G).directory.header z (2^v.W) k v.sampler.degree v.depth).count≤(b).boughtRows) (word : (b).rows<2^W)
    (A : Area) (j : Fin (b).rows) (t : Traversals) (pos : 0<(b).coreRows)
    (copies maxBits : ℕ) (size : maxBits<2^W) (copySize : copies<2^W)
    (bounded : ∀i : Fin A.rows,(m (A.broadcast+i.val)).val≤ maxBits) (full : copies*maxBits<2^W)
    (room : count z (2^v.W) k * paths z v.sampler.degree v.depth≤A.rows)
    (head : t.Reads m (fun i : Fin A.rows=>treeWalk s v.mesh b G (.inner phase trial slice inner) m i.val pos))
    (live : ∀i : Fin A.rows,0<(m (A.broadcast+i.val)).val→
      ∃u : LiveChains v.sampler π v.depth marks,(BoughtLocation.relative u).val=i.val) :
    (PaidWidths.paidBroadcast A t.positions t.owner t.parity t.edge t.sourceRow copies maxBits).load m j≤
     (ChainStrip.edgeCount v.depth+(ChainStrip.edgeCount v.depth+1)*(k*2))*(copies*maxBits) := by
  let atRow : LiveChains v.sampler π v.depth marks ↪ Fin A.rows :=
    ⟨fun u=>(BoughtLocation.relative u).castLE room,fun _ _ eq=>
      BoughtLocation.relative_injective (Fin.ext (congrArg (fun x : Fin A.rows => x.val) eq))⟩
  let ν:=(siteNumber z (2^v.W) k).toEmbedding
  let place:=((allTreeSites v.sampler π v.depth marks unique).trans (stageSitesIntoPayload k)).trans ν
  have party (u : LiveChains v.sampler π v.depth marks) (x) :
      place (u,x)=ν (Prod.map (retainedCol π marks u) id x) := by
    change ν (stageSitesIntoPayload k (allTreeSites v.sampler π v.depth marks unique (u,x)))=_
    rw [allTreeSites_single]
    rfl
  have actual (u : LiveChains v.sampler π v.depth marks):=v.purchased_row_placement_of_fields P z width π groups packed bins keyBase order m
    phase trial tables strata loaded columnsFit marks unique u (records u) keyRoom tilesFit stageFit degreeFit rowsFit capacity word
  refine actual_forest_from_reads (v.purchasedPricePorts P z width phase trial) b A m pos order π ν (vacant v z) j atRow place
    (retainedCol π marks) party loaded (fun u c=>(actual u).1 c)
    (fun u e => by
      obtain ⟨f, read, _, faces⟩ := (actual u).2.1 e none
      exact ⟨f, read, faces⟩)
    t head word copies maxBits size copySize bounded full ?_
  · intro i hi
    obtain ⟨u,h⟩:=live i hi
    exact ⟨u,Fin.ext h⟩

include bins keyBase in
theorem purchased_forest_bandwidth (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (slice inner : ℕ) (board : DatedBoard F s v.mesh b G π groups packed (.inner phase trial slice inner) m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns z (2^v.W))≤2^W)
    (marks : StageAt z (2^v.W)→(Fin k×Bool)→Finset (Fin (2^z)))
    (unique : ∀t j j' x,x∈marks t j→x∈marks t j'→j=j')
    (records : ∀ path : LiveChains v.sampler π v.depth marks,(((s).outer phase trial).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (keyRoom : count z (2^v.W) k≤2^W) (tilesFit : (v.depth+1)*paths z v.sampler.degree v.depth≤2^W)
    (stageFit : N≤2^W) (degreeFit : v.sampler.degree≤2^W) (rowsFit : 2^z≤2^W)
    (capacity : ((G).directory.header z (2^v.W) k v.sampler.degree v.depth).count≤(b).boughtRows) (word : (b).rows<2^W)
    (A : Area) (j : Fin (b).rows) (t : Traversals) (pos : 0<(b).coreRows)
    (copies maxBits : ℕ) (size : maxBits<2^W) (copySize : copies<2^W)
    (bounded : ∀i : Fin A.rows,(m (A.broadcast+i.val)).val≤ maxBits) (full : copies*maxBits<2^W)
    (room : count z (2^v.W) k * paths z v.sampler.degree v.depth≤A.rows)
    (head : t.Reads m (fun i : Fin A.rows=>treeWalk s v.mesh b G (.inner phase trial slice inner) m i.val pos))
    (live : ∀i : Fin A.rows,0<(m (A.broadcast+i.val)).val→
      ∃u : LiveChains v.sampler π v.depth marks,(BoughtLocation.relative u).val=i.val) :
    (PaidWidths.paidBroadcast A t.positions t.owner t.parity t.edge t.sourceRow copies maxBits).load m j≤
     (ChainStrip.edgeCount v.depth+(ChainStrip.edgeCount v.depth+1)*(k*2))*(copies*maxBits) :=
  v.purchased_forest_bandwidth_of_fields P z width π groups packed bins keyBase order m
    phase trial slice inner board.columns board.strata loaded columnsFit marks unique records keyRoom tilesFit
    stageFit degreeFit rowsFit capacity word A j t pos copies maxBits size copySize bounded full room head live

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
