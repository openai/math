import OAI.Computability.BorderVNP.DiagonalFrozenPaddingControls
import OAI.Computability.BorderVNP.DiagonalCandidateIntervalRows
import OAI.Computability.BorderVNP.DiagonalSignedCandidateCubeWords
import OAI.Computability.BorderVNP.DiagonalSignedPublishedHostPointers
import OAI.Computability.BorderVNP.DiagonalPublishedHostCables
import OAI.Computability.BorderVNP.DiagonalNativeOriginalDirectory
import OAI.Computability.BorderVNP.PackedNativeDemandBundleHeader

/-! # The control return equation on the actual signed candidate writers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube Physical Scatter TeamRows DiagonalTallyPacketEmit FiniteEvaluator Evaluator
open BorderVNP.Crossing Packing CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs
open NativeIntervals HostAddress VPVNP.MotifBase Diagonal.ExternalSew
open BottomReports BundleSort Diagonal.ExternalSew.FieldExport

open MeanChoice LabelIndex RoutingOutputs.NativeDemands LocalRow CubeHeaderInstall
open PackedHistoryCircuit Evaluator.SignedPrep Cube.HostScatter
open scoped Classical

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
    {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
    (task : SignedTaskArena.Layout)
    {group : Fin task.cube.header.d → Fin (R+1)}
    {F : TeamRows.Returns (Fin (R+1)) task.cube w}
    {owners : (Packet task.cube.n task.cube.header.d task.cube.header.blocks → Selector task.cube.n task.cube.K task.cube.h) →
      Fin task.cube.header.d → Fin (R+1)}
    {template : Frame} {id : TableEntry task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s → ℕ} {count : ℕ}


variable {dim sites ports cellBits lenBits geometryBits geoOrigin next gap bankBits broadcast frame X : ℕ}
    {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ} (N : Network dim P bits) (cell : N.Site → Fin task.cube.cells)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin sites) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin ports)
    (fields : Fields sites task.cube.cables ports task.cube.cells cellBits lenBits geometryBits σ)
    (x : Fin (R+1) → σ → Bool) (original : Fin D.entries ↪ N.Site) (live : (Fin D.teams × Fin D.sites) ↪ P)
    (bounds : D.DestinationBounds) (shape : Fin D.entries → BottomReports.BundleSort.Shape)
    (valid : VPVNP.VerifierNetwork.Frame σ Unit) (raw : Broadcast task.cube.n task.cube.header.d task.cube.header.cap)
    (hd : 0<task.cube.header.d)
local notation3 (prettyPrint := false) "ar" => task.cube
local notation3 (prettyPrint := false) "decl" => Prod.mk (Fin.ofNat ((ar).n+1) (readCode ((ar).n+1) raw.1))
  (fun (p : Sym2 (Fin (ar).header.d)) (j : Fin ((ar).n+1)) => readCode ((ar).header.cap+1) (raw.2 p j))
local notation3 (prettyPrint := false) "ls" => NativeDemands.rows N cell edgeID portID D original live gap
local notation3 (prettyPrint := false) "receiver" => NativeDemands.receiver N cell edgeID portID D original live gap bounds
local notation3 (prettyPrint := false) "widths" => fun i : Fin (ls).length => (ls)[i.val].width
local notation3 (prettyPrint := false) "labels" => meanPackedLabel N cell receiver widths (List.finRange (ar).cells) (ar).n (ar).header.d hd
local notation3 (prettyPrint := false) "ord" => NativeDemands.cableOrder N cell edgeID
local notation3 (prettyPrint := false) "tables" => bases geoOrigin (ar).cables (ar).cells D.entries
local notation3 (prettyPrint := false) "ctrl" => controlsBase geoOrigin (ar).cables (ar).cells D.entries (D.teams*D.sites)
local notation3 (prettyPrint := false) "pr" => privateLayout frame geoOrigin (ar).cables (ar).cells D.entries D.description gap
local notation3 (prettyPrint := false) "il" => signedChooserLayout (ar) frame geoOrigin
local notation3 (prettyPrint := false) "banks" => (ar).cellWriter frame ctrl (decl).1
local notation3 (prettyPrint := false) "headers" => geometryHeaders fields (siteID ∘ original) D.description (bankConfig banks gap valid) shape
local notation3 (prettyPrint := false) "oldPtrs" => siteID ∘ original
local notation3 (prettyPrint := false) "livePtrs" => portID ∘ live ∘ finProdFinEquiv.symm

variable {I : Type} [Fintype I] {host : I → Fin task.cube.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    {F₀ : (u : Fin (R+1)) → Pins.ProcessorFields (pins u)} (bf : Fin (R+1) → BroadcastFrame)
    {guess : Fin (R+1) → ℕ → Bool} {reg : Fin (R+1) → Bank w} {mem : Fin (R+1) → Memory w}
    (site : ∀ u, CandidateSite (X:=X) task.cube D pp lp raw owner
       (Prod.mk (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) raw.1))
         (fun (p : Sym2 (Fin task.cube.header.d)) (j : Fin (task.cube.n+1)) => readCode (task.cube.header.cap+1) (raw.2 p j))) group frame next (pins u) (F₀ u) (bf u) (guess u)
      (H u).pub (H u).macros (reg u) (mem u) host key sizes N cell (NativeDemands.receiver N cell edgeID portID D original live gap bounds)
        (fun i : Fin (NativeDemands.rows N cell edgeID portID D original live gap).length =>
            (NativeDemands.rows N cell edgeID portID D original live gap)[i.val].width))
local notation3 (prettyPrint := false) "W(" u ")" => (site u).receipt.history
local notation3 (prettyPrint := false) "before(" u ")" => (site u).geometry
local notation3 (prettyPrint := false) "mid(" u ")" => (site u).middle
local notation3 (prettyPrint := false) "published(" u ")" => (site u).published.val.2.2
local notation3 (prettyPrint := false) "dir(" u ")" => readings (site u).receipt.labeling.val.2.2
local notation3 (prettyPrint := false) "rawP(" u ")" => Directory.ISA.placement (readings (mid(u))) (pr).raw
local notation3 (prettyPrint := false) "liveP(" u ")" => Directory.ISA.placement (readings (mid(u))) (tables).livePairs
local notation3 (prettyPrint := false) "hdr(" u ")" => fun i : Fin D.entries =>
  geometryHeader (Retains.id N) siteID fields (x:=x u) pr (readings (W(u)).dataInput) (ar).hostDirectory original i
    (shape i).copies (shape i).fine (shape i).incoming (shape i).cap

local notation3 (prettyPrint := false) "reported" => fun j : Fin D.entries => (shape j).header
  ((ar).cellBank+(cell (original j)).val*(ar).cellStride+
    (NativeDemands.destination N cell edgeID portID D original live gap (.inl j)).2)
  (siteBase N cell (cell (original j)) siteID aux ⟨original j,rfl⟩)

set_option maxRecDepth 8000
set_option maxHeartbeats 3500000

/-- The joint owned return on the true per-team candidate site has exactly
the padding test of the frozen packet. Its actual pre-interval memory is
recovered from the executed chooser rather than chosen as an extra column. -/
theorem SharedWriters.candidate_control_tests (writer : SharedWriters f g src)
    (q : NativeAssignments.Routed (b:=(ar).b) (s:=(ar).s) owners)
    (symbols : SymbolFrame g (src anchor) (ar).header.blocks (ar).K (ar).h decl group)
    (handoff : OwnedHandoff f g src (ar) decl group template id count F)
    (receipt : ObservedOwned (ar) decl group F owners (f.receivedRows g group) q)
    (common : D.directory pp lp=ls) (shared : ∀ u,src u=readings (W(u)).sharedInput)
    (old : Fin (R+1) → Fin 81 → Word w) (pinned subtotal : ℕ)
    (literal : ∀ u,(site u).old = routingExtension (task.extension pinned (bf u).team subtotal (old u))
      D geoOrigin (ar).cables (ar).cells)
    (address : ∀ u,(site u).control=ctrl) (copyAt : ∀ u,(bf u).dst=broadcast)
    (net : ∀ u, Represents N cell aux siteID edgeID portID fields (x u)) (codes : ∀ c,(fields.cells c).val=c.val)
    (fieldRoom : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^geometryBits)
    (hk : lenBits≤geometryBits) (wordFit : geometryBits≤w) (positive : 0<(ar).cells)
    (liveWidth : ∀ j, bits (live j)=D.block)
    (img : ∀ u, Image fields oldPtrs livePtrs (x u) geoOrigin (readings (before(u))))
    (placement : ∀ u,(pr).Image (readings (before(u))) D.entries (readings (mid(u))))
    (privateRoom : ∀ u,(pr).Fits w (readings (before(u))))
    (head : ∀ u, Header frame geoOrigin (ar).cables (ar).cells D.entries (readings (before(u))))
    (nativeW : ∀ u, Nonempty (SlottedWriter (ar) D (rawP(u)) (liveP(u)) (pins u) (H u).pub (mid(u)) next host key sizes))
    (scratch : next+7*D.candidates≤geoOrigin) (originFit : geoOrigin<2^w)
    (teams : D.teams≤2^w) (procs : D.processors≤2^w) (fieldFit : D.fields≤2^w) (lit : D.literal<2^w)
    (cells : (ar).cells≤2^w) (strideFit : (ar).cellStride≤2^w)
    (room : task.OpenRoom frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites) D.entries (2^bankBits) w)
    (payload : ctrl ≤ task.p.bundlePayload) (rank : task.p.bundleInverse=task.p.bundlePayload+2^bankBits)
    (ctrlFit : ∀ i : Fin 37,task.controls i.val < 2^geometryBits)
    (boot : ∀ u, task.OpenFields u.val frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites) D.entries
      (readings (before(u))))
    (keysFit : (ar).cells < 2^lenBits) (descFit : D.description < 2^geometryBits)
    (scanFit : 2^Nat.clog 2 D.entries*D.description < 2^geometryBits)
    (copies : ∀ i,(shape i).copies < 2^geometryBits)
    (strides : ∀ i,bottomStride ((shape i).fine+(shape i).incoming) (shape i).cap < 2^geometryBits)
    (capacity : ∀ c,suppliedSize N cell c+gap+Directory.DataSlabs.size (cell ∘ original) (fun _ => D.description) c ≤ (ar).cellStride)
    (controls : ∀ u (i : Fin 37),readings (before(u)) (ctrl+i.val)=task.controls i.val)
    (sorted : ∀ u (j : Fin (2^bankBits+2^bankBits)),readings (before(u)) (task.p.bundlePayload+j.val)=
      ParseBatchSort.value (fun v => (CellPacketGeometry.geometry (source (ar).cells bankBits headers)).eval (x u) (.inl (j,v))))
    (packing : ∀ v,load (cablePair ord (crossSrc N cell) (crossDst N cell) labels)
      (crossWidth N cell ∘ (ord).symm) v ≤ (ar).header.blocks*((ar).h*(ar).b)) :
    let prog := fun u : Fin (R+1) => task.openInputs u.val frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites)
      D.entries bankBits (cell ∘ original) reported
    OpenSuffix.ControlFamily prog F.pub F.macros F.finalRegs F.output
      (NativeAssignments.RoutedPins N cell owners (packedSlotEmbedding N cell ord labels (ar).header.blocks ((ar).h*(ar).b) packing) q) ∧
    ∀ u,FrozenControlReadback task (prog u) u.val frame (F.pub u 0).val ctrl (tables).ends (tables).livePairs
      (D.teams*D.sites) D.entries (D.directory pp lp).length w (fun c => suppliedSize N cell c)
      (readings (W(u)).dataInput) (readings (F.output u)) := by
  let mid := fun u => (site u).middle
  let before := fun u => (site u).geometry
  have below : geoOrigin+3*(ar).cables≤(ar).header.header := by
    have bound := room.controlEnd
    dsimp only [controlsBase,bases] at bound
    omega
  have scan (u : Fin (R+1)) :
      ∃ m : Memory w, (il).Image (readings m) (il).count (dir(u)) ∧ (il).Fits w (readings m) ∧
      (il).Fields (readings m) ∧ CableColumns (ar) frame il (readings m) ∧
      (∀ z<(ar).publicBase, dir(u) z=readings (published(u)) z) ∧
      ∃ row : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin (ar).cables,
        (∀ e,row (ord e)=edgeID e.val) ∧ PhysicalRows N cell il (readings m) ord row Fin.valEmbedding labels
          (productCode (ar).n (ar).header.d (ar).alphabet rfl) := by
    have frameAt := (site u).origin
    have start := candidate_interval_rows (ar) D N cell aux siteID edgeID portID fields (x u) (net u) codes fieldRoom
      hk wordFit positive original live liveWidth bounds (H u).pub next geoOrigin gap raw (site u) common
      (by simpa only [frameAt] using (nativeW u).some) (img u) (by simpa only [frameAt] using placement u)
      (by simpa only [frameAt] using privateRoom u) (by simpa only [frameAt] using head u) scratch originFit teams procs fieldFit lit cells strideFit below
    obtain ⟨m,im,fit,fields₀,space,lower,row,aligned,physical⟩ := start
    let exactRows (h : ℕ) := PhysicalRows N cell (signedChooserLayout (ar) h geoOrigin) (readings m) ord row
      Fin.valEmbedding labels (productCode (ar).n (ar).header.d (ar).alphabet rfl)
    exact ⟨m,by simpa only [frameAt] using im,by simpa only [frameAt] using fit,by simpa only [frameAt] using fields₀,
      by simpa only [frameAt] using space,lower,row,aligned,Eq.mp (congrArg exactRows frameAt) physical⟩
  choose prev im fits phys space low row aligned rows using scan
  have entered (u : Fin (R+1)) : published(u)=Directory.ISA.publish (mid u) frame next (D.directory pp lp) := by
    simpa only [(site u).origin] using (site u).actual
  have native (u : Fin (R+1)) : NativeEntry (ar) frame ctrl (decl).1 R
      (powerHeaderImage (ar) broadcast (dir(u))) (readings (Directory.ISA.publish (mid u) frame next (D.directory pp lp)))
      (readings (W(u)).dataInput) := by
    have input := (site u).input
    rw [literal u] at input
    have out := (site u).receipt.native_entry task (site u).placement (bf u) (old u) geoOrigin (ar).cables (ar).cells
      pinned subtotal (site u).fresh (site u).gates (site u).outputs (site u).width (site u).off (site u).ell
      (site u).control (site u).profile (site u).claims (site u).pad raw (site u).actual input
    simpa only [(site u).origin,address u,copyAt u,entered u] using out
  have pointers (u : Fin (R+1)) := (site u).input.signed_host_pointers
  have first : frame+112≤next := by simpa only [(site anchor).origin] using (site anchor).placement.rawStart
  have normal (u : Fin (R+1)) : hdr(u)=reported := by
    funext j
    have actualNative := native u
    have retained := actualNative.original_directory D pp lp (mid u) first scratch (by have := room.controlEnd; omega)
    exact NativeDemands.placed_bundle_header N cell aux siteID edgeID portID D original live gap fields (x u) (net u)
      codes fieldRoom frame geoOrigin (ar).hostDirectory (ar).cellBank (ar).cellStride w (readings (before u))
      (readings (mid u)) (readings (W(u)).dataInput) shape liveWidth (img u) (placement u) (privateRoom u) retained.1
      retained.2 j
  have observed := writer.frozen_control_tests_at task N cell aux siteID edgeID portID fields original (live ∘ finProdFinEquiv.symm)
    shape valid il (fun u => readings (prev u)) (fun u => dir(u)) rows im packing before mid x (fun u => published(u))
    (fun u => W(u)) symbols handoff receipt entered (fun u => (site u).receipt.done.emission.demand.ready)
    (fun u => (site u).receipt.done.emission.demand.records) shared fits phys (fun u => (site u).origin.symm) space rfl
    (fun u k hk => by simpa only [signedChooserLayout,entered u] using low u k hk) native
    (fun u => by simpa only [signedChooserLayout,(site u).origin] using pointers u) net codes fieldRoom
    (fun u => published_routing_header pp lp
      (placement u) (head u) first scratch) img room first scratch payload rank ctrlFit boot placement hd keysFit descFit
    scanFit copies strides capacity controls sorted

  let sourceProg := fun u : Fin (R+1) => task.openInputs u.val frame (tables).ends ctrl (tables).livePairs
    (D.teams*D.sites) D.entries bankBits (cell ∘ original) (hdr(u))
  let actualProg := fun u : Fin (R+1) => task.openInputs u.val frame (tables).ends ctrl (tables).livePairs
    (D.teams*D.sites) D.entries bankBits (cell ∘ original) reported
  have same : sourceProg=actualProg := funext fun u => congrArg (task.openInputs u.val frame (tables).ends ctrl
    (tables).livePairs (D.teams*D.sites) D.entries bankBits (cell ∘ original)) (normal u)
  let result := fun (prog : Fin (R+1) → OpenSuffix.Inputs) =>
    OpenSuffix.ControlFamily prog F.pub F.macros F.finalRegs F.output
        (NativeAssignments.RoutedPins N cell owners (packedSlotEmbedding N cell ord labels (ar).header.blocks ((ar).h*(ar).b) packing) q) ∧
      ∀ u,FrozenControlReadback task (prog u) u.val frame (F.pub u 0).val ctrl (tables).ends (tables).livePairs
        (D.teams*D.sites) D.entries (D.directory pp lp).length w (fun c => suppliedSize N cell c)
        (readings (W(u)).dataInput) (readings (F.output u))
  exact Eq.mp (congrArg result same) observed

end TeamContraction

end BorderVNP
end Computability
end OAI
