import OAI.Computability.BorderVNP.DiagonalSignedScheduleWords
import OAI.Computability.BorderVNP.DiagonalSignedRawWriterInput
import OAI.Computability.BorderVNP.DiagonalSignedWriterReceipt
import OAI.Computability.BorderVNP.DiagonalBootedProfilePublication

/-! # The public pin, actual raw declaration guards and the paid signed writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Crossing Packing CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.LabelIndex
open RoutingISA RoutingISA.Evaluator RoutingISA.LocalRow CubeHeaderInstall TeamContraction JointHeader ProcessorSlots VPVNP.BurstRAM
open Cube.MeanChoice Cube.Tally Directory.PrivateBank
open scoped Classical

set_option maxRecDepth 5500
set_option maxHeartbeats 2400000

/-- The measured label-directory memory realizes the specified common network rows and destinations. -/
def PublishedRowPlacement {w n c : ℕ} {P A : Type*} {bits : P → ℕ} (N : Network n P bits)
    (cell : N.Site → Fin c) (recv : A → Fin c) (size : A → ℕ) (frame : ℕ) (m : Memory w) : Prop :=
  let L := LabelIndex.layout frame (readings m)
  ∃ (cnt : L.cells=c) (ends : Endpoints L (readings m)) (cables : N.CrossingEdge cell ↪ Fin L.cableCount)
    (orders : A ≃ Fin L.deliveryCount), RowPlacement (networkRows N cell recv size) (fromTables L (readings m) ends)
       (finCongr cnt.symm) (cables.sumMap orders.toEmbedding)

/-- Only the rows stored in the compact native directory determine the
receiver and its size. This also covers live slots with a zero count. -/
private theorem align_directory_receivers {n c : ℕ} {P : Type*} {bits : P → ℕ} (N : Network n P bits)
    (cell : N.Site → Fin c) (native logical : List Directory.Row) (lab : LabelIndex.Layout)
    {mem : ℕ → ℕ} (ep : LabelIndex.Endpoints lab mem) (cells : lab.cells=c)
    (edges : N.CrossingEdge cell ↪ Fin lab.cableCount) (out : Fin native.length ≃ Fin lab.deliveryCount)
    (r : Fin native.length → Fin c) (s : Fin logical.length → Fin c)
    (rs : ∀ i,(r i).val=native[i.val].cell) (ss : ∀ i,(s i).val=logical[i.val].cell) (eqn : native=logical)
    (placed : RowPlacement (networkRows N cell r (fun i => native[i.val].width)) (fromTables lab mem ep)
      (finCongr cells.symm) (edges.sumMap out.toEmbedding)) :
    ∃ f : Fin logical.length ≃ Fin lab.deliveryCount, RowPlacement (networkRows N cell s (fun i => logical[i.val].width))
      (fromTables lab mem ep) (finCongr cells.symm) (edges.sumMap f.toEmbedding) := by
  subst logical
  have same : r=s := funext (fun i => Fin.ext ((rs i).trans (ss i).symm))
  exact ⟨out,same ▸ placed⟩

variable {w dim s p depth k b d : ℕ} (task : SignedTaskArena.Layout) (dir : Directory.Layout)
  (a : StartupArena) (u : Fin a.teams) (slot : ℕ) (packet : ReferencePacket w d) (other : Arg → Word w)
  (old : Fin 81 → Word w) (raw team subtotal fresh gates outputs width off ell origin gap : ℕ)
  (profile : List Bool) (claims : List (List Bool)) (pad : ℕ)
  (word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap)
  (R X : ℕ) (start : Memory w)
  {P : Type} [Fintype P] {bits : P → ℕ} (N : Network dim P bits) (cell : N.Site → Fin task.cube.cells)
  (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin p)
  {σ : Type*} [Fintype σ] (F : Fields s task.cube.cables p task.cube.cells depth k b σ) {x : σ → Bool}
  (original : Fin dir.entries → N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
  {ad : AdviceLayout} {f : BroadcastFrame}

local notation "ar" => SignedTaskArena.Layout.cube task
local notation "B" => a.operands u slot packet
local notation3 (prettyPrint := false) "pub" => (B).bank (core (withDemandBase (task.routeBank a.frame other) a.next)
  origin (ar).cables (ar).cells)
local notation3 (prettyPrint := false) "control" => controlsBase origin (ar).cables (ar).cells dir.entries (dir.teams*dir.sites)
local notation3 (prettyPrint := false) "loc" => privateLayout a.frame origin (ar).cables (ar).cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "tabs" => bases origin (ar).cables (ar).cells dir.entries
local notation3 (prettyPrint := false) "prev" => routingExtension (task.extension raw team subtotal old) dir origin (ar).cables (ar).cells
local notation3 (prettyPrint := false) "ext" => signedProfileExtension task old dir origin (ar).cables (ar).cells raw team subtotal
  fresh profile.length gates outputs width off ell
local notation3 (prettyPrint := false) "copy" => padded (spelling (profile++DeclarationBits.spelling word) claims) pad

local notation3 (prettyPrint := false) "supply" => Sum.elim (fun z : SuppliedWord N cell => z.1) (id : Fin task.cube.cells → Fin task.cube.cells)
local notation3 (prettyPrint := false) "sWidth" => Sum.elim (supplyWidth N cell) (fun _ : Fin task.cube.cells => gap)
local notation3 (prettyPrint := false) "sId" => reserveID (C := task.cube.cells) (suppliedID N cell edgeID portID)
local notation3 (prettyPrint := false) "host" => Sum.elim supply (cell ∘ original)
local notation3 (prettyPrint := false) "key" => numbered sId
local notation3 (prettyPrint := false) "sizes" => Sum.elim sWidth (fun _ : Fin dir.entries => dir.description)

variable (rep liveRep : ℕ → ℕ × ℕ)
    (ref : Directory.BankPlacement dir rep liveRep _ (Sum.elim (Sum.elim (fun z : SuppliedWord N cell => z.1) (id : Fin task.cube.cells → Fin task.cube.cells)) (cell ∘ original))
      (numbered (reserveID (C:=task.cube.cells) (suppliedID N cell edgeID portID)))
      (Sum.elim (Sum.elim (supplyWidth N cell) (fun _ : Fin task.cube.cells => gap)) (fun _ => dir.description)))
local notation3 (prettyPrint := false) "rr" => dir.directory rep liveRep
variable (recv : Fin (dir.directory rep liveRep).length → Fin task.cube.cells)
local notation3 (prettyPrint := false) "dataBits" => fun i : Fin (rr).length => (rr)[i.val].width
local notation3 (prettyPrint := false) "axis" => Fin.ofNat ((ar).n+1) (readCode ((ar).n+1) word.1)
local notation3 (prettyPrint := false) "decl" => Prod.mk axis (fun (p : Sym2 (Fin (ar).header.d)) (j : Fin ((ar).n+1)) =>
  readCode ((ar).header.cap+1) (word.2 p j))


/-- From the authenticated pin and directory return, run the selected raw declaration on the actual post-publication RAM. -/
theorem signed_published_row_input
    (net : CellAddressPhysical.Represents N cell aux siteID edgeID portID F x) (ids : ∀ c,(F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k≤b) (hb : b≤w) (positive : 0<(ar).cells)
    (liveWidth : ∀ q, bits (live q)=dir.block) (bounds : dir.DestinationBounds) (fields : 0<dir.fields)
    (tail : dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2))
    {g : ℕ} (v : Fin g → Bool) (mac : TeamOpcode.Macros w 8) (postPin : Bank w) (pinMem : Memory w) (preRegs : Bank w)
    (used profCost : ℕ) {field : Pins.ProcessorFields (B).layout}
    {initial : Memory w} {bank : Bank w} (kept : BootResidence (F:=field) a u slot packet f ad pub mac copy initial bank v start)
    (pubRun : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f copy field pub mac
      v postPin pinMem preRegs start used profCost)
    (installed : packet.extension=ext) (dst : f.dst=a.broadcastBase) (len : (copy).length=a.header) (operands : (B).Fits w)
    (img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings start))
    (gapControl : ∀ i : Fin 28, readings start (control+i.val)=task.controls i.val)
    (span : a.next+7*dir.candidates≤origin) (controlLo : control+28≤(ar).header.header)
    (dimension : dir.teams=(B).layout.teams ∧ dir.processors=(B).layout.processors ∧
      dir.literal=(B).layout.literal ∧ dir.link=(B).layout.link)
    (room : Directory.ISA.wordBound (Directory.ISA.placementBound dir (tabs).privatePairs (tabs).livePairs (ar).cellStride)<2^w)
    (sh : (ar).header=geometryInputs fresh profile.length gates outputs width w (ar).header.d (ar).n (ar).header.blocks (ar).b (ar).h (ar).s)
    (two : 2≤(ar).header.d) (replay : (ar).ReplayRoom w a.frame)
    (count : f.teams=R+1) (teams : (ar).teams=R+1) (budget : (prev 0).val=X)
    (million : 1000000<2^w) (scaled : 1000000*X*(R+1)<2^w)
    (proc : 0<dir.processors)
    (rawSpace : 1000000*((ar).stop+3*dir.teams*(dir.processors*dir.literal))+2*(ar).stop<2^w)
    {α ξ : ℝ} {n link : ℕ} (route : Diagonal.RouteTableInputs ar dir α ξ n w a.frame link)
    (envelope : LabelIndex.wordEnvelope (ar).alphabet (Diagonal.ExternalSew.intercellWidth N cell+
      dir.teams*((dir.fields+1)*(dir.processors*dir.literal))) < 2^w)
    (keys : ∀ j,ref.key j=j.elim Sum.inr (fun k => Sum.inl (Sum.inl (suppliedPort N cell (live k)))))
    (rcv : ∀ i,(recv i).val=(rr)[i.val].cell) :
    let label := meanPackedLabel N cell recv dataBits (List.finRange (ar).cells) (ar).n (ar).header.d (Nat.zero_lt_of_lt two)
    let mass := declarationWeight (ar).header.blocks (ar).b (ar).K (ar).h decl label recv dataBits
    let group := fun j : Fin (ar).header.d => TeamNative.owner R mass j.val
    let owner := fun c : ℕ => if h:c<(ar).cells then group (label ⟨c,h⟩ axis) else 0
    ∃ (epoch : Returns epochPlacement pub mac postPin pinMem)
      (published : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2) (mid : Memory w),
      epoch.val.2.2=mid ∧ published.val.2.2=Directory.ISA.publish mid (pub 0).val a.next rr ∧
      epoch.val.1.flatMap TeamRAM.Event.choices=[] ∧
      used+traceCost epoch.val.1+traceCost published.val.1 ≤ profCost+deliveryScanTicks dir.entries dir.teams dir.sites ∧
      ProfileRouteInputs field f pub (Pins.extendGuess v) published.val.2.2 ∧
      field.header.length=(pub 0).val ∧ (∀ count,TablePointers ((ar).table a.frame count) (readings published.val.2.2)) ∧
      Nonempty (SlottedWriter ar dir rep liveRep (B).layout pub mid a.next host key sizes) ∧
      SignedPrep.PinnedRawInput («ar»:=ar) (D:=dir) (pp:=rep) (lp:=liveRep) («pub»:=pub) (slotted:=mid) (base:=a.next)
        f prev fresh gates outputs width off ell control profile claims pad word R X ∧
      PublishedRowPlacement N cell recv dataBits (pub 0).val published.val.2.2 ∧
      (∃ scan : Returns (.seq PrivatePlacement.program Directory.ISA.program) pub mac preRegs start,
        scan.val.2=published.val.2 ∧ traceCost scan.val.1≤deliveryScanTicks dir.entries dir.teams dir.sites) ∧
      (declarationInRange word → broadcastAllowed R X (ar).header.blocks (ar).b (ar).K (ar).h label recv dataBits word →
      Nonempty (SignedPrep.HeaderWriterReceipt ar dir rep liveRep owner decl group (B).layout f pub mac
        published.val.2.1 published.val.2.2)) ∧
      let lab := LabelIndex.layout a.frame (readings published.val.2.2)
      lab.cells=(ar).cells ∧ lab.cableCount=(ar).cables ∧ lab.deliveryCount=(rr).length ∧ lab.labels=(ar).alphabet := by
  intro label mass group owner
  obtain ⟨epoch,published,mid,lastMem,epochAt,pubAt,empty,_,cost,memEq,fit,placed,sources,pins,header,pointers,
    ⟨writer,keyEq⟩,⟨number,ep,edges,del,rcv',values,traffic⟩,scan⟩ := pubRun
  obtain ⟨_,_,_,_,state,resident⟩ := kept
  have base : (pub 0).val=a.frame := (B).frameBase_word _ operands
  have rawInput := signed_raw_writer_input task dir a u slot packet other old raw team subtotal fresh gates
    outputs width off ell origin gap profile claims pad word R X start mid N cell aux siteID edgeID portID F original live
    (Pins.extendGuess v) net ids wireFit hk hb positive liveWidth bounds fields tail writer state resident installed dst len
    (memEq ▸ pins) operands img gapControl placed fit span controlLo dimension room sh two replay count teams budget million scaled proc
    rawSpace route envelope
  have same j := (keyEq j).trans (keys j).symm
  let originalData := dir.directory (Directory.ISA.placement (readings mid) (loc).raw)
    (Directory.ISA.placement (readings mid) (tabs).livePairs)
  have dataEq : originalData=rr := writer.placement.directory_eq ref same bounds
  have newMem : published.val.2.2 = Directory.ISA.publish mid (pub 0).val a.next rr := by
    rw [base,←dataEq]; exact pubAt.trans memEq
  let fixedWriter := writer.commonPlacement ref same
  have fixedInput := rawInput.commonPlacement dataEq
  obtain ⟨order,assigned⟩ := align_directory_receivers N cell _ _ _ ep number edges del rcv' recv values rcv dataEq traffic
  have canonical : PublishedRowPlacement N cell recv dataBits a.frame lastMem := ⟨number,ep,edges,order,assigned⟩
  have actual : PublishedRowPlacement N cell recv dataBits (pub 0).val published.val.2.2 := by
    rw [base,pubAt]; exact canonical
  have order := (ar).writer_order
  have first : origin ≤ control := by dsimp only [controlsBase,bases]; omega
  have headerBelow := (LocalRow.header_le_publicBase ar).trans (by omega : (ar).publicBase ≤ (ar).stop)
  have smallControl : control+8<2^w := (by omega : control+8<(ar).header.header).trans_le headerBelow |>.trans replay.stopFit
  obtain ⟨shape,_,_,_⟩ := signed_publication_fields task dir a u slot packet other old origin raw team subtotal fresh
    profile.length gates outputs width off ell (ar).cellStride (Pins.extendGuess v) installed smallControl (by omega : 1<2^w)
    bounds.fields replay.stopFit room operands state resident
  have low : a.frame+112 ≤ a.next := by unfold StartupArena.next StartupArena.hbase StartupArena.ibase StartupArena.broadcastBase StartupArena.dense; omega
  have pinWords : BootPins pub f ext copy (Directory.ISA.publish mid a.frame a.next rr) := by
    rw [←installed,←dataEq,←memEq]; exact pins
  have basedHeader : Header a.frame origin (ar).cables (ar).cells dir.entries (readings start) := by simpa only [base] using shape
  have dims := signed_published_label_layout task dir a.frame origin a.next gap start mid rep liveRep old raw team subtotal
    fresh profile.length gates outputs width off ell pub f copy base low span (by omega) (Nat.zero_lt_of_lt two)
    rawInput.blocks replay.stopFit basedHeader placed pinWords
  refine ⟨epoch,published,mid,epochAt,newMem,empty,cost,pubAt.symm ▸ sources,header,pubAt.symm ▸ pointers,
    ⟨fixedWriter⟩,fixedInput,actual,scan,?_,?_⟩
  swap
  · rw [newMem,base]
    exact dims
  intro valid allowed
  rw [newMem] at actual
  obtain ⟨_,_,_,_,rows⟩ := actual
  let result := SignedPrep.geometricHeaderReceipt (mac:=mac) (reg:=published.val.2.1) fixedWriter f prev fresh gates outputs
    width off ell control profile claims pad word fixedInput N cell recv dataBits rows valid allowed ref (fun _ => rfl)
    published.val.2.2 newMem
  exact ⟨result⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
