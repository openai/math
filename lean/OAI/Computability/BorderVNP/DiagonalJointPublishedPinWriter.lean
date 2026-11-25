import OAI.Computability.BorderVNP.DiagonalJointPrefixAdmission
import OAI.Computability.BorderVNP.PackedNativeDemandPlacement

/-! # The admitted writer and scan on the published pin of a joint return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Crossing Packing CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.LabelIndex Cube.MeanChoice Cube.Tally Directory.PrivateBank
open RoutingISA RoutingISA.Evaluator RoutingISA.LocalRow CubeHeaderInstall TeamContraction JointHeader ProcessorSlots VPVNP.BurstRAM
open RoutingISA.CompactMachine
open scoped Classical

set_option maxRecDepth 6000
set_option maxHeartbeats 2400000

variable {w dim s p depth k b d : ℕ} (task : SignedTaskArena.Layout) (dir : Directory.Layout)
  (a : StartupArena) (u : Fin a.teams) (slot : ℕ) (packet : ReferencePacket w d) (other : Arg → Word w)
  (old : Fin 81 → Word w) (raw team subtotal fresh gates outputs width off ell origin gap : ℕ)
  (profile : List Bool) (claims : List (List Bool)) (pad : ℕ)
  (word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap)
  {R : ℕ} (X : ℕ)
  {P : Type} [Fintype P] {bits : P → ℕ} (N : Network dim P bits) (cell : N.Site → Fin task.cube.cells)
  (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin p)
  {σ : Type*} [Fintype σ] (F : Fields s task.cube.cables p task.cube.cells depth k b σ) {x : σ → Bool}
  (original : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
  (liveWidth : ∀ q, bits (live q)=dir.block) (bounds : dir.DestinationBounds) {ad : AdviceLayout}

local notation "ar" => SignedTaskArena.Layout.cube task
local notation "B" => a.operands u slot packet
local notation3 (prettyPrint := false) "installedPub" => (B).bank (core (withDemandBase (task.routeBank a.frame other) a.next)
  origin (ar).cables (ar).cells)
local notation3 (prettyPrint := false) "control" => controlsBase origin (ar).cables (ar).cells dir.entries (dir.teams*dir.sites)
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

local notation3 (prettyPrint := false) "rep" => NativeDemands.privatePair N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "liveRep" => NativeDemands.livePair N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "rr" => NativeDemands.rows N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "recv" => NativeDemands.receiver N cell edgeID portID dir original live gap bounds
local notation3 (prettyPrint := false) "dataBits" => fun i : Fin (rr).length => (rr)[i.val].width
local notation3 (prettyPrint := false) "axis" => Fin.ofNat ((ar).n+1) (readCode ((ar).n+1) word.1)
local notation3 (prettyPrint := false) "decl" => Prod.mk axis (fun (p : Sym2 (Fin (ar).header.d)) (j : Fin ((ar).n+1)) =>
  readCode ((ar).header.cap+1) (word.2 p j))

variable {r t link inner n : ℕ} {Edge : Type} {machine : Wiring R r t d link inner n Edge}
    {pubs : Fin (R+1) → Arg → Word w} {regs : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
    {col : Fin d → Bool} {wire : Exterior R r link → Bool}
    (index : TableEntry task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s → ℕ)
    (crew : ∀ i, BootedPinStart SparseExterior.driver machine pubs regs args col wire i)
    (tuple : PinStart.JointPrefix index (fun i => (crew i).start)) (i : Fin (R+1))
local notation3 (prettyPrint := false) "lib" => install SparseExterior.driver n (crew i).start.routines
local notation3 (prettyPrint := false) "f₀" => machine.transferFrame i (args i).header (args i).dst
local notation3 (prettyPrint := false) "initial" => processorMemory
  (machine.processorFields i col wire (args i).ibase (args i).hbase (args i).starbase) w
local notation3 (prettyPrint := false) "Full" => Returns (withStartup pinGeometry) (pubs i) lib (regs i) initial
local notation3 (prettyPrint := false) "sub" => (tuple i).1
local notation3 (prettyPrint := false) "pinRun" => (crew i).pins sub
local notation3 (prettyPrint := false) "used" => (crew i).used+traceCost (pinRun).val.1

include liveWidth in
/-- The actual booted pin and its seven-word directory scan suffice for admission.
The returned writer and its charge use the same output registers and memory as
that scan, starting at the dictionary entry of the original prefix. -/
theorem joint_published_pin_writer
    (net : CellAddressPhysical.Represents N cell aux siteID edgeID portID F x) (ids : ∀ c,(F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k≤b) (hb : b≤w) (positive : 0<(ar).cells)
    (fields : 0<dir.fields)
    (tail : dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2))
    {pf : Pins.ProcessorFields (B).layout}
    (pubEq : pubs i=installedPub)
    (paths : (Fin (crew i).start.guessWidth → Bool) ≃ Full)
    (spells : ∀ v,(paths v).val.1.flatMap TeamRAM.Event.choices=List.ofFn v)
    (ret : Full) (digits : ret.val.1.flatMap TeamRAM.Event.choices=List.ofFn sub)
    (kept : BootResidence (F:=pf) a u slot packet f₀ ad (pubs i) lib copy initial (regs i) sub ret.val.2.2)
    (pubRun : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f₀ copy pf (pubs i) lib
      sub (pinRun).val.2.1 (pinRun).val.2.2 ret.val.2.1 ret.val.2.2 used (traceCost ret.val.1))
    (installed : packet.extension=ext) (dst : (f₀).dst=a.broadcastBase) (len : (copy).length=a.header) (operands : (B).Fits w)
    (img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings ret.val.2.2))
    (gapControl : ∀ i : Fin 28, readings ret.val.2.2 (control+i.val)=task.controls i.val)
    (span : a.next+7*dir.candidates≤origin) (controlLo : control+28≤(ar).header.header)
    (dimension : dir.teams=(B).layout.teams ∧ dir.processors=(B).layout.processors ∧
      dir.literal=(B).layout.literal ∧ dir.link=(B).layout.link)
    (room : Directory.ISA.wordBound (Directory.ISA.placementBound dir (tabs).privatePairs (tabs).livePairs (ar).cellStride)<2^w)
    (sh : (ar).header=geometryInputs fresh profile.length gates outputs width w (ar).header.d (ar).n (ar).header.blocks (ar).b (ar).h (ar).s)
    (two : 2≤(ar).header.d) (replay : (ar).ReplayRoom w a.frame)
    (teams : (ar).teams=R+1) (budget : (prev 0).val=X)
    (million : 1000000<2^w) (scaled : 1000000*X*(R+1)<2^w)
    (proc : 0<dir.processors)
    (rawSpace : 1000000*((ar).stop+3*dir.teams*(dir.processors*dir.literal))+2*(ar).stop<2^w)
    {α ξ : ℝ} (route : Diagonal.RouteTableInputs ar dir α ξ n w a.frame link)
    (envelope : LabelIndex.wordEnvelope (ar).alphabet (Diagonal.ExternalSew.intercellWidth N cell+
      dir.teams*((dir.fields+1)*(dir.processors*dir.literal))) < 2^w) :
    let label := meanPackedLabel N cell recv dataBits (List.finRange (ar).cells) (ar).n (ar).header.d (Nat.zero_lt_of_lt two)
    let mass := declarationWeight (ar).header.blocks (ar).b (ar).K (ar).h decl label recv dataBits
    let group := fun j : Fin (ar).header.d => TeamNative.owner R mass j.val
    let owner := fun c : ℕ => if h:c<(ar).cells then group (label ⟨c,h⟩ axis) else 0
    paths sub=ret ∧ declarationInRange word ∧
      broadcastAllowed R X (ar).header.blocks (ar).b (ar).K (ar).h label recv dataBits word ∧
    ∃ (epoch : Returns epochPlacement (pubs i) lib (pinRun).val.2.1 (pinRun).val.2.2)
      (published : Returns Directory.ISA.program (pubs i) lib epoch.val.2.1 epoch.val.2.2) (mid : Memory w)
      (scan : Returns (.seq PrivatePlacement.program Directory.ISA.program) (pubs i) lib
        (paths sub).val.2.1 (paths sub).val.2.2),
      let L := LabelIndex.layout a.frame (readings scan.val.2.2)
      epoch.val.2.2=mid ∧ published.val.2.2=Directory.ISA.publish mid (pubs i 0).val a.next rr ∧
      epoch.val.1.flatMap TeamRAM.Event.choices=[] ∧
      used+traceCost epoch.val.1+traceCost published.val.1≤traceCost ret.val.1+deliveryScanTicks dir.entries dir.teams dir.sites ∧
      scan.val.2=published.val.2 ∧ traceCost scan.val.1≤deliveryScanTicks dir.entries dir.teams dir.sites ∧
      ProfileRouteInputs pf f₀ (pubs i) (Pins.extendGuess sub) published.val.2.2 ∧
      pf.header.length=(pubs i 0).val ∧ (∀ count,TablePointers ((ar).table a.frame count) (readings published.val.2.2)) ∧
      Nonempty (SlottedWriter ar dir rep liveRep (B).layout (pubs i) mid a.next host key sizes) ∧
      SignedPrep.PinnedRawInput («ar»:=ar) (D:=dir) (pp:=rep) (lp:=liveRep) (pub:=pubs i) (slotted:=mid) (base:=a.next)
        f₀ prev fresh gates outputs width off ell control profile claims pad word R X ∧
      PublishedRowPlacement N cell recv dataBits (pubs i 0).val scan.val.2.2 ∧
      Nonempty (SignedPrep.HeaderWriterReceipt ar dir rep liveRep owner decl group (B).layout f₀ (pubs i) lib
        scan.val.2.1 scan.val.2.2) ∧
      L.cells=(ar).cells ∧ L.cableCount=(ar).cables ∧ L.deliveryCount=(rr).length ∧ L.labels=(ar).alphabet := by
  intro label mass group owner
  have normalizedKept : BootResidence (F:=pf) a u slot packet f₀ ad installedPub lib copy initial
      (regs i) sub ret.val.2.2 := by rw [←pubEq]; exact kept
  have normalizedRun : PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap
      f₀ copy pf installedPub lib sub (pinRun).val.2.1 (pinRun).val.2.2 ret.val.2.1 ret.val.2.2 used
      (traceCost ret.val.1) := by rw [←pubEq]; exact pubRun
  let ref := NativeDemands.referenceBank N cell edgeID portID dir original live gap liveWidth
  have keys := NativeDemands.referenceBank_key N cell edgeID portID dir original live gap liveWidth
  have rcv := NativeDemands.receiver_val N cell edgeID portID dir original live gap bounds
  have fixed := signed_published_row_input task dir a u slot packet other old raw team subtotal fresh gates outputs
    width off ell origin gap profile claims pad word R X ret.val.2.2 N cell aux siteID edgeID portID F original live
    rep liveRep ref recv net ids wireFit hk hb positive liveWidth bounds fields tail sub lib (pinRun).val.2.1 (pinRun).val.2.2
    ret.val.2.1 used (traceCost ret.val.1) normalizedKept normalizedRun installed dst len operands img gapControl span controlLo
    dimension room sh two replay rfl teams budget million scaled proc rawSpace route envelope keys rcv
  rw [←pubEq] at fixed
  obtain ⟨epoch,published,mid,atEpoch,pubAt,empty,paid,sources,header,pointers,⟨writer⟩,input,placed,⟨scan,endState,time⟩,_,dims⟩ := fixed
  have memory := congrArg Prod.snd endState
  rw [←memory] at placed dims
  obtain ⟨eqn,valid,allowed,receipt⟩ := BootedPinStart.joint_published_admission index crew tuple i writer prev
    fresh gates outputs width off ell control profile claims pad word X input paths spells ret digits scan (memory.trans pubAt)
    N cell recv placed (Nat.zero_lt_of_lt two)
  subst ret
  exact ⟨rfl,valid,allowed,epoch,published,mid,scan,atEpoch,pubAt,empty,paid,endState,time,sources,header,pointers,
    ⟨writer⟩,input,placed,receipt,dims⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
