import OAI.Computability.BorderVNP.DiagonalSignedProfilePublication
import OAI.Computability.BorderVNP.DiagonalBootedGeometryProfile

/-! # Signed placement and directory outputs of a particular booted physical pin -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit CellAddressPhysical
open Packing.Directory Packing.Directory.PrivateBank LocalRow BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.LabelIndex
open scoped Classical

open CellMacro.Generator RoutingISA.CompactMachine PackedHistoryCircuit

variable {D p w d g : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (task : SignedTaskArena.Layout) (dir : Directory.Layout) (N : Network D P bits)
    (cell : N.Site → Fin task.cube.cells) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin p)
    (original : Fin dir.entries → N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (a : StartupArena) (u : Fin a.teams) (slot : ℕ) (packet : ReferencePacket w d) (origin gap : ℕ)
    (f : BroadcastFrame) (hdr : List Bool) (fields : Pins.ProcessorFields (a.operands u slot packet).layout)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (v : Fin g → Bool)
    (postPin : Bank w) (pinMem : Memory w) (preRegs : Bank w) (prePlace : Memory w) (usedPin profCost : ℕ)

local notation "B" => a.operands u slot packet
local notation "loc" => privateLayout a.frame origin task.cube.cables task.cube.cells dir.entries dir.description gap
local notation "tabs" => bases origin task.cube.cables task.cube.cells dir.entries
local notation "controlBase" => controlsBase origin task.cube.cables task.cube.cells dir.entries (dir.teams*dir.sites)
local notation3 (prettyPrint := false) "sc" => Sum.elim (fun z : SuppliedWord N cell => z.1) (id : Fin task.cube.cells → Fin task.cube.cells)
local notation "sw" => Sum.elim (supplyWidth N cell) (fun _ : Fin task.cube.cells => gap)
local notation "si" => reserveID (C := task.cube.cells) (suppliedID N cell edgeID portID)

set_option maxRecDepth 5500
set_option maxHeartbeats 2200000

/-- A returned placement followed by the directory writer, at the same pin
and geometry memory. The receipts carry the real routing and label tables. -/
def PublishedPin : Prop :=
    ∃ (epoch : Returns epochPlacement pub mac postPin pinMem)
      (published : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2)
      (mid lastMem : Memory w),
      let pp := Directory.ISA.placement (readings mid) (loc).raw
      let lp := Directory.ISA.placement (readings mid) (tabs).livePairs
      let rows := dir.directory pp lp
      let lab := LabelIndex.layout a.frame (readings lastMem)
      epoch.val.2.2=mid ∧ published.val.2.2=lastMem ∧
      epoch.val.1.flatMap TeamRAM.Event.choices=[] ∧ published.val.1.flatMap TeamRAM.Event.choices=[] ∧
      usedPin+traceCost epoch.val.1+traceCost published.val.1 ≤
        profCost+deliveryScanTicks dir.entries dir.teams dir.sites ∧
      lastMem=Directory.ISA.publish mid a.frame a.next rows ∧ (loc).Fits w (readings prePlace) ∧
      (loc).Image (readings prePlace) dir.entries (readings mid) ∧
      ProfileRouteInputs fields f pub (Pins.extendGuess v) lastMem ∧ BootPins pub f packet.extension hdr lastMem ∧
      fields.header.length=(pub 0).val ∧ (∀ count,TablePointers (task.cube.table a.frame count) (readings lastMem)) ∧
      (∃ writer : SlottedWriter task.cube dir pp lp (B).layout pub mid a.next (Sum.elim sc (cell ∘ original))
        (numbered si) (Sum.elim sw (fun _ => dir.description)), ∀ key,
        writer.placement.key key = key.elim Sum.inr (fun j => Sum.inl (Sum.inl (suppliedPort N cell (live j))))) ∧
      (∃ (count : lab.cells=task.cube.cells) (ep : Endpoints lab (readings lastMem))
        (edges : N.CrossingEdge cell ↪ Fin lab.cableCount) (del : Fin rows.length ≃ Fin lab.deliveryCount)
        (recv : Fin rows.length → Fin task.cube.cells), (∀ i,(recv i).val=rows[i.val].cell) ∧
        RowPlacement (networkRows N cell recv (fun i => rows[i.val].width)) (fromTables lab (readings lastMem) ep)
          (finCongr count.symm) (edges.sumMap del.toEmbedding)) ∧
      ∃ scan : Returns (.seq PrivatePlacement.program Directory.ISA.program) pub mac preRegs prePlace,
        scan.val.2=published.val.2 ∧ traceCost scan.val.1≤deliveryScanTicks dir.entries dir.teams dir.sites

section Physical

variable {R r t link inner n : ℕ} {Edge : Type} {gen : Fragment CellMacro.Generator.IO}
    {G : Wiring R r t d link inner n Edge} {pubs : Fin (R+1) → Arg → Word w}
    {registers : Fin (R+1) → RoutingISA.Bank w} {args : Fin (R+1) → UnitAddresses}
    {pin : Fin d → Bool} {wire : Exterior R r link → Bool} {teamID : Fin (R+1)}
    (run : BootedPinStart gen G pubs registers args pin wire teamID)
local notation3 (prettyPrint := false) "mac₀" => TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)
local notation3 (prettyPrint := false) "lib" => install gen n mac₀
local notation3 (prettyPrint := false) "L₀" => G.pinLayout teamID (args teamID).ibase (args teamID).hbase (args teamID).starbase
local notation3 (prettyPrint := false) "f₀" => G.transferFrame teamID (args teamID).header (args teamID).dst
local notation3 (prettyPrint := false) "F₀" => G.processorFields teamID pin wire (args teamID).ibase (args teamID).hbase (args teamID).starbase
local notation3 (prettyPrint := false) "initial" => processorMemory F₀ w
local notation3 (prettyPrint := false) "pubs₀" => pubs teamID
local notation3 (prettyPrint := false) "bank₀" => registers teamID
variable {s k b depth : ℕ} {σ : Type} [Fintype σ] (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
    (F : Fields s task.cube.cables p task.cube.cells depth k b σ) (x : σ → Bool)
    (net : CellAddressPhysical.Represents N cell aux siteID edgeID portID F x) (ids : ∀ c, (F.cells c).val=c.val)
    (wireFit : ∀ c,guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c<2^b)
    (liveWidth : ∀ j,bits (live j)=dir.block)
    (other : Arg → Word w) (old : Fin 81 → Word w) (extent raw team subtotalWidth fresh reserve gates outputs width off ell : ℕ)
    (A : AdviceLayout) (guess : Fin (G.pinLayout teamID (args teamID).ibase (args teamID).hbase (args teamID).starbase).guessWidth → Bool)
include net ids wireFit liveWidth in
/-- The concrete boot dictionary authenticates the pin of the geometry
run. All 28 emitted signed controls are available on that same memory. -/
theorem booted_profile_publication {o time : ℕ} {words : Fin o → ℕ}
    (paths : ProfilePaths (withStartup pinGeometry) (L₀).guessWidth pubs₀ lib bank₀ initial True time origin words
      (BootResidence (F:=fields) a u slot packet f₀ A pubs₀ lib hdr initial bank₀))
    (images : ∀ ret : Returns (withStartup pinGeometry) pubs₀ lib bank₀ initial,
      Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings ret.val.2.2) ∧
        ∀ i : Fin 28, readings ret.val.2.2 (controlBase+i.val)=task.controls i.val)
    (pubEq : pubs₀=(B).bank (core (withDemandBase (task.routeBank a.frame other) a.next) origin task.cube.cables task.cube.cells))
    (installed : packet.extension=signedProfileExtension task old dir origin task.cube.cables task.cube.cells
      raw team subtotalWidth fresh reserve gates outputs width off ell)
    (fits : (B).Fits w) (room : task.cube.stop<2^w) (widthOne : 1<2^w) (hk : k≤b) (hw : b≤w)
    (cells : 0<task.cube.cells) (cellsFit : task.cube.cells≤2^w)
    (span : a.next+7*dir.candidates≤origin) (rawRoom : a.next+7*dir.candidates≤task.cube.header.header)
    (dt : dir.teams=a.teams) (dp : dir.processors=a.processors) (dl : dir.literal=a.literal) (ll : dir.link=a.link)
    (fieldsPos : 0<dir.fields) (two : dir.fields≤2) (teamsPos : 0<dir.teams)
    (procs : dir.processors≤dir.sites) (entries : dir.entries≤dir.teams*dir.sites)
    (payload : dir.entries*dir.description≤dir.teams*dir.processors*(dir.literal/2))
    (bounded : dir.DestinationBounds)
    (localRoom : ∀ c, suppliedSize N cell c+gap+(∑ j,if cell (original j)=c then dir.description else 0) ≤ task.cube.cellStride)
    (globalRoom : ∀ c, suppliedSize N cell c+gap+dir.entries*dir.description≤extent)
    (ctrl : controlBase+8<2^w) (wordRoom : Directory.ISA.wordBound (Directory.ISA.placementBound dir (loc).raw (tabs).livePairs extent)<2^w)
    (dst : (f₀).dst=a.broadcastBase) (length : hdr.length=a.header) (gap₀ : task.controls 8=gap) :
    ∃ ret : Returns (withStartup pinGeometry) pubs₀ lib bank₀ initial,
      ret.val.1.flatMap TeamRAM.Event.choices=List.ofFn guess ∧ traceCost ret.val.1≤time ∧
      BootResidence (F:=fields) a u slot packet f₀ A pubs₀ lib hdr initial bank₀ guess ret.val.2.2 ∧
      (∀ i : Fin 28, readings ret.val.2.2 (controlBase+i.val)=task.controls i.val) ∧
      PublishedPin task dir N cell edgeID portID original live a u slot packet origin gap f₀ hdr fields pubs₀ lib
        guess (run.pins guess).val.2.1 (run.pins guess).val.2.2 ret.val.2.1 ret.val.2.2
        (run.used+traceCost (run.pins guess).val.1) (traceCost ret.val.1) := by
  obtain ⟨profile,eff⟩ := paths.outputs trivial
  let ret := profile guess
  have read := paths.memory ret guess (eff guess).1
  obtain ⟨img,controls⟩ := images ret
  have gapRead := (controls ⟨8,by decide⟩).trans gap₀
  have boot := run.boot
  rw [siteLibrary_installed gen n] at boot
  refine ⟨ret,(eff guess).1,(eff guess).2.1,read,controls,?_⟩
  exact signed_profile_publication task dir N cell aux siteID edgeID portID F x net ids wireFit original live liveWidth
    a u slot packet other old origin gap extent raw team subtotalWidth fresh reserve gates outputs width off ell
    boot run.stable run.positive run.pins (fun v => (run.outputs v).1) profile (fun v => (eff v).1) guess
    pubEq installed fits room widthOne hk hw cells cellsFit span rawRoom dt dp dl ll fieldsPos two teamsPos procs
    entries payload bounded localRoom globalRoom ctrl wordRoom dst length fields read img gapRead

end Physical
end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
