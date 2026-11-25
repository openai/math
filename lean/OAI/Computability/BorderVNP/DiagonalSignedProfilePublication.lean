import OAI.Computability.BorderVNP.DiagonalChosenPinPublication
import OAI.Computability.BorderVNP.DiagonalSignedPublishedInputs
import OAI.Computability.BorderVNP.DiagonalSignedDemandPublication
import OAI.Computability.BorderVNP.DiagonalSignedPublicationFields
import OAI.Computability.BorderVNP.FiniteProfilePublishedLabels

/-! # The real signed profile reaches the labelled routing directory on the same pin -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit CellAddressPhysical
open Packing.Directory Packing.Directory.PrivateBank LocalRow BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.LabelIndex
open scoped Classical

variable {D s p depth k b w d g : ℕ} {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (task : SignedTaskArena.Layout) (dir : Directory.Layout)
    (N : Network D P bits) (cell : N.Site → Fin task.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin p)
    (F : Fields s task.cube.cables p task.cube.cells depth k b σ) (x : σ → Bool)
    (net : CellAddressPhysical.Represents N cell aux siteID edgeID portID F x) (ids : ∀ c, (F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c<2^b)
    (original : Fin dir.entries → N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (liveWidth : ∀ j,bits (live j)=dir.block)
    (a : StartupArena) (u : Fin a.teams) (slot : ℕ) (packet : ReferencePacket w d)
    (other : Arg → Word w) (old : Fin 81 → Word w) (origin gap extent : ℕ)
    (raw team subtotalWidth fresh reserve gates outputs width off ell : ℕ)
    {f : BroadcastFrame} {A : AdviceLayout} {hdr : List Bool}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {bank : Bank w} {initial : Memory w}
    {trace out saved} (boot : Runs pub mac JointHeader.bootHeader bank initial trace out saved)
    (stable : f.Stable (readings out)) (positive : (saved f.dst).val ≠ 0)
    (pins : (Fin g → Bool) ≃ Pins.Return pub mac (Function.update out 10 (saved f.dst)) saved)
    (pinChoices : ∀ v, (pins v).val.1.flatMap TeamRAM.Event.choices=List.ofFn v)
    (profile : (Fin g → Bool) ≃ Returns (withStartup pinGeometry) pub mac bank initial)
    (profileChoices : ∀ v, (profile v).val.1.flatMap TeamRAM.Event.choices=List.ofFn v)
    (v : Fin g → Bool)

local notation "B" => a.operands u slot packet
local notation "loc" => privateLayout a.frame origin task.cube.cables task.cube.cells dir.entries dir.description gap
local notation "tabs" => bases origin task.cube.cables task.cube.cells dir.entries
local notation "control" => controlsBase origin task.cube.cables task.cube.cells dir.entries (dir.teams*dir.sites)
local notation3 (prettyPrint := false) "sc" => Sum.elim (fun z : SuppliedWord N cell => z.1) (id : Fin task.cube.cells → Fin task.cube.cells)
local notation "sw" => Sum.elim (supplyWidth N cell) (fun _ : Fin task.cube.cells => gap)
local notation "si" => reserveID (C := task.cube.cells) (suppliedID N cell edgeID portID)

set_option maxRecDepth 6000
set_option maxHeartbeats 2500000

include net ids wireFit liveWidth boot stable positive pinChoices profileChoices in
/-- Start at the chosen pin of an accepted full signed geometry profile. Its very
next two returns publish the original private slots, exact seven-word demand
rows, source pins, and the chooser's actual endpoint and receiver tables.
The clock includes startup, substitution, geometry, placement and publication. -/
theorem signed_profile_publication
    (pubEq : pub=(B).bank (core (withDemandBase (task.routeBank a.frame other) a.next) origin task.cube.cables task.cube.cells))
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
    (ctrl : control+8<2^w) (wordRoom : Directory.ISA.wordBound (Directory.ISA.placementBound dir (loc).raw (tabs).livePairs extent)<2^w)
    (dst : f.dst=a.broadcastBase) (length : hdr.length=a.header) (fields : Pins.ProcessorFields (B).layout)
    (res : BootResidence (F:=fields) a u slot packet f A pub mac hdr initial bank v (profile v).val.2.2)
    (img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings (profile v).val.2.2))
    (gapRead : readings (profile v).val.2.2 (control+8)=gap) :
    ∃ (epoch : Returns epochPlacement pub mac (pins v).val.2.1 (pins v).val.2.2)
      (published : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2)
      (mid lastMem : Memory w),
      let pp := Directory.ISA.placement (readings mid) (loc).raw
      let lp := Directory.ISA.placement (readings mid) (tabs).livePairs
      let rows := dir.directory pp lp
      let lab := LabelIndex.layout a.frame (readings lastMem)
      epoch.val.2.2=mid ∧ published.val.2.2=lastMem ∧
      epoch.val.1.flatMap TeamRAM.Event.choices=[] ∧ published.val.1.flatMap TeamRAM.Event.choices=[] ∧
      traceCost trace+2+traceCost (pins v).val.1+traceCost epoch.val.1+traceCost published.val.1 ≤
        traceCost (profile v).val.1+deliveryScanTicks dir.entries dir.teams dir.sites ∧
      lastMem=Directory.ISA.publish mid a.frame a.next rows ∧ (loc).Fits w (readings (profile v).val.2.2) ∧
      (loc).Image (readings (profile v).val.2.2) dir.entries (readings mid) ∧
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
      ∃ scan : Returns (.seq PrivatePlacement.program Directory.ISA.program) pub mac (profile v).val.2.1 (profile v).val.2.2,
        scan.val.2=published.val.2 ∧ traceCost scan.val.1≤deliveryScanTicks dir.entries dir.teams dir.sites := by
  subst pub
  let params := core (withDemandBase (task.routeBank a.frame other) a.next) origin task.cube.cables task.cube.cells
  let publ := (B).bank params
  let before := (profile v).val.2.2
  have frame : (publ 0).val=a.frame := (B).frameBase_word _ fits
  have residence := res
  obtain ⟨_,_,_,_,state,retained⟩ := residence
  obtain ⟨header,pointed,shape,host⟩ := signed_publication_fields task dir a u slot packet other old
    origin raw team subtotalWidth fresh reserve gates outputs width off ell extent (Pins.extendGuess v) installed
    ctrl widthOne two room wordRoom fits state retained
  have recordFit : task.cube.records<2^w := by
    have order := task.cube.writer_order
    omega
  obtain ⟨es,fs,r₁,r₂,mid,place,privateFit,privateImage,publish,_,paid,_,writer,keyEq⟩ :=
    signed_publication task dir N cell aux siteID edgeID portID F x net ids wireFit original live liveWidth
      a u slot packet other origin gap (Pins.extendGuess v) extent mac (profile v).val.2.1 fits span recordFit host rawRoom
      dt dp dl ll fieldsPos payload bounded localRoom state retained img header shape pointed gapRead ctrl teamsPos procs entries
      globalRoom wordRoom
  obtain ⟨epoch,lastRun,epochState,lastState,epSilent,dirSilent,clock⟩ :=
    chosenPin_publication f boot stable positive pins pinChoices profile profileChoices v place publish
  have tables := BootResidence.signedPublishedInputs task a u slot packet other origin task.cube.cables task.cube.cells gap dir
    dst length room span fits fields res privateImage
  have tRoom : dir.teams≤2^w := dt ▸ (fits (B).layout.teams (by simp [PacketOperands.values])).le
  have pRoom : dir.processors≤2^w := dp ▸ (fits (B).layout.processors (by simp [PacketOperands.values])).le
  have lRoom : dir.literal<2^w := dl ▸ fits (B).layout.literal (by simp [PacketOperands.values])
  have strideRoom : task.cube.cellStride≤2^w :=
    ((Nat.le_mul_of_pos_left _ cells).trans (Nat.le_add_left _ task.cube.cellBank)).trans room.le
  have startRoom : origin<2^w := by dsimp only [controlsBase,bases] at ctrl; omega
  have labels := FiniteDiagonal.slotted_label_placement task.cube dir N cell aux siteID edgeID portID F x net ids wireFit
    hk hw cells original live liveWidth publ a.next origin gap before mid writer img
    (frame ▸ privateImage) (frame ▸ privateFit) (frame ▸ header) span startRoom tRoom pRoom (two.trans widthOne)
    lRoom cellsFit strideRoom
  let physicalLabels (head : ℕ) : Prop :=
    let placed := privateLayout head origin task.cube.cables task.cube.cells dir.entries dir.description gap
    let rows := dir.directory (Directory.ISA.placement (readings mid) placed.raw)
      (Directory.ISA.placement (readings mid) (tabs).livePairs)
    let data := readings (Directory.ISA.publish mid head a.next rows)
    let lab := LabelIndex.layout head data
    ∃ (count : lab.cells=task.cube.cells) (ep : Endpoints lab data) (edges : N.CrossingEdge cell ↪ Fin lab.cableCount)
      (del : Fin rows.length ≃ Fin lab.deliveryCount) (recv : Fin rows.length → Fin task.cube.cells),
      (∀ i,(recv i).val=rows[i.val].cell) ∧ RowPlacement (networkRows N cell recv (fun i => rows[i.val].width))
        (fromTables lab data ep) (finCongr count.symm) (edges.sumMap del.toEmbedding)
  have actual : physicalLabels (publ 0).val := labels
  have labelled : physicalLabels a.frame := (congrArg physicalLabels frame).mp actual
  have midEq : epoch.val.2.2=mid := congrArg Prod.snd epochState
  have finalEq := congrArg (fun p => p.2.2) lastState
  refine ⟨epoch,lastRun,mid,_,midEq,finalEq,epSilent,dirSilent,?_,?_⟩
  · rw [clock]
    rw [Transmission.cost_append] at paid
    omega
  · exact ⟨rfl,privateFit,privateImage,tables.1,tables.2.1,tables.2.2.1,tables.2.2.2,⟨writer,keyEq⟩,labelled,
      ⟨⟨(es++fs,r₂,_),place.seq publish⟩,(congrArg Prod.snd lastState).symm,paid⟩⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
