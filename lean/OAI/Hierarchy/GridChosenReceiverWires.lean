import OAI.Hierarchy.GridChosenReceiverWirePayload
import OAI.Hierarchy.TraceReceiverWordSources
import OAI.Hierarchy.TraceReceiverTerminalMap
import OAI.Hierarchy.TraceReceiverWireBits
import OAI.Hierarchy.TraceReceiverInstalled

namespace OAI
/-! # The selected physical forest reads the actual compact receiver tape -/

noncomputable section
namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open TraceAdmission GridScale GridThrough GridRegisteredSetting GridInstalledEvaluator GridReceiverDirectory GridPhysicalCompiler
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] [Fintype F] {Q : ℕ→ℕ} {loss : ℕ→ℝ}
variable {blk : Block F} {m A w degree stageRate rootRate tariff power : ℕ}
variable {v : TickSelection F (m+1) A w Q loss} (I : Installed blk m A w degree stageRate rootRate v)
variable (R : GridInstalledFit.Receipt blk m A w degree stageRate rootRate v I tariff power)
set_option quotPrecheck false
local notation "l" => layout m A w (overhead Q loss w) v.copies degree stageRate rootRate
local notation "D" => I.D
local notation "gate" => 26*GridDescription.sector w
local notation "arch" => GridDescription.capacity w
local notation "W" => 64*w
local notation "rails" => GridControllerSimGeometry.railCount m (l).sideMinusOne (l).bank
local notation "cnt" => GridNativeImage.parameterCount D l
local notation "args" => GridNativeDispatch.params D l 0 gate
local notation "bits" => GridPhysicalSelector.bits (D).run
local notation "ext" => TraceReceiverSeedWords.source (D).machine (D).fit (D).field (D).state
local notation "U" => TraceReceiverSeedWords.wordsLayout (D).machine (D).fit (D).field (D).state (D).block (D).axesFit
local notation "trees" => TraceReceiverSeedWords.forest (D).machine (D).fit (D).field (D).state (D).block (D).axesFit
variable (geom : ElectionRoom I.D (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate))
    (recv : Machine (64*w) (GridDescription.capacity w) (GridDescription.capacity w) (GridDescription.capacity w))
    (safe : GridNativeDispatch.WordRoom I.D)
local notation "code" => GridDescription.code (q:=w^2) recv (D).machine
local notation "table" => GridNativeDispatch.actualTable D safe
local notation "room" => GridNativeDispatch.selectorRoom D l R.table R.selector safe
local notation "rooms" => (R.rooms recv 0 gate).choose
local notation "widths" => (fun i=>(v.replacement.width_le_size i).trans v.size_le)
variable (z : I.D.trace)
local notation "P" => streamLayout I R geom recv safe z
local notation "sel" => InputWindow D l z safe room
local notation "site" => ((D).ordinal z.1).symm
local notation "selected" => (D).run.plan.assemble z.1 ((receiverAssembly I) U) trees
local notation "cost" => (D).costs (GridNativeImage.resources D l) z.1 m (l).sideMinusOne (l).bank (D).issuedCharges ((D).issuedUnit w degree stageRate rootRate)
local notation "group" => (fun (c : Cell (m+1) (l).sideMinusOne) (j : Fin v.copies) =>
  FactorAllocation.factors w cost (List.ofFn id) (GridTicks.index (c,j)))
local notation "input" => (streamInput I recv 0 gate R.text rooms widths (table).codes room z)

set_option maxHeartbeats 1600000 in
/-- The boundary bits begin just after the actual accepted history on this tape. -/
def wireSuffix : ℕ := (l).receiverText+((cnt+1)*W+GridReceiverHeader.count w*W)+1+
  ((D).run.plan.write (table).codes z.1).length

include R recv in
theorem wireSuffix_fit (c : Cell (m+1) (l).sideMinusOne) (j : Fin v.copies) :
    wireSuffix I safe z+bits z.1≤(l).pinWidth := by
  have head:=(stream_header I recv 0 gate R.text rooms widths (table).codes room z (fun _=>false) c j).1
  change (GridReceiverHeader.header (l).receiverText R.text code ((GridTicks.index (c,j)).val:Word W) args sel).length≤_ at head
  rw [GridReceiverHeader.length] at head
  change (l).receiverText+((cnt+1)*W+(GridReceiverHeader.count w*W+((l).selectorCap+1)))≤(l).pinWidth at head
  have span:=room z.1
  unfold wireSuffix
  omega

/-- Every external wire uses its authentic assigned input slot. Each incident
wire uses the same boundary numbering as the certificate on this tick. -/
def slotWire (c : Cell (m+1) (l).sideMinusOne) (j : Fin v.copies) :
    ∀ i : Fin (group c j).length, Fin ((selected).1.width (site (group c j)[i])) → Fin (l).pinWidth :=
  fun i=>TraceReceiverWordSources.wires (D).run z.1 (receiverAssembly I) U trees P ext (wireSuffix I safe z)
    (wireSuffix_fit I R recv safe z c j) (site (group c j)[i])

local notation "actual" => ((D).run.terminalLayer z.1).state
local notation "words" => (D).run.endWords z.1 (receiverAssembly I).steps U

set_option maxHeartbeats 1600000 in
/-- The four-field native root record resolves this external socket through
its real ancestry to the scheduled physical input word. -/
def slotEndpoint (u : (actual).shape.Site) (a : Fin ((words).ext u)) : Fin (l).pinWidth :=
  let b:=(D).run.extAncestor z.1 (receiverAssembly I).steps U u a
  (P).slot (ext b.1 b.2)

private def factorSite (c : Cell (m+1) (l).sideMinusOne) (j : Fin v.copies)
    (i : Fin (group c j).length) : (I.D.run.plan.finish z.1).Site :=
  site (group c j)[i]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 2800000 in
/-- This address is the one read back by `TraceReceiverMapExecution.Source.saved`.
The hypotheses identify the registered root and its actual port ordinal. -/
theorem slotWire_at (c : Cell (m+1) (l).sideMinusOne) (j : Fin v.copies)
    (i : Fin (group c j).length) (u : (actual).shape.Site) (same : HEq u (factorSite I z c j i))
    (native : Fin ((words).ports.form.width u)) (port : Fin ((selected).1.width (factorSite I z c j i)))
    (ordinal : native.val=port.val) :
    slotWire I R geom recv safe z c j i port=
      (words).ports.physicalSource (slotEndpoint I R geom recv safe z)
        (TraceReceiverTerminalMap.shared actual (wireSuffix I safe z) (wireSuffix_fit I R recv safe z c j)) u native :=
  TraceReceiverWordSources.wires_at (D).run z.1 (receiverAssembly I) U trees P ext (wireSuffix I safe z)
    (wireSuffix_fit I R recv safe z c j) u (factorSite I z c j i) same native port ordinal

set_option maxRecDepth 32000 in
set_option maxHeartbeats 2800000 in
/-- This is the per-port read required by `ReceiverStreams`, for the genuine
registered ordinal, seed coordinate and local grid assignment. -/
theorem slotWire_read (x : GridDiagonal.Pins (Fin rails)) (c : Cell (m+1) (l).sideMinusOne) (j : Fin v.copies) :
    ∀ (i : Fin (group c j).length) a, input x c j (slotWire I R geom recv safe z c j i a).val =
      (selected).1.read (site (group c j)[i])
        (fun b : Fin I.inputSize=>GridDescription.input (x ∘ UniversalGrid.Wiring.railPin.symm) code
          (GridNativeDispatch.source D l v.replacement 0 gate) b.val)
        (((D).run.plan.finish z.1).graph.atVertex ((D).run.terminalLabels z.1 z.2) (site (group c j)[i])) a := by
  intro i
  let localTape:=fun a : Fin (l).pinWidth=>input x c j a.val
  let rawPin:=fun b : Fin I.inputSize=>GridDescription.input (x ∘ UniversalGrid.Wiring.railPin.symm) code
    (GridNativeDispatch.source D l v.replacement 0 gate) b.val
  obtain ⟨owns,_,order,_⟩:=streamLayout_rows I R geom recv safe z
  apply TraceReceiverWordSources.wires_read (D).run z.1 (receiverAssembly I) U trees P ext ((D).ordinal z.1)
    (c,j) rawPin localTape (wireSuffix I safe z) (wireSuffix_fit I R recv safe z c j) z.2
  · exact fun a t=>TraceReceiverSeedWords.seed_read (D).machine (D).fit (D).field (D).state (D).block (D).axesFit a rawPin t
  · intro a t
    rw [owns]
    change (D).ordinal z.1 ((D).run.plan.destination z.1
      (PairedCursor.owner (TraceDistribution.layout (D).machine (D).fit (D).field (D).state) (ext a t)))=_
    exact congrArg ((D).ordinal z.1) (congrArg ((D).run.plan.destination z.1)
      (TraceReceiverSeedWords.source_owner (D).machine (D).fit (D).field (D).state a t))
  · exact fun a same=>slot_payload I R geom recv safe z x c j a same
  · intro b
    exact TraceReceiverWireBits.mounted (D).run.plan (table).codes bits (l).selectorCap (l).receiverText R.text code
      ((GridTicks.index (c,j)).val:Word W) args sel (input x c j) room z
      (GridSelector.decode_encode (D).run.plan (table).codes bits (l).selectorCap room (some z)) _ rfl
      (stream_header I recv 0 gate R.text rooms widths (table).codes room z x c j).2 b
  · rw [Equiv.apply_symm_apply,order]
    exact List.getElem_mem («l»:=group c j) i.isLt

end Hierarchy.GridChosenReceiver

end
end OAI
