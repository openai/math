import OAI.Computability.BorderVNP.DiagonalSignedProfilePublication
import OAI.Computability.BorderVNP.DiagonalSignedPublicationPins
import OAI.Computability.BorderVNP.FiniteEvaluatorPinnedRawInput
import OAI.Computability.BorderVNP.DiagonalSelectedRouteTable

/-! # The raw schedule input of the signed seven-word publisher -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Crossing Packing CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.LabelIndex
open RoutingISA RoutingISA.Evaluator RoutingISA.LocalRow CubeHeaderInstall TeamContraction JointHeader ProcessorSlots VPVNP.BurstRAM
open scoped Classical

set_option maxRecDepth 5500
set_option maxHeartbeats 2400000

variable {w dim s p depth k b d : ℕ} (task : SignedTaskArena.Layout) (dir : Directory.Layout)
  (a : StartupArena) (u : Fin a.teams) (slot : ℕ) (packet : ReferencePacket w d) (other : Arg → Word w)
  (old : Fin 81 → Word w) (raw team subtotal fresh gates outputs width off ell origin gap : ℕ)
  (profile : List Bool) (claims : List (List Bool)) (pad : ℕ)
  (word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap)
  (R X : ℕ) (start mid : Memory w)
  {P : Type} [Fintype P] {bits : P → ℕ} (N : Network dim P bits) (cell : N.Site → Fin task.cube.cells)
  (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin p)
  {σ : Type*} [Fintype σ] (F : Fields s task.cube.cables p task.cube.cells depth k b σ) {x : σ → Bool}
  (original : Fin dir.entries → N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
  {ad : AdviceLayout} {f : BroadcastFrame} {z : Bank w} {saved : Memory w} (guess : ℕ → Bool)

local notation "ar" => SignedTaskArena.Layout.cube task
local notation "B" => a.operands u slot packet
local notation3 (prettyPrint := false) "pub" => (B).bank (core (withDemandBase (task.routeBank a.frame other) a.next)
  origin (ar).cables (ar).cells)
local notation3 (prettyPrint := false) "control" => controlsBase origin (ar).cables (ar).cells dir.entries (dir.teams*dir.sites)
local notation3 (prettyPrint := false) "loc" => privateLayout a.frame origin (ar).cables (ar).cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "tabs" => bases origin (ar).cables (ar).cells dir.entries
local notation3 (prettyPrint := false) "pp" => Directory.ISA.placement (readings mid) (loc).raw
local notation3 (prettyPrint := false) "lp" => Directory.ISA.placement (readings mid) (tabs).livePairs
local notation3 (prettyPrint := false) "prev" => routingExtension (task.extension raw team subtotal old) dir origin (ar).cables (ar).cells
local notation3 (prettyPrint := false) "ext" => signedProfileExtension task old dir origin (ar).cables (ar).cells raw team subtotal
  fresh profile.length gates outputs width off ell
local notation3 (prettyPrint := false) "copy" => padded (spelling (profile++DeclarationBits.spelling word) claims) pad
local notation3 (prettyPrint := false) "result" => Directory.ISA.publish mid a.frame a.next (dir.directory pp lp)

/-- The actual signed boot, geometry, scalar controls and attained directory
supply the raw guard on any header declaration. No execution of the group
scheduler is needed to obtain its input. -/
theorem signed_raw_writer_input
    (net : CellAddressPhysical.Represents N cell aux siteID edgeID portID F x) (ids : ∀ c,(F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k≤b) (hb : b≤w) (positive : 0<(ar).cells)
    (liveWidth : ∀ q, bits (live q)=dir.block) (bounds : dir.DestinationBounds) (fields : 0<dir.fields)
    (tail : dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2))
    {I : Type*} [Fintype I] {host : I → Fin (ar).cells} {id : I ↪ ℕ} {size : I → ℕ}
    (writer : SlottedWriter ar dir pp lp (B).layout pub mid a.next host id size)
    {field : Pins.ProcessorFields (B).layout}
    (boot : BootHeaderState field f ad packet pub copy z saved)
    (resident : ∀ j<a.next, start j=Pins.preparedMemory (B).layout guess saved (B).layout.count j)
    (installed : packet.extension=ext) (dst : f.dst=a.broadcastBase) (len : (copy).length=a.header)
    (after : BootPins pub f packet.extension copy result) (operands : (B).Fits w)
    (img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings start))
    (gapControl : ∀ i : Fin 28, readings start (control+i.val)=task.controls i.val)
    (placed : (loc).Image (readings start) dir.entries (readings mid)) (fit : (loc).Fits w (readings start))
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
      dir.teams*((dir.fields+1)*(dir.processors*dir.literal))) < 2^w) :
    SignedPrep.PinnedRawInput («ar» := ar) (D:=dir) («pp» := pp) («lp» := lp) («pub» := pub) (slotted:=mid) (base:=a.next)
      f prev fresh gates outputs width off ell control profile claims pad word R X := by
  have base : (pub 0).val=a.frame := (B).frameBase_word _ operands
  have before := signed_profile_pins a u slot packet guess base boot resident dst len
  have low : a.frame+112 ≤ a.broadcastBase := by unfold StartupArena.broadcastBase StartupArena.dense; omega
  have through : a.broadcastBase+a.header ≤ a.next := by unfold StartupArena.next StartupArena.hbase StartupArena.ibase; omega
  have controls : control+8<2^w :=
    (by omega : control+8 < (ar).header.header).trans
      ((LocalRow.header_le_publicBase ar).trans_lt (by have order := (ar).writer_order; omega))
  obtain ⟨header,pointer,dirHead,_⟩ := signed_publication_fields task dir a u slot packet other old
    origin raw team subtotal fresh profile.length gates outputs width off ell (ar).cellStride guess installed controls
    (by omega : 1<2^w) bounds.fields replay.stopFit room operands boot resident
  have small : Directory.ISA.placementBound dir (tabs).privatePairs (tabs).livePairs (ar).cellStride < 2^w := by
    let v := Directory.ISA.placementBound dir (tabs).privatePairs (tabs).livePairs (ar).cellStride
    change 32*(v+1)^4 < 2^w at room
    nlinarith only [room,Nat.zero_le (v^4),Nat.zero_le (v^3),Nat.zero_le (v^2)]
  have nc : dir.candidates < 2^w := by dsimp only [Directory.ISA.placementBound] at small; omega
  have tFit : dir.teams ≤ 2^w := dimension.1 ▸ (operands (B).layout.teams (by simp [PacketOperands.values])).le
  have pFit : dir.processors ≤ 2^w := dimension.2.1 ▸ (operands (B).layout.processors (by simp [PacketOperands.values])).le
  have lit : dir.literal < 2^w := dimension.2.2.1 ▸ operands (B).layout.literal (by simp [PacketOperands.values])
  have nd : a.next < 2^w := by
    have o : origin ≤ control := by dsimp only [controlsBase,bases]; omega
    omega
  obtain ⟨_,demand⟩ := decoded_demand_header dir B (task.routeBank a.frame other) a.next origin (ar).cables (ar).cells
    start dimension operands nd fields (resident_frames a u slot packet guess base boot resident).1 (base ▸ dirHead)
  have border : origin+(ar).cables*3 ≤ (ar).publicBase := by
    have bound : origin+(ar).cables*3 ≤ control := by dsimp only [controlsBase,bases]; omega
    exact bound.trans ((Nat.le_add_right _ _).trans (controlLo.trans (LocalRow.header_le_publicBase ar)))
  rw [installed] at before after
  apply writer.signed_pinned_input task old dir fresh gates outputs width off ell raw team subtotal profile claims pad word R X
    origin a.next gap start mid N cell aux siteID edgeID portID F original live net ids wireFit hk hb positive liveWidth
    bounds fields tail before
  · simpa only [base] using after
  · exact img
  · simpa only [base] using header
  · exact demand
  · simpa only [base] using pointer
  · exact gapControl
  · rw [base]; omega
  · rw [base,dst]; exact low
  · rw [dst,len]; exact through
  · exact span
  · exact border
  · simpa only [base] using placed
  · simpa only [base] using fit
  · exact ⟨tFit,pFit,(by have h := bounds.fields; omega),lit,(by have h:=replay.stopFit; have h' := (ar).writer_order; dsimp only [CubeArena.Layout.stop] at h; omega),
      (by dsimp only [Directory.ISA.placementBound] at small; omega)⟩
  · exact (dir.directory_length_le ..).trans_lt nc
  · exact sh
  · omega
  · exact two
  · simpa only [base] using replay
  · exact count
  · exact teams
  · exact budget
  · exact million
  · exact scaled
  · exact proc
  · exact bounds.block
  · exact bounds.fields
  · exact rawSpace
  · apply (route.tables ..).1
  · exact envelope

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
