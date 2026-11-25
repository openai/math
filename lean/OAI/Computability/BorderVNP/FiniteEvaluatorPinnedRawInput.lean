import OAI.Computability.BorderVNP.FiniteEvaluatorPublishedWriterSources
import OAI.Computability.BorderVNP.FiniteProfilePublishedWriter
import OAI.Computability.BorderVNP.CubeISALocalRowLabelPublished

/-! # Computing the raw finite schedule inputs from the reached publication -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open Crossing Packing CellAddresses CellAddressCircuit CellAddressPhysical
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.LabelIndex
open RoutingISA RoutingISA.Evaluator RoutingISA.LocalRow CubeHeaderInstall
open TeamContraction TeamContraction.JointHeader VPVNP.BurstRAM
open PackedHistoryCircuit RoutingOutputs

set_option maxRecDepth 5000
set_option maxHeartbeats 2000000

variable {R r lit link inner n w nt ng o : ℕ} {Edge : Type} {Q Γ : Type} {K : Type*} [Field K]
    (G : Wiring R r lit 0 link inner n Edge) (u : Fin (R+1)) (ext : Exterior R r link → Bool)
    (ib hb sb header dst : ℕ) (pub : Arg → Word w) (bank : Bank w)
    (lib : Fin 8 → TeamSite.Macro Q Γ nt ng) (ret : FieldProcessor.Returns Q Γ K nt 8) (fuel : ℕ)

local notation "wf" => Wiring.transferFrame G u header dst
local notation "pf" => Wiring.processorFields G u (Fin.elim0 : Fin 0 → Bool) ext ib hb sb
local notation "mc" => TeamSiteEvents.macros lib fuel

/-- The actual returning geometry processor retains the copied bit string,
all signed extension words, and the native team ID before private placement.
These are the inputs to the label-arena bound on the published table. -/
theorem FrontReceipt.geometry_boot {count pinClock fresh origin : ℕ} {extension : Fin 81 → Word w}
    {copy : List Bool} {words : Fin o → ℕ} {z : Returns profileFront pub mc bank (processorMemory pf w)}
    (receipt : FrontReceipt G u ext ib hb sb header dst pub bank lib ret fuel z count extension copy pinClock fresh origin words)
    (frameEnd : (pub 0).val+112 ≤ dst) (indexStart : dst ≤ ib) (liveStart : dst ≤ hb)
    (endBank : ib+(G.pinLayout u ib hb sb).count ≤ fresh) :
    BootPins pub wf extension copy z.val.2.2 := by
  obtain ⟨inputs,_,read⟩ := receipt.route_sources G u ext ib hb sb header dst pub bank lib ret fuel
    frameEnd indexStart liveStart endBank
  exact ⟨inputs.broadcast.1,inputs.broadcast.2.1,inputs.broadcast.2.2.2.2.2.2,read,receipt.headerAt⟩

end FiniteDiagonal

namespace RoutingISA.Evaluator

open Crossing Packing CellAddresses CellAddressCircuit CellAddressPhysical
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.LabelIndex
open RoutingISA.LocalRow CubeHeaderInstall TeamContraction TeamContraction.JointHeader VPVNP.BurstRAM
open PackedHistoryCircuit RoutingOutputs FiniteDiagonal

variable {W e s n d k b : ℕ} {pub : Arg → Word W} {f : BroadcastFrame} (task : SignedTaskArena.Layout)
    (old : Fin 81 → Word W) (dir : Directory.Layout)
    (fresh gates outputs width off ell raw team subtotal : ℕ) (historyBits : List Bool)
    (claims : List (List Bool)) (pad : ℕ) (word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap)
    (R X origin next gap : ℕ) (start mid : Memory W)
    {P : Type} [Fintype P] {bits : P → ℕ} (N : Network e P bits) (cell : N.Site → Fin task.cube.cells)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin n)
    {σ : Type*} [Fintype σ] (F : Fields s task.cube.cables n task.cube.cells d k b σ) {x : σ → Bool}
    (original : Fin dir.entries → N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)

local notation3 (prettyPrint := false) "a" => SignedTaskArena.Layout.cube task
local notation3 (prettyPrint := false) "frame" => (pub 0).val
local notation3 (prettyPrint := false) "addr" => controlsBase origin (a).cables (a).cells dir.entries (dir.teams*dir.sites)
local notation3 (prettyPrint := false) "q" => privateLayout frame origin (a).cables (a).cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "t" => bases origin (a).cables (a).cells dir.entries
local notation3 (prettyPrint := false) "pp" => Directory.ISA.placement (readings mid) (q).raw
local notation3 (prettyPrint := false) "lp" => Directory.ISA.placement (readings mid) (t).livePairs
local notation3 (prettyPrint := false) "rows" => dir.directory pp lp
local notation3 (prettyPrint := false) "after" => Directory.ISA.publish mid frame next rows
local notation3 (prettyPrint := false) "prev" => routingExtension (task.extension raw team subtotal old) dir origin (a).cables (a).cells
local notation3 (prettyPrint := false) "extra" => signedProfileExtension task old dir origin (a).cables (a).cells raw team subtotal fresh historyBits.length gates outputs width off ell
local notation3 (prettyPrint := false) "copy" => padded (spelling (historyBits++DeclarationBits.spelling word) claims) pad

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2400000 in
/-- After the reached private table and seven-word publication, the header
addresses, chooser rows and the two physical cube-buffer operands meet the
scheduler input predicate even on an incorrect declaration. -/
theorem SlottedWriter.signed_pinned_input
    (net : Represents N cell aux siteID edgeID portID F x) (ids : ∀ c,(F.cells c).val=c.val)
    (small : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k ≤ b) (hb : b ≤ W) (positive : 0<(a).cells)
    (block : ∀ key, bits (live key)=dir.block) (destinations : dir.DestinationBounds)
    (fields : 0 < dir.fields) (tails : dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2))
    {pins : Pins.Layout} {I : Type*} [Fintype I] {host : I → Fin task.cube.cells} {id : I ↪ ℕ} {size : I → ℕ}
    (writer : SlottedWriter a dir pp lp pins pub mid next host id size)
    (beforeBoot : BootPins pub f extra copy start) (publishedBoot : BootPins pub f extra copy after)
    (img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings start))
    (hdr : Header frame origin (a).cables (a).cells dir.entries (readings start))
    (demand : readings start (frame+8)=next) (pointer : readings start (frame+92)=addr)
    (controls : ∀ i : Fin 28, readings start (addr+i.val)=task.controls i.val)
    (prior : frame+112 ≤ next) (front : frame+112 ≤ f.dst) (copied : f.dst+(copy).length ≤ next)
    (span : next+7*dir.candidates ≤ origin) (endCables : origin+(a).cables*3 ≤ (a).publicBase)
    (placed : (q).Image (readings start) dir.entries (readings mid)) (fit : (q).Fits W (readings start))
    (dims : dir.teams≤2^W ∧ dir.processors≤2^W ∧ dir.fields≤2^W ∧ dir.literal<2^W ∧
      (a).cells≤2^W ∧ (a).cellStride≤2^W) (count : (rows).length<2^W)
    (shape : (a).header=geometryInputs fresh historyBits.length gates outputs width W (a).header.d (a).n (a).header.blocks (a).b (a).h (a).s)
    (secondary : addr+10 < (a).header.header) (two : 2 ≤ (a).header.d)
    (replay : (a).ReplayRoom W frame) (teamCount : f.teams=R+1) (teamArena : (a).teams=R+1)
    (budget : (prev 0).val=X) (million : 1000000 < 2^W) (scaled : 1000000*X*(R+1) < 2^W)
    (processors : 0 < dir.processors) (payload : 0 < dir.block) (fieldsMax : dir.fields≤2)
    (rawSpace : 1000000*((a).stop+3*dir.teams*(dir.processors*dir.literal))+2*(a).stop < 2^W)
    (records : (rows).length+(a).header.d.choose 2 ≤ (a).maxRows)
    (envelope : LabelIndex.wordEnvelope (a).alphabet (Diagonal.ExternalSew.intercellWidth N cell+
      dir.teams*((dir.fields+1)*(dir.processors*dir.literal))) < 2^W) :
    SignedPrep.PinnedRawInput (ar := task.cube) (D := dir) («pp» := pp) («lp» := lp) (pub := pub)
      (slotted := mid) (base := next) f prev fresh gates outputs width off ell addr historyBits claims pad word R X := by
  have hlen := dir.directory_length_le pp lp
  have room : next+7*(rows).length ≤ origin := (Nat.add_le_add_left (Nat.mul_le_mul_left 7 hlen) next).trans span
  have geo : origin ≤ addr := by simp [controlsBase,bases]; omega
  have low : next ≤ origin := (Nat.le_add_right ..).trans span
  have numbers := slotted_row_words writer dims.1 dims.2.1 dims.2.2.1 dims.2.2.2.1 dims.2.2.2.2.1 dims.2.2.2.2.2
  have lab := labelPrefixFits_published a prev fresh historyBits.length gates outputs width off ell start mid beforeBoot
    N cell aux siteID edgeID portID F net ids small hk hb positive dir original live block destinations fields tails
    origin next gap img hdr demand prior copied (.inl (by omega)) endCables
    (by have h := replay.primary; omega) replay.alphabet replay.stopFit envelope placed fit room count numbers
  obtain ⟨_,_,_,_,cellCount⟩ := chooser_header (readings start) mid rows hdr demand (by omega) (by omega) placed count
  obtain ⟨ptr,ctrl⟩ := directoryPublished_controls dir pp lp (fun j => task.controls j.val) prior span placed pointer controls
  rw [ptr] at ctrl
  exact ⟨publishedBoot,shape,replay.primary,by omega,two,Nat.pos_of_mul_pos_right replay.payload,replay.positive,
    replay.stopFit,lab,cellCount,teamCount,teamArena,budget,million,scaled,secondary,
    ⟨ptr,(ctrl 9).trans task.consumer_words.2.2.1,(ctrl 10).trans task.consumer_words.2.2.2.1⟩,
    processors,payload,fieldsMax,rawSpace,records⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
