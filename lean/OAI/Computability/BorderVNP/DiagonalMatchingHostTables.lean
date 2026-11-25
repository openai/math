import OAI.Computability.BorderVNP.DiagonalJointPublishedHostTables
import OAI.Computability.BorderVNP.RoutingISASignedPrepOwned

/-! # Joint host rows from the actual matching signed writer histories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing PackedHistoryCircuit
open BorderVNP.Cube Cube.Physical Cube.Scatter Cube.TeamRows Scatter.Assignment DiagonalTallyPacketEmit
open FiniteEvaluator Evaluator SignedPrep Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit
open Packing.Directory CellAddressPhysical Cube.MeanChoice Cube.LabelIndex Cube.NativeIntervals Cube.HostScatter
open TeamContraction.JointHeader CubeHeaderInstall LocalRow Physical.NativeAssignments
open Diagonal.ExternalSew.Fragments
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 5500

variable {R r t pins₀ link inner e₀ w : ℕ} {Edge : Type} {G : Wiring R r t pins₀ link inner e₀ Edge}
variable {pin : Fin pins₀ → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {histDir : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {ownedOrigin ownedStride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L histDir pp lp owner ownedOrigin ownedStride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}

variable (task : SignedTaskArena.Layout) (dir : Directory.Layout)
    {D sz n d k b : ℕ} {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin task.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin sz) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin n)
    (F : Fields sz task.cube.cables n task.cube.cells d k b σ) (x : Fin (R+1) → σ → Bool)
    (original : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (bounds : dir.DestinationBounds) (base geo gap : ℕ) (profile mid : Fin (R+1) → Memory w)
    {decl : LengthDeclaration task.cube.n task.cube.header.d} {group : Fin task.cube.header.d → Fin (R+1)}
    {owned : TeamRows.Returns (Fin (R+1)) task.cube w}
    {template : Frame} {id : TableEntry task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s → ℕ} {count : ℕ}
    (alphabet : 0<task.cube.header.d)

local notation3 (prettyPrint := false) "head(" u ")" => ((H u).pub 0).val
local notation3 (prettyPrint := false) "pr(" u ")" => privateLayout (head(u)) geo task.cube.cables task.cube.cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "tabs" => bases geo task.cube.cables task.cube.cells dir.entries
local notation3 (prettyPrint := false) "p₀(" u ")" => ISA.placement (readings (mid u)) (pr(u)).raw
local notation3 (prettyPrint := false) "l₀(" u ")" => ISA.placement (readings (mid u)) (tabs).livePairs
local notation3 (prettyPrint := false) "published(" u ")" => ISA.publish (mid u) (head(u)) base (dir.directory (p₀(u)) (l₀(u)))
local notation3 (prettyPrint := false) "dataRows" => NativeDemands.rows N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "recv" => NativeDemands.receiver N cell edgeID portID dir original live gap bounds
local notation3 (prettyPrint := false) "amount" => fun i : Fin (dataRows).length => dataRows[i.val].width
local notation3 (prettyPrint := false) "labels" => meanPackedLabel N cell recv amount (List.finRange task.cube.cells) task.cube.n task.cube.header.d alphabet
local notation3 (prettyPrint := false) "ownerMap" => greedyOwner (blocks:=task.cube.header.blocks) (K:=task.cube.K) (h:=task.cube.h) R task.cube.b task.cube.s labels recv amount

/-- The actual matching assignment replay and its interpreters' raw publication and
writer histories produce the full host tables on all its owned output memories.
The common frame and the assigned teams are read from this joint handoff. -/
theorem SharedWriters.matching_host_tables
    (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) task.cube.header.blocks task.cube.K task.cube.h decl group)
    (handoff : OwnedHandoff f g src task.cube decl group template id count owned)
    (matchQ : Matching task.cube ownerMap decl (f.receivedRows g group))
    (observed : ObservedOwned task.cube decl group owned ownerMap (f.receivedRows g group) matchQ.val)
    (net : ∀ u, Represents N cell aux siteID edgeID portID F (x u)) (ids : ∀ c,(F.cells c).val=c.val)
    (fieldRoom : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k≤b) (wordFit : b≤w) (positive : 0<task.cube.cells) (liveWidth : ∀ j,bits (live j)=dir.block)
    (img : ∀ u, Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) (x u) geo (readings (profile u)))
    (place : ∀ u,(pr(u)).Image (readings (profile u)) dir.entries (readings (mid u)))
    (fit : ∀ u,(pr(u)).Fits w (readings (profile u)))
    (hdr : ∀ u,Header (head(u)) geo task.cube.cables task.cube.cells dir.entries (readings (profile u)))
    (reserve : base+7*dir.candidates≤geo) (endGeo : geo+5*task.cube.cables≤task.cube.header.header)
    (geoFit : geo<2^w) (teams : dir.teams≤2^w) (procs : dir.processors≤2^w) (fields : dir.fields≤2^w)
    (literal : dir.literal<2^w) (cells : task.cube.cells≤2^w) (stride : task.cube.cellStride≤2^w)
    (capacity : ∀ c,suppliedSize N cell c+gap+(∑ j,if cell (original j)=c then dir.description else 0)≤task.cube.cellStride)
    {I : Type} [Fintype I] {sc : I → Fin task.cube.cells} {sid : I ↪ ℕ} {sw : I → ℕ}
    {ps : Fin (R+1) → Pins.Layout} (B : Fin (R+1) → BroadcastFrame) (processor : ∀ u,Pins.ProcessorFields (ps u))
    {guess : Fin (R+1) → ℕ → Bool} (source : ∀ u,ProfileRouteInputs (processor u) (B u) (H u).pub (guess u) (published(u)))
    (team : ∀ u,(B u).team=u.val)
    (write : ∀ u,SlottedWriter task.cube dir (p₀(u)) (l₀(u)) (ps u) (H u).pub (mid u) base sc sid sw)
    {old : Fin (R+1) → Fin 81 → Word w} {fresh gates outputs width off ell controls X : ℕ}
    {Gbits : Fin (R+1) → List Bool} {claims : Fin (R+1) → List (List Bool)} {pad : Fin (R+1) → ℕ}
    {raw : Broadcast task.cube.n task.cube.header.d task.cube.header.cap}
    (room : ∀ u,PinnedRawInput (ar:=task.cube) (D:=dir) (pp:=p₀(u)) (lp:=l₀(u)) (pub:=(H u).pub)
      (slotted:=mid u) (base:=base) (B u) (old u) fresh gates outputs width off ell controls
      (Gbits u) (claims u) (pad u) raw R X)
    (decoded : (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) raw.1),
      fun row j => readCode (task.cube.header.cap+1) (raw.2 row j))=decl)
    (history : ∀ u, ∃ (regs lastReg : Bank w) (events : List (TeamRAM.Event w)) (last : Memory w)
      (W : WriterHistory task.cube.n (Cube.Tally.selectorWidth task.cube.n task.cube.K task.cube.h)
        (H u).pub (H u).macros regs (published(u)) events lastReg last),
      DataReady (H u).pub W.dataInput ∧
      (DataWriter.layout (readings (H u).pub) (readings W.dataInput)).output=task.cube.records ∧
      src u=readings W.sharedInput) :
    (∀ u,(hostLayout owned.pub owned.output u).packets=task.cube.header.packetBase ∧
      (hostLayout owned.pub owned.output u).singles=task.cube.singleBank) ∧
    ∃ scan before : Fin (R+1) → ℕ → ℕ, ∃ row : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin task.cube.cables,
      HostTables (blocks:=task.cube.header.blocks) (b:=task.cube.b) (h:=task.cube.h) (K:=task.cube.K) (s:=task.cube.s)
        N cell edgeID portID (SignedPrep.signedChooserLayout task.cube g.frame geo) (NativeDemands.cableOrder N cell edgeID)
        row labels (chosen task.cube.b task.cube.s matchQ.val.1) group Fin.valEmbedding owned.pub owned.output
        task.cube.cellBank task.cube.cellStride before scan rfl := by
  choose regs lastReg events last W ready records shared using history
  have reached (u : Fin (R+1)) :=
    writer.signed_pinned_host u dir N cell aux siteID edgeID portID F (x u) (net u) ids fieldRoom hk wordFit positive
      original live liveWidth bounds base geo gap (profile u) (mid u) alphabet (write u) (img u) (place u) (fit u)
      (hdr u) reserve geoFit teams procs fields literal cells stride (by omega) (room u) symbols handoff matchQ.val
      observed decoded (W u) (ready u) (records u) (shared u)
  refine ⟨fun u => ?_,?_⟩
  · obtain ⟨_,_,_,_,_,pointers,_⟩ := reached u
    exact pointers
  have pubs : owned.pub=(fun u => (H u).pub) := funext handoff.pub
  let target (chosenGroup : Fin task.cube.header.d → Fin (R+1)) (chosenPub : Fin (R+1) → Arg → Word w) : Prop :=
    ∃ scan before : Fin (R+1) → ℕ → ℕ, ∃ row : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin task.cube.cables,
      HostTables (blocks:=task.cube.header.blocks) (b:=task.cube.b) (h:=task.cube.h) (K:=task.cube.K) (s:=task.cube.s)
        N cell edgeID portID (SignedPrep.signedChooserLayout task.cube g.frame geo) (NativeDemands.cableOrder N cell edgeID)
        row labels (chosen task.cube.b task.cube.s matchQ.val.1) chosenGroup Fin.valEmbedding chosenPub owned.output
        task.cube.cellBank task.cube.cellStride before scan rfl
  change target group owned.pub
  apply (congrArg₂ target observed.allocation pubs.symm).mp
  refine HostTables.ofSignedHosts (controls:=fun _ => controls) task dir N cell aux siteID edgeID portID F (fun u => (H u).pub)
    profile mid owned.output (fun u => p₀(u)) (fun u => l₀(u)) x B processor labels ownerMap matchQ.val
    (fun u => (handoff.frame u).symm) net ids fieldRoom img place hdr (fun u => (write u).rawStart) reserve endGeo
    source team capacity ?_
  intro u
  obtain ⟨z,retention,entry,selected,pointer,_,earlier,row,aligned,physical,interval,resident⟩ := reached u
  refine ⟨readings (W u).dataInput,powerHeaderImage task.cube (B u).dst (readings z.val.2.2),
    readings z.val.2.2,?_⟩
  rw [handoff.pub u] at retention entry selected pointer
  change ResidentRows (HostScatter.Layout.fromFrame (readings (owned.pub u) 0) (readings (owned.output u))) _ _ _ _ _ _ _ _ _ _ _ at resident
  rw [handoff.pub u] at resident
  exact ⟨retention,entry,selected,pointer,earlier,row,aligned,physical,interval,resident⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
