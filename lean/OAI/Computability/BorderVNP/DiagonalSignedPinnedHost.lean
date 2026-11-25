import OAI.Computability.BorderVNP.DiagonalReturnedHostTables
import OAI.Computability.BorderVNP.DiagonalSignedPublishedIntervalRows
import OAI.Computability.BorderVNP.DiagonalSignedPublishedOwner
import OAI.Computability.BorderVNP.DiagonalSignedPublishedHostPointers
import OAI.Computability.BorderVNP.RoutingISASignedPrepBroadcast

/-! # The host of an actual signed chooser prefix on its recovered assignment -/

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
open private read_write from OAI.Computability.BorderVNP.CubePhysicalDeclarationWords
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 5500

private theorem selected_axis_of_cast {n d cap blocks b h K s : ℕ}
    (raw : Broadcast n d cap) (select : Packet n d blocks → Selector n K h)
    (size : cap = declarationCap n d blocks b h s) (same : size ▸ raw=broadcast b s select) :
    Fin.ofNat (n+1) (readCode (n+1) raw.1)=chosen b s select := by
  subst cap
  have fst : raw.1=(broadcast b s select).1 := congrArg Prod.fst same
  rw [fst]
  apply Fin.ext
  simp only [broadcast,read_write,Fin.ofNat,Fin.val_mk,Nat.mod_eq_of_lt (chosen b s select).isLt]

private theorem broadcast_of_decoded {cap teams : ℕ} (a : CubeArena.Layout)
    (own : (Packet a.n a.header.d a.header.blocks → Selector a.n a.K a.h) → Fin a.header.d → Fin (teams+1))
    (q : NativeAssignments.Routed (b:=a.b) (s:=a.s) own) (raw : Broadcast a.n a.header.d cap)
    (size : cap=declarationCap a.n a.header.d a.header.blocks a.b a.h a.s)
    (checked : declarationInRange raw)
    (same : (Fin.ofNat (a.n+1) (readCode (a.n+1) raw.1),fun row j => readCode (cap+1) (raw.2 row j)) =
      (Routed.encode own q).declaration) : size ▸ raw=broadcast a.b a.s q.1 := by
  subst cap
  let words : CheckedBroadcast a := ⟨raw,checked⟩
  exact congrArg Subtype.val ((declared_iff_routeBroadcast a own words q).mp same.symm)

variable {R r t pins₀ link inner e₀ w : ℕ} {Edge : Type} {G : Wiring R r t pins₀ link inner e₀ Edge}
variable {pin : Fin pins₀ → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {histDir : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {ownedOrigin ownedStride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L histDir pp lp owner ownedOrigin ownedStride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
variable (u : Fin (R+1))
variable {D s n d k b : ℕ} {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
    {a : CubeArena.Layout} (dir : Directory.Layout) (N : Network D P bits) (cell : N.Site → Fin a.cells)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin a.cables) (portID : P ↪ Fin n)
    (F : Fields s a.cables n a.cells d k b σ) (x : σ → Bool)
    (net : Represents N cell aux siteID edgeID portID F x) (ids : ∀ c,(F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k ≤ b) (wordFit : b ≤ w) (positive : 0<a.cells)
    (original : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (liveWidth : ∀ j,bits (live j)=dir.block) (bounds : dir.DestinationBounds)
    (base origin gap : ℕ) (before mid : Memory w)

local notation3 (prettyPrint := false) "pub" => (H u).pub
local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "pr" => privateLayout head origin a.cables a.cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "tables" => bases origin a.cables a.cells dir.entries
local notation3 (prettyPrint := false) "placedOriginal" => ISA.placement (readings mid) (pr).raw
local notation3 (prettyPrint := false) "placedLive" => ISA.placement (readings mid) (tables).livePairs
local notation3 (prettyPrint := false) "rows" => dir.directory placedOriginal placedLive
local notation3 (prettyPrint := false) "published" => readings (ISA.publish mid head base rows)
local notation3 (prettyPrint := false) "geometry" => LabelIndex.layout head published
local notation3 (prettyPrint := false) "list" => NativeDemands.rows N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "recv" => NativeDemands.receiver N cell edgeID portID dir original live gap bounds

local notation3 (prettyPrint := false) "width₀" => fun i : Fin (list).length => list[i.val].width

variable {decl : LengthDeclaration a.n a.header.d}
variable {group : Fin a.header.d → Fin (R+1)} {owned : TeamRows.Returns (Fin (R+1)) a w}

variable {template : Frame} {id : TableEntry a.n a.b a.h a.K a.s → ℕ} {count : ℕ}

local notation3 (prettyPrint := false) "il" => signedChooserLayout a head origin
variable (alphabet : 0<a.header.d)
local notation3 (prettyPrint := false) "lab" => meanPackedLabel N cell recv width₀ (List.finRange a.cells) a.n a.header.d alphabet
local notation3 (prettyPrint := false) "who" => greedyOwner (blocks:=a.header.blocks) (K:=a.K) (h:=a.h) R a.b a.s lab recv width₀
local notation3 (prettyPrint := false) "entryMem" => Packing.Directory.ISA.publish mid head base rows

include net ids wireFit hk wordFit positive liveWidth in
/-- On the team's actual interval return and writer history the entire host reads its
canonical sparse rows; its physical receiving cell uses that same assignment's greedy owner. -/
theorem SharedWriters.signed_pinned_host
    {I : Type} [Fintype I] {sc : I → Fin a.cells} {sid : I ↪ ℕ} {sw : I → ℕ} {sourcePins}
    (write : SlottedWriter a dir placedOriginal placedLive sourcePins pub mid base sc sid sw)
    (img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings before))
    (place : (pr).Image (readings before) dir.entries (readings mid)) (fit : (pr).Fits w (readings before))
    (hdr : Header head origin a.cables a.cells dir.entries (readings before))
    (scratch : base+7*dir.candidates≤origin) (originFits : origin<2^w)
    (teams : dir.teams≤2^w) (procs : dir.processors≤2^w) (fields : dir.fields≤2^w) (literal : dir.literal<2^w)
    (cells : a.cells≤2^w) (stride : a.cellStride≤2^w) (below : origin+3*a.cables≤a.header.header)
    {bf : BroadcastFrame} {old : Fin 81 → Word w} {fresh gates outputs width off ell controls X : ℕ}
    {inputBits : List Bool} {claims : List (List Bool)} {pad : ℕ} {raw : Broadcast a.n a.header.d a.header.cap}
    (room : PinnedRawInput (ar:=a) (D:=dir) (pp:=placedOriginal) (lp:=placedLive) («pub»:=pub) (slotted:=mid) (base:=base)
      bf old fresh gates outputs width off ell controls inputBits claims pad raw R X)
    (writer : SharedWriters f g src) (symbols : SymbolFrame g (src anchor) a.header.blocks a.K a.h decl group)
    (handoff : OwnedHandoff f g src a decl group template id count owned)
    (q : NativeAssignments.Routed (b:=a.b) (s:=a.s) who)
    (receipt : ObservedOwned a decl group owned who (f.receivedRows g group) q)
    (decoded : (Fin.ofNat (a.n+1) (readCode (a.n+1) raw.1),fun pair j => readCode (a.header.cap+1) (raw.2 pair j))=decl)
    {reg rt : Bank w} {last : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory a.n (Cube.Tally.selectorWidth a.n a.K a.h) pub (H u).macros reg entryMem es rt last)
    (ready : DataReady pub W.dataInput) (records : (DataWriter.layout (readings pub) (readings W.dataInput)).output=a.records)
    (source : src u=readings W.sharedInput) :
    ∃ z : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub (H u).macros reg entryMem,
    let axis := chosen a.b a.s q.1
    let frame := readings (owned.pub u) 0
    let input := powerHeaderImage a bf.dst (readings z.val.2.2)
    CubeAllocation.HostRetention a frame published (readings W.dataInput) (readings (owned.output u)) ∧
    NativeEntry a frame controls axis R input published (readings W.dataInput) ∧
    (∀ c : Fin a.cells, (a.receivingOwner frame axis R input c.val).val=routedOwnerWord a who lab q c.val) ∧
    published (frame+72)=a.hostDirectory ∧
    ((hostLayout owned.pub owned.output u).packets=a.header.packetBase ∧ (hostLayout owned.pub owned.output u).singles=a.singleBank) ∧
    ∃ earlier : ℕ → ℕ, ∃ row : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin a.cables,
      (∀ e, (row (NativeDemands.cableOrder N cell edgeID e)).val=(edgeID e.val).val) ∧
      PhysicalRows N cell il earlier (NativeDemands.cableOrder N cell edgeID) row Fin.valEmbedding lab
        (productCode a.n a.header.d a.alphabet rfl) ∧ (il).Image earlier a.cables (readings z.val.2.2) ∧
      ResidentRows (hostLayout owned.pub owned.output u) il earlier (readings z.val.2.2) (readings (owned.output u))
        a.n a.header.d a.header.blocks a.b a.h a.K a.s := by
  obtain ⟨tr,midReg,selected,run,_,_,beforeWriter,_⟩ :=
    write.raw_schedule bf old fresh gates outputs width off ell controls (H u).macros reg inputBits claims pad raw R X
      room.boot room.geometry room.frameSpace room.copied room.alphabet room.blocks room.bank room.arena room.labels
      room.cells room.teamCount room.teamArena room.budget room.million room.scaled room.controlLow room.pointers
      room.processors room.payload room.fields room.rawSpace room.records
  let z : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub (H u).macros reg entryMem :=
    ⟨⟨tr,midReg,selected⟩,run⟩
  have rawRead := broadcast_of_decoded a who q raw
    (show a.header.cap=declarationCap a.n a.header.d a.header.blocks a.b a.h a.s by rw [room.geometry]; rfl)
    (beforeWriter.sound W.prefixRun).1.1 (decoded.trans receipt.observed.1.symm)
  have axisRead := selected_axis_of_cast raw q.1 (b:=a.b) (s:=a.s)
    (show a.header.cap=declarationCap a.n a.header.d a.header.blocks a.b a.h a.s by rw [room.geometry]; rfl) rawRead
  have declAxis : chosen a.b a.s q.1=decl.1 := congrArg Prod.fst receipt.observed.1
  have entry : NativeEntry a head controls decl.1 R (powerHeaderImage a bf.dst (readings z.val.2.2))
      published (readings W.dataInput) :=
    (axisRead.trans declAxis) ▸ (beforeWriter.sound W.prefixRun).2.1
  refine ⟨z,?_⟩
  intro axis frame input
  have chooser := signed_published_interval_rows a dir N cell aux siteID edgeID portID F x net ids wireFit hk wordFit positive
    original live liveWidth bounds pub base origin gap before mid write img place fit hdr scratch originFits teams procs fields
    literal cells stride room below z.property
  have addresses := room.signed_host_operands
  have physical := writer.published_host_rows symbols handoff receipt u W ready records source N cell edgeID lab il rfl rfl rfl
    entry addresses.1 addresses.2.1 addresses.2.2 (by
      obtain ⟨mem,run,fit,fields,cables,low,row,ids,physicalRows⟩ := chooser
      exact ⟨mem,run,fit,fields,cables,low,row,fun e => congrArg Fin.val (ids e),physicalRows⟩)
  have whoReads := signed_published_owner_word a dir N cell aux siteID edgeID portID F x net ids wireFit hk wordFit positive
    original live liveWidth bounds pub base origin gap before mid write img place fit hdr scratch originFits teams procs fields
    literal cells stride bf old fresh gates outputs width off ell controls (H u).macros reg inputBits claims pad X raw room z alphabet q rawRead
  have frameRead : frame=head := congrFun (congrArg readings (handoff.pub u)) 0
  have host : published (head+72)=a.hostDirectory := by
    have room' := room.arena
    obtain ⟨_,_,_,_,_,_,_,_⟩ := a.writer_order
    exact room.boot.arenaOperand a old fresh inputBits.length gates outputs width off ell
      (k:=72) (value:=a.hostDirectory) rfl (by omega)
  have srcPointers : CubeAllocation.HostPointers a g.frame (src u) := by
    rw [handoff.frame u,source]
    exact room.signed_host_pointers.after_data W entry ready records room.frameSpace
  have hostWords := writer.owned_host_words symbols handoff receipt u srcPointers
  exact ⟨physical.1,physical.2.1,fun c => by
    change (a.receivingOwner frame (chosen a.b a.s q.1) R input c.val).val=_
    rw [frameRead,←axisRead]
    exact whoReads c,frameRead ▸ host,⟨hostWords.2.1,hostWords.2.2.1⟩,physical.2.2⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
