import OAI.Computability.BorderVNP.DiagonalJointOwnedCableClock
import OAI.Computability.BorderVNP.DiagonalSignedPinnedHost
import OAI.Computability.BorderVNP.DiagonalSignedPublishedWeightImage
import OAI.Computability.BorderVNP.DiagonalPinnedBroadcastReadback

/-! # The genuine signed source publication supplies the pre-call owned clock -/

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
open private pointer_fit from OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostPointers
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 5500

variable {R r t pins₀ link inner e₀ w : ℕ} {Edge : Type} {G : Wiring R r t pins₀ link inner e₀ Edge}
variable {pin : Fin pins₀ → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {histDir : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {ownedOrigin ownedStride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L histDir pp lp owner ownedOrigin ownedStride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
variable (u : Fin (R+1))
variable {D s n d k b : ℕ} {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
    {task : SignedTaskArena.Layout} (dir : Directory.Layout) (N : Network D P bits) (cell : N.Site → Fin task.cube.cells)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin n)
    (F : Fields s task.cube.cables n task.cube.cells d k b σ) (x : σ → Bool)
    (net : Represents N cell aux siteID edgeID portID F x) (ids : ∀ c,(F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k ≤ b) (wordFit : b ≤ w) (positive : 0<task.cube.cells)
    (original : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (liveWidth : ∀ j,bits (live j)=dir.block) (bounds : dir.DestinationBounds)
    (base origin gap : ℕ) (before mid : Memory w)

local notation3 (prettyPrint := false) "pub" => (H u).pub
local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "pr" => privateLayout head origin task.cube.cables task.cube.cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "tables" => bases origin task.cube.cables task.cube.cells dir.entries
local notation3 (prettyPrint := false) "placedOriginal" => ISA.placement (readings mid) (pr).raw
local notation3 (prettyPrint := false) "placedLive" => ISA.placement (readings mid) (tables).livePairs
local notation3 (prettyPrint := false) "rows" => dir.directory placedOriginal placedLive
local notation3 (prettyPrint := false) "published" => readings (ISA.publish mid head base rows)
local notation3 (prettyPrint := false) "geometry" => LabelIndex.layout head published
local notation3 (prettyPrint := false) "list" => NativeDemands.rows N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "recv" => NativeDemands.receiver N cell edgeID portID dir original live gap bounds

local notation3 (prettyPrint := false) "width₀" => fun i : Fin (list).length => list[i.val].width

variable {decl : LengthDeclaration task.cube.n task.cube.header.d}
variable {group : Fin task.cube.header.d → Fin (R+1)}

variable {template : Frame} {id : TableEntry task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s → ℕ} {count : ℕ}

variable (U : Fin (R+1) → PinStart SparseExterior.driver e₀ w)
    (active : PinStart.JointPrefix id U)
local notation3 (prettyPrint := false) "owned" => PinStart.ownedVisits (ar:=task.cube) U active
local notation3 (prettyPrint := false) "v" => PinStart.visits id U (active u)
local notation3 (prettyPrint := false) "il" => signedChooserLayout task.cube head origin
variable (alphabet : 0<task.cube.header.d)
local notation3 (prettyPrint := false) "lab" => meanPackedLabel N cell recv width₀ (List.finRange task.cube.cells) task.cube.n task.cube.header.d alphabet
local notation3 (prettyPrint := false) "who" => greedyOwner (blocks:=task.cube.header.blocks) (K:=task.cube.K) (h:=task.cube.h) R task.cube.b task.cube.s lab recv width₀
local notation3 (prettyPrint := false) "entryMem" => Packing.Directory.ISA.publish mid head base rows

include net ids wireFit hk wordFit positive liveWidth in
/-- The checked signed publication on the original network determines the
physical padding guard and cable clock at this team's genuine owned return.
The same selected interval and declared tableau supply its group-weight image. -/
theorem SharedWriters.signed_pinned_argument_rows
    {I : Type} [Fintype I] {sc : I → Fin task.cube.cells} {sid : I ↪ ℕ} {sw : I → ℕ} {sourcePins}
    (write : SlottedWriter task.cube dir placedOriginal placedLive sourcePins pub mid base sc sid sw)
    (img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings before))
    (place : (pr).Image (readings before) dir.entries (readings mid)) (fit : (pr).Fits w (readings before))
    (hdr : Header head origin task.cube.cables task.cube.cells dir.entries (readings before))
    (scratch : base+7*dir.candidates≤origin) (originFits : origin<2^w)
    (teams : dir.teams≤2^w) (procs : dir.processors≤2^w) (fields : dir.fields≤2^w) (literal : dir.literal<2^w)
    (cells : task.cube.cells≤2^w) (stride : task.cube.cellStride≤2^w) (below : origin+3*task.cube.cables≤task.cube.header.header)
    {bf : BroadcastFrame} {old : Fin 81 → Word w} {fresh gates outputs width off ell controls X : ℕ}
    {inputBits : List Bool} {claims : List (List Bool)} {pad : ℕ} {raw : Broadcast task.cube.n task.cube.header.d task.cube.header.cap}
    (room : PinnedRawInput (ar:=task.cube) (D:=dir) (pp:=placedOriginal) (lp:=placedLive) («pub»:=pub) (slotted:=mid) (base:=base)
      bf old fresh gates outputs width off ell controls inputBits claims pad raw R X)
    (writer : SharedWriters f g src) (symbols : SymbolFrame g (src anchor) task.cube.header.blocks task.cube.K task.cube.h decl group)
    (handoff : OwnedHandoff f g src task.cube decl group template id count owned)
    (q : NativeAssignments.Routed (b:=task.cube.b) (s:=task.cube.s) who)
    (receipt : ObservedOwned task.cube decl group owned who (f.receivedRows g group) q)
    (decoded : (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) raw.1),
      fun pair j => readCode (task.cube.header.cap+1) (raw.2 pair j))=decl)
    {reg rt : Bank w} {last : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory task.cube.n (Cube.Tally.selectorWidth task.cube.n task.cube.K task.cube.h) pub (H u).macros reg entryMem es rt last)
    (ready : DataReady pub W.dataInput) (records : (DataWriter.layout (readings pub) (readings W.dataInput)).output=task.cube.records)
    (source : src u=readings W.sharedInput)
    (templateFit : LocalRow.templateLimit task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s<2^w)
    (site : bf.team=u.val)
    (cap : ∀ pair, load (cablePair (NativeDemands.cableOrder N cell edgeID) (crossSrc N cell) (crossDst N cell) lab)
      (crossWidth N cell ∘ (NativeDemands.cableOrder N cell edgeID).symm) pair ≤ task.cube.header.blocks*(task.cube.h*task.cube.b)) :
    ∃ z : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub (H u).macros reg entryMem,
      let here := readings (U u).pub 0
      let mem := readings (v).owned.val.2.2
      let native := HostScatter.Layout.fromFrame here mem
      let prof := powerHeaderImage task.cube bf.dst (readings z.val.2.2)
      GroupWeights.PhysicalImage (weightLayout task.cube here decl.1.val) prof task.cube.header.blocks task.cube.b task.cube.K task.cube.h decl lab recv width₀ ∧
      (∃ scheduled, GroupWeights.ScheduleResult (weightLayout task.cube here decl.1.val) (teamLayout task.cube R) prof scheduled ∧
        CubeArena.DirectoryImage task.cube here controls decl.1 R prof scheduled (readings W.dataInput) ∧
        (TeamBudget.Layout.mk (R+1) X task.cube.teamTotals).Passes scheduled) ∧
      Padding.Returned task.cube decl.1 group u here w mem (fun k => readings z.val.2.2 ((il).widths+k)) ∧
      ∃ _ : native.ScheduledCables mem (task.cube.header.blocks*(task.cube.h*task.cube.b)) decl.1 (fun x => (group x).val),
        native.team=u.val ∧ native.count=task.cube.cables := by
  have rawRead := W.broadcast_of_pinned_decode write bf old fresh gates outputs width off ell controls inputBits claims pad raw R X
    room who q (decoded.trans receipt.observed.1.symm)
  obtain ⟨z,_,entry,_⟩ := writer.signed_pinned_host u dir N cell aux siteID edgeID portID F x net ids wireFit hk
    wordFit positive original live liveWidth bounds base origin gap before mid alphabet write img place fit hdr scratch originFits
    teams procs fields literal cells stride below room symbols handoff q receipt decoded W ready records source
  refine ⟨z,?_⟩
  intro here mem native prof
  obtain ⟨before₀,interval,intervalFit,fields₀,columns,low,row,_,physical⟩ :=
    signed_published_interval_rows task.cube dir N cell aux siteID edgeID portID F x net ids wireFit hk wordFit positive
      original live liveWidth bounds pub base origin gap before mid write img place fit hdr scratch originFits teams procs
      fields literal cells stride room below z.property
  let recovered := Scatter.Assignment.Routed.trueDeclaration task.cube.b task.cube.s q.1
  have image : GroupWeights.PhysicalImage (weightLayout task.cube head recovered.1.val) prof
      task.cube.header.blocks task.cube.b task.cube.K task.cube.h recovered lab recv width₀ := signed_published_weight_image task.cube dir N cell aux siteID edgeID portID F x net ids wireFit hk wordFit positive
    original live liveWidth bounds pub base origin gap before mid write img place fit hdr scratch originFits teams procs fields
    literal cells stride bf old fresh gates outputs width off ell controls (H u).macros reg inputBits claims pad X raw room z alphabet q rawRead
  have trueDecl : Scatter.Assignment.Routed.trueDeclaration task.cube.b task.cube.s q.1=decl := receipt.observed.1
  change recovered=decl at trueDecl
  rw [trueDecl] at image
  have axis : chosen task.cube.b task.cube.s q.1=decl.1 := congrArg Prod.fst trueDecl
  change NativeEntry task.cube here controls (chosen task.cube.b task.cube.s q.1) R prof published (readings W.dataInput) at entry
  rw [axis] at entry
  have hereEq : here=head := congrFun (congrArg readings (handoff.pub u)) 0
  have fixed : CubeAllocation.HostPointers task.cube head published := by
    intro idx member value operand
    exact room.boot.arenaOperand task.cube old fresh inputBits.length gates outputs width off ell operand
      (pointer_fit task.cube room.arena templateFit member operand)
  have cableCount : readings entryMem (head+7)=task.cube.cables := by
    obtain ⟨_,edges,_,_,_,_,_,_,_,_⟩ := signed_published_cable_rows task.cube dir N cell aux siteID edgeID portID F x
      net ids wireFit hk wordFit positive original live liveWidth bounds pub base origin gap before mid
      write img place fit hdr scratch originFits teams procs fields literal cells stride
    exact edges
  have teamWord : readings entryMem head=u.val := room.boot.team.trans site
  have entryHere := entry
  rw [hereEq] at entry
  have paid := SharedWriters.owned_argument_rows (a:=task) (f:=f) (q:=q) (ctl:=controls) (broadcast:=bf.dst) U active lab recv width₀ writer symbols handoff receipt u W ready records source
    N cell (signedChooserLayout task.cube head origin) (readings before₀) (readings z.val.2.2) rfl physical interval
    intervalFit fields₀ rfl columns rfl low fixed teamWord cableCount cap entry image
  obtain ⟨scheduled,schedule,remaining⟩ := entryHere.image
  have useSchedule := schedule
  rw [hereEq,←trueDecl] at useSchedule
  have budget := W.pinned_budget_on_return write bf old fresh gates outputs width off ell controls inputBits claims pad raw R X
    room z q.1 rawRead scheduled useSchedule
  rw [←hereEq] at image
  exact ⟨image,⟨scheduled,schedule,remaining,budget⟩,paid⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
