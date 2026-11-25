import OAI.Hierarchy.DescentPostedSnapshotRankReturn
import OAI.Hierarchy.DescentIssuedSnapshotRanks
import OAI.Hierarchy.DescentResetHubRectangle

namespace OAI
/-! # Input evidence for the snapshot rank written by an issued reset -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {w : ℕ}

set_option hygiene false
local notation "rankInputBoard" => ctl.board
local notation "rankInputPacket" => ctl.bitsR
local notation "rankInputA" => named G S (rankInputBoard) k tail age p f g drift degree payload e previous M nextM C (rankInputPacket)
      oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "rankInputV" => (rankInputA).successor
local notation "rankInputStart" => (rankInputA).stageStart floor
local notation "rankInputBase₀" => (rankInputA).rebased (rankInputStart)
local notation "rankInputCc" => S.groupWidth k tail age
local notation "rankInputCal" => capCalendar G.b S.rounds g S.height
local notation "rankInputCap" => ((rankInputCal).take age).prod*256
local notation "rankInputHt" => GroupStage.depthBound venue.degree n f g
local notation "rankInputWide" => laneBits ((rankInputCc)+k) payload (S.localWalshBits p ((rankInputCc)+k) f (quota S.rounds))
local notation "rankInputSh" => namedStencil G S (rankInputBoard) k tail age p f g drift degree payload e previous M nextM C (rankInputPacket)
      oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "rankInputRoots" => namedRoots G S (rankInputBoard) k tail age p f g drift degree payload e previous M nextM C (rankInputPacket)
      oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "rankInputAtlas" => namedAtlas G S (rankInputBoard) k tail age p f g drift degree payload e previous M nextM C (rankInputPacket)
      oldLanes primitiveLanes printedBits venue io floor (rankInputSh) count
local notation "rankInputRc" => (rankInputA).rootPhase (rankInputSh) (rankInputStart) count io.hubs g (2^n) (rankInputRoots) w
local notation "rankInputE" => (rankInputA).estimator (rankInputStart)
local notation "rankInputBook" => atlasBook (rankInputAtlas) (rankInputSh) (rankInputStart) count io.hubs g (2^n) (rankInputRoots) w
local notation "rankInputActorBase" => (rankInputV).middle.stop (rankInputBase₀)
local notation "rankInputEarly" => (rankInputV).actorEnd (rankInputBase₀)
local notation "rankInputOlder" => namedOriginals G S (rankInputBoard) k tail age p f g drift degree payload e previous M nextM C (rankInputPacket)
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "rankInputI₀" => DateInputs.fromNamed G S (rankInputBoard) k tail age p f g drift degree payload e previous M nextM C (rankInputPacket)
      oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "rankInputU" => (rankInputI₀) previousMeta previousArguments initial prepared sceneRoom
local notation "rankInputHH" => S.hostSize age
local notation "rankInputAmp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap
set_option hygiene true

/-- The physical inputs to the selected reset. All measured words in the
constructor are inputs to the named CPU; the emitted rank is obtained by running it. -/
inductive PostedRankInputs (B : ClosedReset input ctl) (p : ℕ) (cpu : DateCode w) (bank : Bank)
    (endAddress : ℕ) (m : Memory w) : Type 2 where
  | named
      (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
      (venue : StageVenueTail.Date) (io : Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor : ℕ)
      (fitsStencil : e≤(rankInputWide)-k) (fitsSigned : e≤previous) (fitsCut : previous≤(rankInputCc)) (count : Bank)
      (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rankInputRc).PreparedFits (rankInputBook))
      (sceneRoom : (rankInputV).front.SceneRoom (rankInputEarly) ((rankInputV).issuedScene (rankInputBase₀) (rankInputOlder)) w)
      (degreeAt : venue.degree=D) (ready : (rankInputU).Ready) (pad : NativePhase w) (padded : pad.Runs m)
      (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
      (capAt : input.placement.cap=(rankInputCap)) (history : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
      (seen : stageVenue input input.valid.host io (rankInputV).funded.oldLanes (rankInputV).funded.precision floor
      (input.venueRoster input.valid.host) (pad.image m)) (popFit : count.Fits w floor)
      (popRead : pad.image m count.base=(Fintype.card input.V:Word w))
      (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      (rankInputHH)*chunks (S.groupCount age) (rankInputV).funded.oldLanes≤(io.wire x.val j.val).size)
      (oldPos : 0<(rankInputV).funded.oldLanes) (oldWidth : (rankInputV).funded.precision=S.censusBits p)
      (entryFits : (rankInputStart)<2^w) (low : k≤(rankInputE).low)
      (score : 3*(rankInputE).dim+((rankInputE).precision+Nat.clog 2 (rankInputE).hosts)+2≤w)
      (live : 0 < (rankInputAmp)) (degreePos : 0 < 32*Nat.clog 2 (2*venue.degree))
      (headerBits : Nat.clog 2 ((rankInputE).dim+2)+((rankInputE).dim+S.censusBits p) ≤ w) (hostBits : (rankInputHH) < 2^w)
      (ranksFit : venue.degree*2^(rankInputHt) < 2^w)
      (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*venue.degree)) g n ≤ w)
      (degFit : venue.degree+1 < 2^w) (laneRoom : 2^e ≤ w) (finish : (rankInputU).FinalInputs) (room : finish.Room)
      (code : cpu=DateCode.withPriorArchive pad (enterCode (rankInputA).ingress floor (rankInputU) finish io))
      (location : bank=(((rankInputV).actor).directory (rankInputActorBase)).ranks) (enclosed : (rankInputEarly)≤endAddress) :
      PostedRankInputs B p cpu bank endAddress m

theorem PostedRankInputs.ranks {B : ClosedReset input ctl} {cpu : DateCode w} {bank : Bank}
    {endAddress : ℕ} {m : Memory w} (data_ : PostedRankInputs B p cpu bank endAddress m)
    (accepted : B.Recorded p) :
    let vertex:=B.frame.host.symm.toEmbedding.trans input.vertex
    bank.Fits w endAddress ∧ ∀x:B.next.V,
      bank.read (cpu.nextMemory m) ((B.reset.rawHostRank B.terminals vertex x).val:Word w)=
        ((B.reset.denseHostRank B.terminals vertex x).val:Word w) := by
  cases data_ with
  | named drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor
      fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
      degreeAt ready pad padded gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth
      entryFits low score alive degreePos headerBits hostBits ranksFit namesFit degFit laneRoom
      finish room code location enclosed =>
    obtain ⟨fit,read⟩:=DateInputs.fromNamed_snapshot_rank_return accepted
      drift degree payload e previous M nextM oldLanes primitiveLanes printedBits venue io floor w
      fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
      degreeAt ready pad m padded gr fee capAt history branch seen popFit popRead wireRoom oldPos oldWidth
      entryFits low score alive degreePos headerBits hostBits ranksFit namesFit degFit laneRoom finish room
    subst cpu
    subst bank
    refine ⟨⟨fit.1,fit.2.1,fit.2.2.trans enclosed⟩,?_⟩
    let vertex:=B.frame.host.symm.toEmbedding.trans input.vertex
    intro x
    exact (read x).trans (congrArg (fun rankMap => ((rankMap x).val : Word w))
      (B.reset.denseHostRank_extend B.terminals vertex input.valid.host))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentDatedAddressBook.PhysicalReset ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F Pin : Type} [Field F] [Fintype Pin] {d : ℕ} {bits : Pin→ℕ} {I U : MarkedWorld F d Pin bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k len z₀ D₀ z D wire hist w age : ℕ}
    {entry : Reached I G q ε S k 0 z₀ D₀ wire hist} {exit : Reached U G q ε S k len z D wire hist}
    {path : Path entry exit}

/-- A concrete actor census issued at this reset event of the selected path. -/
inductive Path.Event.ResetRankOperands (scale : ℕ) (cpu : DateCode w) (bank : Bank)
    (endAddress : ℕ) (m : Memory w) : path.Event age → Type 2 where
  | reset {V : MarkedWorld F d Pin bits} {z' D' n h C f g cut tail : ℕ}
      {src : Reached V G q ε S k age z' D' wire hist} {ctl : ResetRates G S k D' n h C f g cut tail}
      (before : Path entry src) (B : ClosedReset src ctl) (after_ : Path B.next exit)
      (joined : (before.reset B).append after_=path)
      (native : PostedRankInputs B scale cpu bank endAddress m) :
      Path.Event.ResetRankOperands scale cpu bank endAddress m (.reset before B after_ joined)

omit [Fintype Pin] in
theorem Path.Event.ResetRankOperands.publication {scale : ℕ} {cpu : DateCode w} {bank : Bank}
    {endAddress : ℕ} {m : Memory w} {e : path.Event age}
    (operands : e.ResetRankOperands scale cpu bank endAddress m) (recorded : e.resetRecorded scale) :
    e.rankPublication bank endAddress (cpu.nextMemory m) := by
  cases operands with
  | reset before B after_ joined native => exact native.ranks recorded

end
end Hierarchy.DescentSixParty.Chronology

end OAI
