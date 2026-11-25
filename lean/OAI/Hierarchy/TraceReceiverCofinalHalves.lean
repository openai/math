import OAI.Hierarchy.TraceCompactSeed
import OAI.Hierarchy.TraceReceiverWarmEntry
import OAI.ThreeFlat.Diagonal.InitialSeedContinuation

namespace OAI
/-! # All four true seed-half fields in the selected compact receiver -/
namespace Hierarchy.TraceCompactSeed
open ThreeFlat Diagonal Diagonal.PhysicalStage NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure NavigationDirectory TraceAdmission TraceDistribution
open private mountedHeader selected_sources from OAI.Hierarchy.TraceCompactSeed
open Filter
open scoped Classical Fin.CommRing
noncomputable section
section Seed

variable {F : Type} [Field F] [Fintype F] {w pc regs slots S base d fuel : ℕ}
variable (B : Block F) (axes n cap off rowSlots : ℕ) (M : Machine (64*w) pc regs slots)
    (fit : NativeTrace.Fits M S base d fuel) (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w))
    (raw gateBase : ℕ)
set_option quotPrecheck false
local notation "W" => 64*w
local notation "G" => TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs slots d
local notation "ed" => GridStructuralHeader.directory (w:=w) B axes n cap
local notation "tc" => TraceReceiverTemplate.count G
local notation "libSize" => RAM.HistoryStageBody.Physical.libraryWords B W
local notation "total" => GridStructuralHeader.wordCount (ed).length tc libSize
local notation "text" => SelfAdvice.textSize W pc slots
local notation "phase" => GridStructuralHeader.receiverPhase w text total
local notation "beta" => GridStructuralHeader.recipientBase w
local notation "src" => 2+text+W*(1+(ed).length+tc)
local notation "params" => GridStructuralHeader.parameters B axes n cap M fit hF st raw gateBase
local notation "arch" => archive B w beta axes off rowSlots cap src phase
local notation "P" => B.repeat n
local notation "rem" => axes-(P).charge
local notation "ss" => (P).directory rem axes
local notation "edges" => (P).finalEdges rem axes

variable (textFit : SelfAdvice.textSize (64*w) pc slots ≤ w^2) (self : Fin (w^2)→Bool)
    (index : Word (64*w)) (sel : Fin (cap+1)→Bool) {p : ℕ} (input : ℕ→Bool)
local notation "head" => mountedHeader B axes n cap M fit hF st raw gateBase textFit self index sel
local notation "pins" => (fun j : Fin p => input j.val)
local notation "mem" => TickMountedPins.memory (w:=W) pins
local notation "bits" => GridStructuralHeader.selectorBit cap sel

theorem initial_half_rows
    (padded : (mountedHeader B axes n cap M fit hF st raw gateBase textFit self index sel).length ≤ p)
    (stored : TraceFactorReceiver.Selector.headerReads (SelfAdvice.textSize (64*w) pc slots)
      textFit self index (GridStructuralHeader.parameters B axes n cap M fit hF st raw gateBase) sel input)
    {k : ℕ} (hk : 2 ≤ k+1) (ax : k+1=axes)
    (room : 2+(head).length ≤ beta) (body : W*(arch).histWords ss ≤ cap)
    (fitSeed : TraceSeedWriter.Fits (arch) ss edges n k W)
    (limits : (arch).TraceLimits (2^w) ((arch).control:Word W) ss edges (2^(3*w/5)))
    (term : (arch).TerminalRoom ss edges W)
    (sumWord : 2*(arch).initialDegree*(arch).relayWidth<2^W) :
    let result:=TraceSeedWriter.memory (arch) ss edges [] bits mem n
    State.HalfRows ((arch).cursorSeedSites B hk (w/2) off rowSlots ax (by change 2^axes=2^(k+1);rw [ax]))
      (fun i=>(arch).initialRecords≤ i ∧ i<(arch).metadataEnd) (fun i=>(result i).val) := by
  intro result
  have srcOk:=selected_sources B axes n cap off rowSlots M fit hF st raw gateBase textFit self index sel input
    padded stored hk ax room body fitSeed limits term
  have ready:=TraceSeedWriter.ready (arch) ss edges B hk (w/2) off rowSlots rfl ax
    (by change 2^axes=2^(k+1);rw [ax]) rfl [] [] bits mem n fitSeed.space fitSeed.mount srcOk
    fitSeed.bits fitSeed.axes fitSeed.degree fitSeed.lanes fitSeed.word rfl fitSeed.clock
  have lanes : (arch).remainingLanes=2^(k+1):=by change 2^axes=2^(k+1);rw [ax]
  have edge : (B.cursorState hk (w/2) off rowSlots).edgeCount≤2^W := by
    have count:=fitSeed.space.widthsBefore
    have top:=fitSeed.space.controlRoom
    change (Fintype.card (Fin (k+1))*2^B.exponent 0)*2^(k+1)≤_
    rw [Fintype.card_fin,ax]
    change (arch).cursor.width+(axes*2^B.exponent 0)*2^axes≤(arch).control at count
    omega
  exact Archive.InitialNodeMetadata.cursorHalfRows (arch) B hk (w/2) off rowSlots ax lanes rfl rfl result
    ready.nodes fitSeed.space.meta.endFit fitSeed.degree edge fitSeed.bits sumWord


end Seed

/-- The native history registrar explicitly retains the original seed metadata
up to its end. These records are below the actual last heap and lie in S20–S40.
The two spans are those of the published frame’s `NativeNavigation.halfArchiveCell`. -/
theorem seen_half_rows {W u heap d l lo hi : ℕ} {A : State d l} {O : A.ArchiveSites}
    (origin registered entry : Memory W)
    (initial : State.HalfRows O (fun i=>lo≤ i ∧ i<hi) (fun i=>(origin i).val))
    (source : ∀ i,lo≤ i→i<hi→ registered i=origin i)
    (endSeed : hi≤heap) (start : TickWorkspace.base u 20≤lo) (finish : heap≤TickWorkspace.base u 40) :
    State.HalfRows O (fun i =>
      (TickWorkspace.base u 20 ≤ i ∧ i < TickWorkspace.base u 40) ∨
      (TickWorkspace.base u 49 ≤ i ∧ i < TickWorkspace.base u 53))
      (fun i=>(TraceReceiverWarmEntry.seen heap registered entry i).val) := by
  apply initial.transfer
  · intro i h
    simp only [TraceReceiverWarmEntry.seen,ite_eq_left (h.2.trans_le endSeed),source i h.1 h.2]
  · exact fun i h=>Or.inl ⟨start.trans h.1,h.2.trans_le (endSeed.trans finish)⟩

end
end Hierarchy.TraceCompactSeed

end OAI
