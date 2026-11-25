import OAI.Hierarchy.DescentRecordedActorDirectoryAfterRoots
import OAI.Hierarchy.DescentPhysicalResetAtlas
import OAI.Hierarchy.DescentDatedActorGateRoom

namespace OAI
/-! # Running the recorded actor directory on the public opcode alphabet -/
namespace Hierarchy.DescentDatedAddressBook.ActorSetup
open DescentDenseHostOrder DescentSixParty DescentSixParty.ResetInput.SourceFrame
open DescentSIMDLookup ProtocolRAM
noncomputable section
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h)
def printed (H c r M t a W D Ht : ℕ) : ActorSetup :=
  ⟨H,c,r,M,t,a,(roster board r Ht).card,DescentSharedBookScan.width r (2^n) D,W,D*2^Ht⟩
def printedInputs (H c r M t a W D Ht : ℕ) (pop depths line : Bank) (chart : DescentSharedBookScan.Chart) :
    (printed board H c r M t a W D Ht).Inputs :=
  ⟨pop,depths,chart,D,2^Ht,fun j=>headerControl r D (shapeAt board r Ht j),
    fun j=>opcode r (shapeAt board r Ht j),.lookup line .row⟩

private theorem start_before_end (v : ActorSetup) (base : ℕ) : base ≤ v.endAddress base := by
  obtain ⟨repeatAt,gateAt,outAt⟩ := v.gate_order base
  have beforeRepeat : (v.gate base).scalar ≤ (v.gate base).repeatBase :=
    (Nat.le_add_right ..).trans repeatAt.le
  have beforeGate : (v.gate base).repeatBase ≤ (v.gate base).gateBase := by
    rw [←gateAt]
    unfold DescentSharedLeafLookup.Public.stop
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have beforeOutput : (v.gate base).gateBase ≤ (v.gate base).output :=
    (Nat.le_add_right ..).trans outAt.le
  exact (v.scalar_before base).trans (beforeRepeat.trans (beforeGate.trans
    (beforeOutput.trans (Nat.le_add_right ..))))

end
end Hierarchy.DescentDatedAddressBook.ActorSetup

namespace Hierarchy.DescentSixParty.ClosedReset.Recorded
open DescentDatedAddressBook DescentActorRaster DescentCompiler DescentGL DescentColonies
open DescentPlainTerminal DescentPlainTerminal.Suffix DescentSIMDLookup DescentChosenRouter
open DescentResetAttachments DescentRelativeContacts DescentRosterOrder DescentTreePrefixIntervals
open DescentPacking.PackedMatch.Local DescentIssuedFallbackPanel ResetInput.SourceFrame
open DescentDenseHostOrder DescentCommonHost DescentPackedZip DescentActorRaster.CPU
open DescentFallbackPeriod DescentFallbackPeriod.Projected DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "full" => (A).wire*((A).z*G.b)*(A).cap
local notation "wid" => S.groupWidth k tail i+k
local notation "coarse" => (T).commonDepth
local notation "res" => (Z).k-coarse
local notation "ht" => GroupStage.depthBound D n f g
local notation "peer" => PackedFlow.portAt A ((A).numberedHeader (S.resetInputDigits ctl.base ctl.radix i) input.vertex).site
local notation "prev" => fun v=>(Z).placement.b (B.frame.host v)
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => (B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb input.valid.host)
local notation "H" => S.hostSize i
local notation "shapeCount" => (DescentDenseHostOrder.roster (Z).graph res ht).card
local notation "id_" => (Z).rawHostRank T rank
variable {D₁ n₁ r₁ c₁ Ht₁ width₁ a t M w cap N G₁ K R hh ll field : ℕ}
  (board : NonlinearExpanders.Graph n₁ h) (pop raw line : Bank)
  (rc : Receiver D₁ cap N n₁ r₁ c₁ (S.hostSize i) G₁ K R M hh ll t field Ht₁ w)
  (book : RootBook n₁ r₁ D₁ (2^r₁) cap field) (safe : rc.PreparedFits book)
local notation "U₁" => ActorSetup.printed board H c₁ r₁ M t a width₁ D₁ Ht₁
local notation "ops" => ActorSetup.printedInputs board H c₁ r₁ M t a width₁ D₁ Ht₁ pop raw line (book.common rc.projectionEnd H)
local notation "chart" => book.common rc.projectionEnd H
local notation "first" => rc.preparedEnd book
local notation "dir" => (U₁).directory first
local notation "scene" => (U₁).scene first
local notation "gate" => (U₁).gate first
variable {nbits : ℕ}
structure ActorPanelAt (measured : Memory w) : Prop where
  panel : PackedFlow.Padded.Published (h:=S.groupWidth k tail i) (l:=k) M t line.base idx
    (realPanel (reset:=B) rfl B.frame.basis nbits t) measured
  hosts : ∀u j,measured (book.previousNeighbors.base+((idx u).val*(A).degree+j.val))=
    (DescentFallbackRankRAM.hostDigit idx (peer u j):Word w)
  hubs : ∀u,measured (book.previousHubs.base+(idx u).val)=(((A).hub u).toNat:Word w)
  count : measured pop.base=(Fintype.card input.V:Word w)
  depth : ∀v,measured (raw.base+(idx v).val*(wid+1))=(prev v:Word w)

set_option maxHeartbeats 1000000 in
include accepted in
/-- The public receiver and root book may have different dependent index expressions
from the recorded graph. The casts here compare the two issuers before either runs. -/
theorem directory_on_public (dd : D₁=(A).degree) (nn : n₁=(Z).n) (rotor : HEq board (Z).graph)
    (rr : r₁=res) (cc : c₁=coarse) (height : Ht₁=ht) (width : width₁=wid)
    (digits : a=ActorSetup.levelBits wid D₁ Ht₁)
    (measured : Memory w) (page : RootPage r₁ (2^n₁))
    (observed : ActorPanelAt (B:=B) (M:=M) (t:=t) (nbits:=nbits) pop raw line book measured)
    (catalog : book.fallbackDegree=32*Nat.clog 2 (2*D₁) ∧ book.hubBits=g ∧ book.loadBits=f ∧ book.shapes=2^Ht₁)
    (level : wid-coarse < 2^nbits) (one : 1 < 2^nbits) (mass : 2^(wid-coarse)*full < 2^nbits)
    (shapeRoom : 2*DescentFallbackShapeTable.rows (wid-coarse) (2^(Z).n) ≤ 2^t)
    (live : 0 < full) (quotaPos : 0 < quota S.rounds) (degreePos : 0 < 32*Nat.clog 2 (2*D₁))
    (ww : 0 < w) (card : D₁*2^Ht₁ < 2^w)
    (small : ∀z : DescentContacts.Endpoint (2^n₁),z.1.2 < 2^z.1.1 → z.1.1 ≤ r₁ → ∀j sh,
      sh∈DescentFallbackLeafScan.localShape r₁ (32*Nat.clog 2 (2*D₁)) g f z j →
      DescentFallbackShapeTable.shapeNumber sh+1 < 2^w)
    (bounded : ∀v,prev v ≤ wid)
    (popLow : pop.Fits w rc.origin) (depthLow : raw.Fits w rc.origin) (depthRows : H*(wid+1) ≤ raw.size)
    (lineLow : line.base+H*chunks (2^c₁) M ≤ rc.origin) (lineFit : line.Fits w first) (lineRows : H*chunks (2^c₁) M ≤ line.size)
    (peerLow : book.previousNeighbors.Fits w rc.origin) (peerSize : H*D₁ ≤ book.previousNeighbors.size)
    (hubLow : book.previousHubs.Fits w rc.origin) (hubSize : H ≤ book.previousHubs.size)
    (hostsFit : H < 2^w) (degreeFit : D₁+1 < 2^w)
    (ready : (U₁).Ready ops first w)
    (positive : 0 < M) (lanes : M ≤ w) :
    ∃dst,(((rc.preparedRoots book safe).seq ((U₁).classifier ops first w)).seq ((dir).program w scene)).Exec
        measured dst ((rc.preparedTicks book safe+(U₁).classifierTime ops first w)+(dir).ticks scene) ∧
      dst (dir).count.base=(Fintype.card B.next.V:Word w) ∧
      (∀v : B.next.V,dst ((dir).inverse.base+((Z).denseHostRank T rank v).val)=((id_ v).val:Word w)) ∧
      (∀v : B.next.V,dst ((dir).ranks.base+(id_ v).val)=(((Z).denseHostRank T rank v).val:Word w)) ∧
      (∀j : Fin (H*shapeCount),dst ((dir).flags.base+j.val)=if ∃v,id_ v=j then 1 else 0) ∧
      (∀j,j < rc.origin ∨ (dir).endAddress ≤ j → dst j=measured j) ∧
      ∃mid,dst=(dir).result scene mid ∧
        (∀j (p : Row H (2^coarse) M),mid ((scene).base+j.val*(H*chunks (2^coarse) M)+(row _ _ _ p).val)=
          ((data (realActor (reset:=B) (Window.shapes B) (Window.rack B input.valid.host) j) p).val:Word w)) ∧
        (∀j,j < first → mid j=rc.preparedImage book safe measured j) ∧
        (∀v,mid (((U₁).depths first).base+(idx v).val)=(prev v:Word w)) ∧
        ∀j,j < ((U₁).levels first).size → mid (((U₁).levels first).base+j)=((j-coarse+1:ℕ):Word w) := by
  have low := ActorSetup.start_before_end U₁ first
  have afterFloor : first < 2^w := low.trans_lt ready.gates.endFit
  have access := fun j=>(U₁).readable_header ready.gates j
  subst D₁; subst n₁; subst r₁; subst c₁; subst Ht₁; subst width₁; subst a
  cases eq_of_heq rotor
  have diff : wid-coarse=res:=congrArg (fun j=>j-coarse) B.keyWidth.symm
  have heightRead (j : Fin shapeCount) (v : input.V) :=
    ActorSetup.measured_level B.frame f (A).degree peer bounded v (Window.shapes B j) (Ht:=ht)
  let actorAt (r : ℕ) : ActorSetup := ⟨H,coarse,r,M,t,ActorSetup.levelBits wid (A).degree ht,
    shapeCount,DescentSharedBookScan.width res (2^(Z).n) (A).degree,wid,(A).degree*2^ht⟩
  have sameShape (j : Fin shapeCount) : ActorSetup.shapeAt (Z).graph res ht j = Window.shapes B j := rfl
  have usableGates (r : ℕ) (hr : r=res) : (actorAt r).GateFits (rc.preparedEnd book)
      pop (fun j=>headerControl res (A).degree (Window.shapes B j)) (.lookup line .row) w := by
    subst r
    simpa only [actorAt, ActorSetup.printed, ActorSetup.printedInputs, sameShape] using ready.gates
  have result:=directory_after_roots accepted level one mass shapeRoom live quotaPos degreePos input.valid.host
    pop raw line rc book safe measured page observed.panel catalog observed.hosts observed.hubs observed.count observed.depth
    ww card small (input.valid.host.trans_lt hostsFit) bounded heightRead popLow depthLow depthRows
    lineLow lineFit lineRows peerLow peerSize hubLow hubSize hostsFit degreeFit afterFloor
    (by simpa only [ActorSetup.printed, ActorSetup.printedInputs] using ready.refs)
    (usableGates (wid-coarse) diff)
    (by simpa only [ActorSetup.printed, ActorSetup.groups, diff] using access)
    positive lanes (by simpa only [ActorSetup.printed, ActorSetup.chunksPerHost, ActorSetup.groups] using ready.parts)
    (by simpa only [ActorSetup.printed, diff] using ready.room)
  let ctrl := fun j : Fin shapeCount => headerControl res (A).degree (Window.shapes B j)
  let query := fun j : Fin shapeCount => opcode res (Window.shapes B j)
  have opEq := congrArg (fun r : ℕ => (actorAt r).operator (rc.preparedEnd book) pop ctrl query
    (.lookup line .row) (w:=w)) diff
  have timeEq := congrArg (fun r : ℕ => (actorAt r).operatorTime (rc.preparedEnd book) pop ctrl query
    (.lookup line .row) w) diff
  dsimp only [actorAt, ctrl, query] at opEq timeEq
  simp only [diff, ActorSetup.directoryEnd] at result
  simp only [opEq, timeEq] at result
  simp only [ActorSetup.printed, ActorSetup.printedInputs, ActorSetup.classifier, ActorSetup.classifierTime, sameShape]
  exact result

end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
