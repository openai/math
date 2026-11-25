import OAI.Hierarchy.DescentDatedSampledOperandValues
import OAI.Hierarchy.DescentDatedOperandNativePreparation
import OAI.Hierarchy.DescentDatedOperandPipelineObserved
import OAI.Hierarchy.DescentDatedOperandHostPrefix

namespace OAI
/-! # Typed original dated words become the native eight operand expressions -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip
open DescentRawCablePanel DescentHaloWalkRAM DescentSharedCableNames ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "P" => breadth (fmt).degree
local notation "O" => DepotRAM.Material.roles fmt
local notation "l" => v.resolver
local notation "g" => v.ticketReadGeometry
local notation "J" => (l).jobs
local notation "d" => v.operandShortBits
local notation "b" => (e).fieldBits
local notation "pwidth" => Packed.bits P

/-- Both routings read the very same input adjacency. One array retains the first physical walk,
and the checked W roster numbers distinct old hosts in increasing order. -/
structure WalkBanks (floor : ℕ) (A : v.ArgumentEntry)
    (reach : Fin (e).oldHosts→Fin P→Option (Fin (e).oldHosts)) {w : ℕ} (base : ℕ) (m : Memory w) : Prop where
  visited : (v.operandRanks floor).endpoints.Fits w base
  sorted : (A.ports v floor).roster.Fits w base
  visitedRows : (e).oldHosts*P≤(v.operandRanks floor).endpoints.size
  sortedRows : (e).oldHosts*P≤(A.ports v floor).roster.size
  sentinel : (e).oldHosts<2^w
  raw : ∀h p,m ((v.operandRanks floor).endpoints.base+(Ranks.id h p).val)=(number (Gather.select reach h p):Computability.VPVNP.BurstRAM.Word w)
  ordered : ∀h t,m ((A.ports v floor).roster.base+(Ranks.id h t).val)=(number (DescentSortedRoster.indexed reach h t):Computability.VPVNP.BurstRAM.Word w)

theorem WalkBanks.keep {floor lo hi w : ℕ} {A : v.ArgumentEntry} {reach : Fin (e).oldHosts→Fin P→Option (Fin (e).oldHosts)}
    {m : Memory w} {prog : NativePhase w} (rows : v.WalkBanks floor A reach lo m) (step : Step lo hi prog m) :
    v.WalkBanks floor A reach hi (prog.image m) :=by
  have kept (B : Bank) (before : B.Fits w lo) (fit : (e).oldHosts*P≤B.size) (h : Fin (e).oldHosts) (i : Fin P) :
      prog.image m (B.base+(Ranks.id h i).val)=m (B.base+(Ranks.id h i).val):=
    step.frame _ (.inl ((Nat.add_lt_add_left ((Ranks.id h i).isLt.trans_le fit) _).trans_le before.2.2))
  exact ⟨⟨rows.visited.1,rows.visited.2.1,rows.visited.2.2.trans step.order⟩,
    ⟨rows.sorted.1,rows.sorted.2.1,rows.sorted.2.2.trans step.order⟩,rows.visitedRows,rows.sortedRows,rows.sentinel,
    fun h i=>(kept _ rows.visited rows.visitedRows h i).trans (rows.raw h i),
    fun h i=>(kept _ rows.sorted rows.sortedRows h i).trans (rows.ordered h i)⟩

variable (floor : ℕ) (c : v.SignedChart) (A : v.ArgumentEntry) («matching» : A.Match v floor)
    (shape : v.VectorShape) (blocks : v.resolver.blocks = v.material.blocks)
variable (data : v.OriginalData)
/-- Each premise names the literal earlier RAM address which issued that
word, at its original width. The final lane-dependent key is computed by
the five succeeding lookup programs. -/
structure OriginalReads {w : ℕ} (m : Memory w) : Prop where
  origin : ∀j f,Held g (v.headTransferEnd floor) m (v.originAt floor d shape j f) (data.origin j f)
  prior : ∀j f,Held g (v.headTransferEnd floor) m (v.oldHeaderAt floor j f) (data.prior j f)
  mouth : ∀j f,Held g (v.headTransferEnd floor) m (v.mouthAt floor A «matching» shape j f) (data.mouth j f)
  old : ∀j f i,Held g (v.headTransferEnd floor) m
    (v.transferredOld floor (v.receiverBlock blocks j) f i) (data.old j f i)
  path : ∀i,Held g (v.headTransferEnd floor) m (v.transferredPath floor i) (data.path i)
  anchor : ∀j f i,Held g (v.headTransferEnd floor) m
    (v.transferredAnchor floor (v.receiverBlock blocks j) f i) (data.anchor j f i)
  raw : ∀j f i,Held g (v.headTransferEnd floor) m
    (v.transferredRaw floor (v.receiverBlock blocks j) f i) (data.raw j f i)
  rank : ∀i,Held g (v.headTransferEnd floor) m (v.transferredRank floor i) (data.rank i)

variable {w : ℕ} (m : Memory w)
local notation "castStage" => DescentDatedOperandCasts.phase v.operandWidth d (l).lanes (v.headTransferEnd floor) w
local notation "pre" => v.headTransferEnd floor
local notation "start" => v.operandRootBase floor
theorem coded_original (old : v.OriginalReads floor A «matching» shape blocks data m) (space : start<2^w) :
    Step pre start castStage m ∧ Recorded g (v.nativeTicketSources floor c A «matching» shape blocks) (v.originalValues data) start ((castStage).image m) :=by
  have issued:=DescentDatedOperandCasts.any v.operandWidth d (l).lanes space m
  have run:Step pre start castStage m:=⟨Nat.le_add_right ..,issued.1,issued.2⟩
  have port (i : Fin 4) (src : Expr) (x : Values g (v.operandWidth i)) (prior : Held g pre m src x) :
      Held g start ((castStage).image m) (v.sourceCast floor i src) (fun h r=>DescentRootOrderCast.widen («b»:=d) (x h r)) :=by
    have used:=DescentDatedOperandCasts.issued v.operandWidth d (l).lanes v.operandWidth_le space i src m x prior.fits prior.read
    exact ⟨used.1,used.2⟩
  exact ⟨run,⟨fun j f=>Step.keep g run (old.origin j f),
    fun j f=>port 1 _ _ (old.prior j f),fun j f=>port 2 _ _ (old.mouth j f),
    fun j f i=>port 0 _ _ (old.old j f i),fun i=>port 3 _ _ (old.path i),
    fun j f i=>port 0 _ _ (old.anchor j f i),fun j f i=>port 0 _ _ (old.raw j f i),
    fun i=>port 3 _ _ (old.rank i)⟩⟩

theorem native_source_returns (reach : Fin (e).oldHosts→Fin P→Option (Fin (e).oldHosts))
    (rosters : v.WalkBanks floor A reach pre m) (old : v.OriginalReads floor A «matching» shape blocks data m)
    (space : v.preparedUntil floor<2^w) :
    let run:=(castStage).seq (v.sortedTicketPhase floor w c A «matching» shape blocks)
    let corrected:=SortedInput.values g (v.originalValues data) (v.walkValues reach)
    Step pre (v.preparedUntil floor) run m ∧
      ∀j f,Held g (v.preparedUntil floor) (run.image m) (v.nativeTicketExpr floor c A «matching» shape blocks j f)
        (fun h k=>finalLaw g f (fun i=>finalInputs g corrected j i h k)) :=by
  intro run corrected
  obtain ⟨one,two,three⟩:=SortedInput.ceilings g start
  have high:=one.trans (two.trans three)
  have mounted:=v.coded_original floor c A «matching» shape blocks data m old (high.trans_lt space)
  have ready:=rosters.keep v mounted.1
  have pb : P≤2^(g).digitBits:=by
    have small : P≤2^(Packed.bits P):= (Nat.le_succ P).trans (Nat.le_pow_clog (by decide) (P+1))
    exact small.trans (Nat.pow_le_pow_right (by decide) (v.operandWidth_le 3))
  have issued:=SortedInput.program_observed g (v.nativeTicketSources floor c A «matching» shape blocks) (v.originalValues data) v.materialPitch _ _
    reach ((castStage).image m) mounted.2 ready.visited ready.sorted ready.visitedRows ready.sortedRows
    ready.sentinel pb ready.raw ready.ordered space
  exact ⟨mounted.1.thenStep issued.1,issued.2⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
