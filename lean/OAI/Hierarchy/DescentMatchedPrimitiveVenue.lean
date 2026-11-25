import OAI.Hierarchy.DescentOriginalResetMeasures
import OAI.Hierarchy.DescentNamedVenueRootPacket
import OAI.Hierarchy.DescentScheduledReachedVenue

namespace OAI
/-! Primitive venue fields of a registered measured reset. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSixParty DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open DescentPackedColony DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
open DescentPackedZip DescentOrdinaryHostPad DescentRetainedRangeDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open scoped Classical Fin.CommRing
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z D n₁ h₁ C f₁ g₁ cut tail₁ wire hist : ℕ}
    {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n₁ h₁ C f₁ g₁ cut tail₁}
    {n h f g tail : ℕ} (board₀ : NonlinearExpanders.Graph n h) (op₀ : RotorSpec)
    (B : ClosedReset input ctl) (p drift degree payload w : ℕ) (ordinary : ℕ→Dated.Ordinary)
    (seats profile : ℕ→ℕ) (header : ℕ) (cursor : Position)
local notation "op" => op₀
local notation "s₀" => S.firstWidth G.b p
local notation "Z₀" => S.grainAt G.b p 0
local notation "board" => board₀
local notation "old" => cursor.ports.venue
local notation "io" => cursor.ports.io
local notation "cap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "oldExp" => NativePitch.resetCut S k tail p f payload age
local notation "nextM" => NativePitch.incoming S k tail p f payload ordinary (age+1)
local notation "oldL" => cursor.ports.operandLanes
local notation "roleL" => cursor.ports.roleLanes
local notation "token" => DescentPrimitivePalette.printedBits G s₀ Z₀ op
local notation "rcut" => receiverCut G S board k tail age p f g drift degree payload oldExp nextM (op).C (op).w
  oldL roleL token old
local notation "base" => cursor.ports.priorStart k cursor.floor
local notation "history" => (cursor.ports.afterPad k cursor.floor).archive
local notation "outer" => scheduledAtPorts G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor
local notation "a" => (outer).inner
local notation "v" => (a).successor
local notation "start" => (a).stageStart base
local notation "E" => (a).estimator start
local notation "HH" => S.hostSize age
local notation "Ht" => GroupStage.depthBound (old).degree n f g
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap
local notation "fits" => scheduled_cut_origin G S board k tail age p f g drift degree payload ordinary op s₀ Z₀ oldL roleL old
local notation "priorFits" => preceding_cut S k tail p f payload age
local notation "menu" => (⟨board,op,g,tail,p,f,drift,degree,payload,seats,ordinary,profile,header⟩ : Menu n h)
local notation "publisher" => priorArchivePhase G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w
variable (capacity : (old).cap=cap)
    (space : ScheduledCodeRoom G S board k tail age p f g drift degree payload ordinary op s₀ Z₀ oldL roleL
      old io base w history)
local notation "u" => DatePorts.resetInputs G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w space
local notation "finish" => FinalInputs.fromArchive G S board k tail age p f g drift degree payload rcut oldExp (2^rcut)
  nextM (op).C (op).w oldL roleL token old io base w fits fits priorFits (history).count
  (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space) history s₀ Z₀ op capacity
local notation "ports" => cursor.ports
variable (geo : Geometry G S menu k w age cursor)
variable (paid : B.Recorded p)
local notation "pre" => (a).ingress.phase base w (io).hubs (fun x=>(io).atoms x.val) (fun j=>(io).wire j.1.val j.2.val)
local notation "atMem" m:arg => (pre).image ((publisher).image m)
open DescentPrimitivePalette DescentKernelHistory DescentLocalArchiveOrder
open DescentResetActorClass DescentFundedCensus DescentColonies
local notation "sites" => B.next.vertex.trans (Fin.castLEEmb B.next.valid.host)
local notation "placement" => (v).birth.placement
local notation "lowBase" => (a).rebased start
local notation "dir" => (v).actor.directory ((v).middle.stop lowBase)
local notation "res" => B.reset.k-B.terminals.commonDepth
local notation "kind" hn:arg h:arg => Fin.cast (congrArg (fun t : ℕ=>2^t) (show (v).birth.classBits=indexBits B.reset.n res from by
  change indexBits n k=_
  exact congrArg₂ indexBits (B.dimension.trans hn).symm (ClosedReset.Window.calendar_residual B).symm).symm)
  ((ClosedReset.Window.paidActorAt B h).elim 0 (fun actor=>indexed B.reset.graph res actor.val))

include paid geo in
/-- Primitive class, occupied successor census and both directory wires on the physical registered date. -/
theorem matched_primitive_venue (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (hb : HEq ctl.board board₀) (ho : RotorSpec.ofRates ctl=op₀) (degreeAt : (old).degree=D)
    (ready : (u).Ready) (safe : (finish).Room)
    (m : Memory w) (ms : OriginalMeasures (f:=f) (g:=g) (tail:=tail) board₀ op₀ B p drift degree payload w ordinary cursor m)
    (mid : Memory w) (spent : (u).throughOperandDate.Runs (atMem m) mid) :
    0<(v).birth.sourceLanes ∧
    (finish).venueImage mid (dir).count.base=(Fintype.card B.next.V:Computability.VPVNP.BurstRAM.Word w) ∧
    (∀j:Fin (Fintype.card B.next.V),(finish).venueImage mid ((dir).inverse.base+j.val)=
      ((ClosedReset.Window.originalCompactName B HH input.valid.host j).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    Fintype.card B.next.V<2^w ∧ (placement).newHosts≤2^w ∧ Fintype.card B.next.V≤(dir).inverse.size ∧
    (∀site,(B.next.placement.records site).length<2^(v).birth.paidBits) ∧
    Source (PhysicalReset.FinalInputs.classWord u) (fun (host : Fin (placement).newHosts) (_ : Fin (placement).groups)=>kind hn host) (placement).lanes ((finish).classImage mid) ∧
    ∀x:Block k,Source (.lookup (((v).venue.sources (PhysicalReset.FinalInputs.predecessor u)
      ((v).fundedEnd lowBase)).paid x.val) .row)
      (fun h g=>Census.count B.next.placement (Equiv.refl _) sites (v).birth.paidBits h g x)
      (placement).lanes ((finish).venueImage mid):=by
  let cutAtDate:=rcut
  let oldCut:=oldExp
  let nextPitch:=nextM
  let bitsAt:=token
  have cutFits:=fits
  have oldFits:=priorFits
  let entered:=(publisher).image m
  let done : (u).FinalInputs:=finish
  have past:=(outer).stages.1
  have hr:=geo.room.header.mono past
  have wr:=geo.room.wires.mono past
  have pr:=geo.room.paid.mono past
  have issued : IssuedBanks io (old).hosts (S.groupCount age) (old).lanes:=ms.oldGroups ▸ pr.issued
  have siteCount : 0<S.initialSites:=by
    obtain ⟨j,hj⟩:=geo.room.initialSites
    exact hj.symm ▸ Nat.two_pow_pos j
  have hostPos : 0<S.hostSize (age+1):=by
    rw [AtomSchedule.hostSize,ctl.radix]
    positivity
  have groupPos : 0<S.groupCount (age+1):=by
    rw [AtomSchedule.groupCount,ctl.base,ctl.radix]
    positivity
  have chunkPos : 0<chunks (S.groupCount (age+1)) (2^cutAtDate):=by
    apply Nat.div_pos _ (Nat.two_pow_pos _)
    omega
  have cables (j:(a).ingress.signed.Slot) : ((io).wire j.1.val j.2.val).Fits w base:=by
    exact (wr (j.1.cast (congrArg (2^·) ms.oldBlocks).symm)
      (j.2.cast (congrArg (2*·) capacity).symm)).1
  subst n
  subst h
  subst f
  subst g
  subst tail
  have sameBoard : ctl.board=board₀:=eq_of_heq hb
  subst board₀
  subst op₀
  exact (PhysicalReset.fromNamed_packet_primitive_venue B drift degree payload cutAtDate oldCut
    (2^cutAtDate) nextPitch oldL roleL bitsAt old io base w cutFits cutFits oldFits (history).count
    (history).nodeBase (history).arguments (history).seed (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space)
    done paid degreeAt ready entered ms.gr ms.fee ms.capAt ms.historyAt ms.branch ms.seen ms.popFit ms.popRead
    ms.wireRoom ms.oldPos ms.oldWidth ms.entryFits ms.low ms.score paid.positive ms.degreePos ms.headerBits
    ms.hostBits ms.ranksFit ms.namesFit ms.degFit ms.laneRoom ms.oldHosts.symm ms.oldGroups ms.oldBlocks
    (capacity.trans ms.capAt.symm) ms.pitchOld rfl rfl rfl safe issued hr.hubs (fun x=>pr.stock x.val) cables
    ms.hubSpan rfl rfl ms.narrow ms.word ms.ceiling hostPos chunkPos spent).2

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
