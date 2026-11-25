import OAI.Hierarchy.DescentNamedReplayCalendar
import OAI.Hierarchy.DescentNamedSnapshotPublicHomes
import OAI.Hierarchy.DescentTerminalFixedSlices
import OAI.Hierarchy.DescentPhysicalSnapshotRanks
import OAI.Hierarchy.DescentEarlyRotationReel
import OAI.Hierarchy.DescentExteriorSnapshotCalendar

namespace OAI
/-! The selector's dated ancestry, frozen labels and expanded public packets in the
unique halt memory of the original terminal replay program. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.publicSpine Branch.originalPin
set_option quotPrecheck false
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0<p)

open DescentGL DescentColonies DescentExterior PinCohorts


namespace Branch
open DescentTerminalExteriorPackets DescentExteriorReplay ThreeFlat.RAM PhysicalProcedure
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "retained" => S.groupWidth k tail S.length+k
local notation "shape" => j+(j+rest)
local notation "E" => Fintype.card (Port P X.width)
variable (width : S.groupWidth k tail 0+k=j+(j+rest))


open DescentTerminalPacketHomeRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
attribute [local irreducible] Procedure.Exec ProtocolRAM.CheapCode

local notation "frozen_" => b.path.frozen


local notation "size₀" => E*2^frozen_
local notation "rows₀" => E*2^(j+rest)

open DescentTerminalFrozenRoster Computability.BorderVNP.FragmentBucket
local notation "H" => S.hostSize S.length
local notation "capBits" => 8+S.capGain*S.length
local notation "home₀" => cohortHome X G S b hp base
local notation "fr" => fun u : Fin size₀=>(finProdFinEquiv.symm u : Fin E×Fin (2^frozen_)).2
local notation "codes" => DescentTerminalFrozenRoster.book home₀ fr
local notation "finalWorld" => ((Epochs.finish G hu he r).state c).graph


private def calendarAt {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P)
    (S : AtomSchedule) (k tail j rest : ℕ) (A : Snapshots k) (frozenBits : ℕ) :
    DescentTerminalFixedReplay.Calendar k where
  snapshots := A
  age := S.length
  frozenBits := frozenBits
  cohortBits := 8+S.capGain*S.length
  ports := Fintype.card (Port P X.width)
  j := j
  rest := rest
  kept := S.groupWidth k tail S.length+k
  hosts := S.hostSize S.length
  seed a := (Fintype.equivFin (Site X.network.copyGraph) (.inr (finProdFinEquiv.symm a).1)).val

variable {bw : ℕ}

/-- The addresses in this receipt belong to the fixed calendar. Its right-hand sides
are the selected mathematical graph, its real attached pins, and its original dated snapshots. -/
structure OriginalReplayRead (T : DescentTerminalFixedReplay.Calendar k) (start censusAt : ℕ)
    (first out : Memory bw) : Prop where
  homes (i : Fin rows₀) :
    (T.homes start).read out (i.val:Computability.VPVNP.BurstRAM.Word bw)=((publicHost X G S b hp base width i).val:Computability.VPVNP.BurstRAM.Word bw)
  census (i : Fin H) :
    (out ((DescentTerminalCohortArena.tallyBase censusAt T.frozenBits T.cohortBits T.cohorts T.hosts+
      4*T.cohorts)+i.val)).val=(codes i).val ∧
    (out ((DescentTerminalCohortArena.order censusAt T.frozenBits T.cohortBits T.cohorts T.hosts).counts+
      i.val)).val=count home₀ i
  pins (v : (finalWorld).Site) (pin : Attached finalWorld v) :
    out (DescentTerminalCohortArena.indexBase censusAt T.frozenBits T.cohortBits T.cohorts T.hosts+
      (dest home₀ (cohort X G S b hp base pin.val)).val)=(densePin X G S b hp base v pin:Computability.VPVNP.BurstRAM.Word bw) ∧
    DescentExterior.terminalPin initialBits retained frozen_
      (matrixCode (pinSpine X G S b hp base).matrix).val
      (out ((DescentTerminalCohortArena.tallyBase censusAt T.frozenBits T.cohortBits T.cohorts T.hosts+
        4*T.cohorts)+(b.target.home v).val)).val pin.val.1.val=densePin X G S b hp base v pin
  stage (a : ℕ) (ha : a<T.packetStart start) :
    out a=DescentExteriorReplay.stage (T.snapshots.hop start frozen_ (T.scratch start) size₀) size₀
      (Snapshots.seedImage (T.scratch start) (seedAncestry X G S b)
        (T.snapshots.image start frozen_ first S.length)) S.length a
  frame (a : ℕ) (outside : a<start ∨ T.stop censusAt≤a) : out a=first a

variable (A : Snapshots k) (start censusAt : ℕ) (first : Memory bw)
local notation "cal" => replayCalendar X S k tail j rest A
local notation "actual" => calendarAt X S k tail j rest A frozen_

private theorem original_read_at (T : DescentTerminalFixedReplay.Calendar k) (eqn : actual=T)
    (room : T.stop censusAt<2^bw) (ordered : T.packetEnd start≤censusAt)
    (bounds : ∀t<S.length,S.hostSize t≤A.hosts t)
    (ranks : b.path.snapshotRanks A start first) (labels : b.path.snapshotLabels A)
    (retained_ : j≤retained) (alive : 0<H) (payload : (T.frozenBits+1)*2^T.cohortBits≤bw) :
    OriginalReplayRead X G S b hp base width T start censusAt first (T.memory start censusAt room first) := by
  subst T
  obtain ⟨rootFits,_,middle,last,_⟩ := (actual).addresses start censusAt
  have enough := middle.trans_lt (ordered.trans_lt (last.trans_lt room))
  have rankFits : ∀t<(actual).age,∀bank,(actual).snapshots.compact t=some bank →
      bank.Fits bw ((actual).scratch start) := by
    intro t ht bank found
    have orig:=b.path.snapshot_rank_rooms A start first ranks t ht bank found
    exact ⟨orig.1,orig.2.1,orig.2.2.trans rootFits⟩
  obtain ⟨out,run,_,homes,counts,ports,staged⟩:=
    snapshot_packet_hosts X G S b hp base width A start ((actual).scratch start) first bounds
      le_rfl enough ranks labels ((actual).packetStart start) censusAt retained_
      (A.last_fits start frozen_ size₀ S.length enough).2.2 ordered room alive payload
  have native : ((actual).program start censusAt room).Exec first out ((actual).cost start censusAt room) := run
  have canonical := (actual).exec_memory start censusAt room ordered alive rankFits first
  have equal := ProtocolRAM.exec_unique _ _ _ _ native canonical.1
  subst out
  exact ⟨homes,counts,ports,staged,canonical.2.2⟩

/-- The executable program, its advice, and the halt image use the same calendar on every
branch. The actual frozen dimension identifies each seed digit and each dated directory. -/
theorem original_replay_read (room : (cal).stop censusAt<2^bw) (ordered : (cal).packetEnd start≤censusAt)
    (bounds : ∀t<S.length,S.hostSize t≤A.hosts t)
    (ranks : b.path.snapshotRanks A start first) (labels : b.path.snapshotLabels A)
    (retained_ : j≤retained) (alive : 0<H) (payload : (k*S.length+1)*2^capBits≤bw) :
    OriginalReplayRead X G S b hp base width (cal) start censusAt first
      ((cal).memory start censusAt room first) :=
  original_read_at X G S b hp base width A start censusAt first (cal)
    (congrArg (calendarAt X S k tail j rest A) b.path.frozen_age)
    room ordered bounds ranks labels retained_ alive payload

/-- The role normalization between the last date and the public replay preserves the
rank words even when the last reset has empty sites or no attached pins. -/
theorem original_slice_ranks (P₀ : DescentTerminalFixedSlices.Phase F) (lo replayAt : ℕ)
    (mem : Memory bw) (ranks : b.path.snapshotRanks A lo mem)
    (done_ : P₀.output.metadataEnd P₀.dateBase≤lo)
    (one : DescentSIMDLookup.chunks P₀.output.receiver.groups P₀.output.receiver.lanes=1)
    (space : P₀.stop lo<2^bw) (grows : lo≤replayAt) :
    b.path.snapshotRanks A replayAt (P₀.memory lo mem) :=
  b.path.snapshotRanks_frame A ranks grows (fun a before=>(P₀.run lo mem done_ one space).2.2.1 a (.inl before))

/-- All reset/ordinary labels on the replay tape come from the original branch calendar.
The bank numbers are the actual directories allocated by the dated program. -/
theorem original_snapshot_labels {cut : ℕ}
    (ctl : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
    (directories : ℕ→Bank) (rotor : b.path.OnlyRotor (RotorSpec.ofRates ctl)) :
    b.path.snapshotLabels (Chronology.SnapshotCalendar ctl (Chronology.kindCalendar S.rounds S.height)
      (capCalendar G.b S.rounds g S.height) directories) :=
  b.path.issued_snapshot_labels ctl directories b.kinds b.calendar rotor

section Dated
variable (P₀ : DescentTerminalFixedSlices.Phase F) (floor t compact : ℕ)
  (tag : ℕ→Bool) (rotation : ℕ→ℕ) (initialMem : Memory bw)
local notation "early" => DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail floor j rest t E
local notation "slices" => P₀.stop early
local notation "earlyMem" => DescentExteriorMatrixUpdate.Calendar.earlyImage S k tail floor tag rotation
  j rest t E compact initialMem
local notation "preReplay" => P₀.memory early earlyMem

/-- Carry the original date's rank directories through both native phases immediately
preceding the fixed replay. The resulting readbacks have the same input memory and addresses
as the replay in the terminal CPU. -/
theorem original_replay_from_dated (room : (cal).stop censusAt<2^bw)
    (ordered : (cal).packetEnd slices≤censusAt)
    (bounds : ∀t<S.length,S.hostSize t≤A.hosts t)
    (ranks : b.path.snapshotRanks A floor initialMem) (labels : b.path.snapshotLabels A)
    (positive : 0<bw) (prev : ∀d<S.length,rotation d<floor)
    (seed : compact+32*DescentExteriorShelf.span j rest t E≤floor)
    (done_ : P₀.output.metadataEnd P₀.dateBase≤early)
    (one : DescentSIMDLookup.chunks P₀.output.receiver.groups P₀.output.receiver.lanes=1)
    (retained_ : j≤retained) (alive : 0<H) (payload : (k*S.length+1)*2^capBits≤bw) :
    OriginalReplayRead X G S b hp base width (cal) slices censusAt preReplay
      ((cal).memory slices censusAt room preReplay) := by
  have a:floor≤early:=by
    unfold DescentExteriorMatrixUpdate.Calendar.earlyEnd DescentExteriorMatrixUpdate.Calendar.earlyAt
      DescentExteriorMatrixUpdate.Calendar.stop DescentExteriorMatrixUpdate.Calendar.tableAt
    omega
  have l:early≤ slices:=by
    unfold DescentTerminalFixedSlices.Phase.stop DescentTerminalCompiledPrefix.AddressPlan.sliceStop
      DescentTerminalSliceShelf.fence DescentTerminalSliceShelf.stage DescentTerminalPointerDigits.Gather.rom
      DescentOperandStateBanks.guard
    simp only [Nat.add_assoc]
    exact Nat.le_add_right ..
  obtain ⟨s₀,s₁,s₂,h₀,_⟩:=(cal).addresses slices censusAt
  have free : slices<2^bw:=(s₀.trans (s₁.trans (s₂.trans (ordered.trans h₀)))).trans_lt room
  have reel:=DescentExteriorMatrixUpdate.Calendar.early_run S k tail floor tag rotation j rest t E compact
    initialMem positive prev seed (l.trans_lt free)
  have earlierRanks:=b.path.snapshotRanks_frame A ranks a (fun i hi=>reel.2.2 i (.inl hi))
  have finalRanks:=b.path.snapshotRanks_frame A earlierRanks l
    (fun i hi=>(P₀.run early earlyMem done_ one free).2.2.1 i (.inl hi))
  exact original_replay_read X G S b hp base width A slices censusAt preReplay room ordered
    bounds finalRanks labels retained_ alive payload

end Dated
end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.publicSpine Branch.publicLayout
  Branch.originalPin Branch.cohortHome Branch.cohort Branch.atCohort Branch.densePin
