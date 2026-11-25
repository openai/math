import OAI.Hierarchy.DescentNamedSnapshotRoster
import OAI.Hierarchy.DescentTerminalPacketHomeInstall

namespace OAI
/-! # Expanding the genuine frozen birth snapshots into terminal public-home rows -/
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
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace Branch
open DescentTerminalExteriorPackets DescentExteriorReplay ThreeFlat.RAM PhysicalProcedure
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "retained" => S.groupWidth k tail S.length+k
local notation "shape" => j+(j+rest)
local notation "E" => Fintype.card (Port P X.width)
local notation "Public" => Σ _:Fin (2^shape),Fin E
variable (width : S.groupWidth k tail 0+k=j+(j+rest))


open DescentTerminalPacketHomeRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM

attribute [local irreducible] Procedure.Exec ProtocolRAM.CheapCode

local notation "tracking" => publicSpine X G S b hp base width
local notation "origPin" => NativeBranch.rawPin S (X:=X) (radix:=radix) base width
local notation "originLayout" => fun _ : Fin E=>LinearEquiv.refl (ZMod 2) (Bits shape)
local notation "oldOwner" => fun u : Public=>host b.origin.source (origPin u)
local notation "newOwner" => fun u : Public=>host b.target (origPin u)
local notation "frozen_" => b.path.frozen


local notation "size₀" => E*2^frozen_
local notation "rows₀" => E*2^(j+rest)
local notation "rep" => fun a:Fin size₀=>origPin (representative tracking originLayout (finProdFinEquiv.symm a))

open DescentTerminalFrozenRoster Computability.BorderVNP.FragmentBucket
local notation "H" => S.hostSize S.length
local notation "capBits" => 8+S.capGain*S.length
local notation "home₀" => cohortHome X G S b hp base
local notation "fr" => fun u : Fin size₀=>(finProdFinEquiv.symm u : Fin E×Fin (2^frozen_)).2
local notation "codes" => DescentTerminalFrozenRoster.book home₀ fr
local notation "finalWorld" => ((Epochs.finish G hu he r).state c).graph

variable {bw : ℕ} (A : Snapshots k) (start scratch : ℕ) (first : Memory bw)
local notation "hop_" => A.hop start frozen_ scratch size₀
local notation "lit" => A.image start frozen_ first S.length
local notation "init" => Snapshots.seedImage scratch (seedAncestry X G S b) lit
local notation "seedOp" => Snapshots.seedProgram bw scratch (seedAncestry X G S b)
local notation "seedTicks" => 4+10*size₀
local notation "earlyCode" => (A.program bw start frozen_ S.length).seq seedOp
variable (bounds : ∀t<S.length,S.hostSize t≤A.hosts t)
  (before : A.start start b.path.frozen S.length ≤ scratch)
  (enough : scratch + (S.length+1) * Snapshots.stride (Fintype.card (Port P X.width) * 2^b.path.frozen) < 2^bw)
  (ranks : b.path.snapshotRanks A start first) (labels : b.path.snapshotLabels A)

variable (packetStart censusAt : ℕ)
local notation "lastPage" => Snapshots.page scratch size₀ S.length
local notation "L" => Expansion.layout packetStart rows₀ lastPage
local notation "freshEnd" => Expansion.stop packetStart rows₀
local notation "sortEnd" => DescentTerminalCohortArena.stop censusAt frozen_ capBits size₀ H
local notation "homesCode" => Expansion.fixedProgram bw packetStart E j rest retained lastPage
local notation "census" => DescentTerminalCohortArena.order censusAt frozen_ capBits size₀ H

private theorem packetArenaOffsets (c f k n p : ℕ) :
    c ≤ DescentTerminalCohortArena.indexBase c f k n p ∧
    c ≤ DescentTerminalCohortArena.tallyBase c f k n p + 4*n ∧
    c ≤ (DescentTerminalCohortArena.order c f k n p).counts ∧
    c ≤ DescentTerminalCohortArena.stop c f k n p := by
  unfold DescentTerminalCohortArena.stop DescentTerminalCohortArena.tallyBase
    DescentTerminalCohortArena.indexBase DescentTerminalPacketSlotRAM.out DescentTerminalCohortArena.order
  simp only [Nat.add_assoc]
  exact ⟨Nat.le_add_right .., Nat.le_add_right .., Nat.le_add_right .., Nat.le_add_right ..⟩

include bounds before enough ranks labels in
/-- The terminal host values come from the same executed hop snapshots as the
frozen census. Only the public calendar ordinal is written as a literal. -/
theorem snapshot_packet_hosts (retained_ : j≤retained)
    (snapshotEnd : (lastPage).base+(lastPage).size≤packetStart)
    (separate : freshEnd≤censusAt)
    (ready : sortEnd<2^bw) (alive : 0<H) (payload : (frozen_+1)*2^capBits≤bw) :
    let bins_ := DescentTerminalCohortArena.shelf censusAt frozen_ capBits size₀ H ready
    let rank := DescentTerminalCohortArena.indexBase censusAt frozen_ capBits size₀ H
    let act := (steps bw size₀ (schedule hop_ S.length)).seq
      (DescentTerminalCohortArena.machine censusAt frozen_ capBits size₀ H ready lastPage)
    let fee := clocks size₀ (schedule hop_ S.length)+DescentTerminalCohortArena.ticks censusAt frozen_ capBits size₀ H ready lastPage
    ∃out,(((earlyCode).seq act).seq homesCode).Exec first out
       ((A.clocks frozen_ S.length+seedTicks+fee)+(8+38*rows₀)) ∧
      CheapCode (((earlyCode).seq act).seq homesCode) ∧
      (∀i:Fin rows₀,(L).dest.read out (i.val:Computability.VPVNP.BurstRAM.Word bw)=((publicHost X G S b hp base width i).val:Computability.VPVNP.BurstRAM.Word bw)) ∧
      (∀v:Fin H,(out (bins_.bins+v.val)).val=(codes v).val ∧ (out ((census).counts+v.val)).val=count home₀ v) ∧
      (∀v:(finalWorld).Site,∀pin:Attached finalWorld v,
        let at_:=cohort X G S b hp base pin.val
        out (rank+(dest home₀ at_).val)=(densePin X G S b hp base v pin:Computability.VPVNP.BurstRAM.Word bw) ∧
        DescentExterior.terminalPin initialBits retained frozen_ (matrixCode (pinSpine X G S b hp base).matrix).val
          (out (bins_.bins+(b.target.home v).val)).val pin.val.1.val=densePin X G S b hp base v pin) ∧
      ∀a<packetStart,out a=stage hop_ size₀ init S.length a := by
  intro bins_ rank act fee
  have reserve : size₀+1≤Snapshots.stride size₀:=Nat.le_pow_clog (by decide) _
  have roomOld : size₀≤(lastPage).size := by change size₀≤Snapshots.stride size₀;omega
  obtain ⟨rankHi,binHi,countsHi,wide⟩ := packetArenaOffsets censusAt frozen_ capBits size₀ H
  have env := Expansion.room packetStart lastPage snapshotEnd roomOld (separate.trans_lt (wide.trans_lt ready))
  have initSpace : scratch+Snapshots.stride size₀<2^bw :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) _) enough
  have hopSize (t : ℕ) (_live : t<S.length) : size₀≤(hop_ t).dest.size ∧ (hop_ t).dest.size<2^bw := by
    change size₀≤Snapshots.stride size₀ ∧ Snapshots.stride size₀<2^bw
    omega
  have snap := replayed_frozen X G S b hp base width hop_ L init env
    (Snapshots.seed_read scratch (seedAncestry X G S b) lit initSpace)
    (snapshot_fields X G S b hp base width A start scratch first bounds before enough ranks labels)
    (fun _ _=>rfl) hopSize rfl
  have p₀ : packetStart≤freshEnd := by
    unfold Expansion.stop;omega
  have low : (lastPage).Fits bw censusAt :=
    ⟨Nat.two_pow_pos _,by omega,snapshotEnd.trans (p₀.trans separate)⟩
  obtain ⟨prior,ran,cheap,counts,ports,frame⟩ := snapshot_roster X G S b hp base width A start scratch first
    bounds before enough ranks labels L env rfl censusAt ready low alive payload
  let ids := frozenIndex X G S b hp base width retained_
  have static := Expansion.fixed_code bw packetStart lastPage ids (frozenIndex_val X G S b hp base width retained_)
  have funded := Expansion.install packetStart lastPage ids prior snapshotEnd roomOld (separate.trans_lt (wide.trans_lt ready))
  let out := Expansion.image packetStart lastPage ids prior
  have older (a:Fin size₀) : prior ((lastPage).base+a.val)=((frozenHome X G S b hp base width a).val:Computability.VPVNP.BurstRAM.Word bw) :=
    (frame _ ((Nat.add_lt_add_left (a.isLt.trans_le roomOld) _).trans_le low.2.2)).trans (snap a)
  have raw (i:Fin rows₀) := Expansion.reads packetStart lastPage ids prior snapshotEnd roomOld
    (separate.trans_lt (wide.trans_lt ready)) (frozenHome X G S b hp base width) older i
  have keep (a:ℕ) (hi:censusAt≤a) : out a=prior a := funded.2.2 a (.inr (separate.trans hi))
  have rankOffset : censusAt ≤ rank := rankHi
  have binOffset : censusAt ≤ bins_.bins := binHi
  refine ⟨out,?_,?_,fun i=>(raw i).trans (congrArg (fun a:Fin H=>(a.val:Computability.VPVNP.BurstRAM.Word bw))
    (publicHost_frozen X G S b hp base width retained_ i).symm),?_,?_,
    fun a ha=>(funded.2.2 _ (.inl ha)).trans (frame _ (ha.trans_le (p₀.trans separate)))⟩
  · rw [static]
    exact Procedure.Exec.then ran funded.1
  · rw [static]
    exact cheap_seq cheap funded.2.1
  · intro v
    simpa only [keep _ (binOffset.trans (Nat.le_add_right ..)),keep _ (countsHi.trans (Nat.le_add_right ..))] using counts v
  · intro v pin
    dsimp only
    rw [keep _ (rankOffset.trans (Nat.le_add_right ..)),keep _ (binOffset.trans (Nat.le_add_right ..))]
    exact ports v pin

/-- Transport the low frame of the actual packet-host run all the way to the
incoming hardware memory, across its population snapshots and original owner seed. -/
theorem snapshot_packet_entry (out:Memory bw)
    (actual:∀a<packetStart,out a=stage hop_ size₀ init S.length a) (cut:ℕ)
    (beforePacket:cut≤packetStart) (beforeSeed:cut≤ scratch) (beforeTables:cut≤ start) :
    ∀a<cut,out a=first a := by
  intro a ha
  exact (actual a (ha.trans_le beforePacket)).trans <|
    (A.stage_frame start frozen_ scratch size₀ init S.length a (ha.trans_le beforeSeed)).trans <|
    (Snapshots.seed_low scratch (seedAncestry X G S b) lit a (ha.trans_le beforeSeed)).trans
    (A.image_frame start frozen_ first S.length a (.inl (ha.trans_le beforeTables)))

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.publicSpine Branch.publicLayout
  Branch.originalPin Branch.cohortHome Branch.cohort Branch.atCohort Branch.densePin
