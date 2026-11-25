import OAI.Hierarchy.DescentExteriorSnapshotFields
import OAI.Hierarchy.DescentExteriorSnapshotSeed
import OAI.Hierarchy.DescentNamedFrozenRoster

namespace OAI
/-! A real immutable seed page and dated native snapshots feed the terminal frozen roster. -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing Catalyst DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open PinCohorts DescentExteriorReplay DescentHostDirectory DescentHostDegree DescentCommonHost DescentDenseHostOrder
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k hwire hist : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {I W : MarkedWorld F d P bits}
  {z₀ D₀ i z D : ℕ} {initial : Reached I G q ε S k 0 z₀ D₀ hwire hist}
  {current : Reached W G q ε S k i z D hwire hist}
  (path : Path initial current) (A : Snapshots k)

omit [Fintype P] in
theorem Path.snapshot_rank_rooms {bw : ℕ} (low : ℕ) (m : Memory bw)
    (ranks : path.snapshotRanks A low m) :
    ∀ t< i,∀B,A.compact t=some B → B.Fits bw low := by
  induction path with
  | here => intro t impossible;omega
  | @ordinary _ age _ _ _ _ src prev _ _ _ _ _ _ ticket ih =>
    obtain ⟨past,last⟩:=ranks
    intro t ht B eqn
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with earlier|rfl
    · exact ih past t earlier B eqn
    · rw [last] at eqn;contradiction
  | @reset _ age _ Di dim gh C₀ f₀ g₀ c₀ t₀ src prev ctl b ih =>
    obtain ⟨past,R,last,fit,read⟩:=ranks
    intro t ht B eqn
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with earlier|rfl
    · exact ih past t earlier B eqn
    · rw [last] at eqn
      exact (Option.some.inj eqn) ▸ fit

end
end Hierarchy.DescentSixParty.Chronology

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
attribute [local irreducible] Origin.source
set_option quotPrecheck false
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S radix R r c) (hp : 0<p)

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
variable (width : S.groupWidth k tail 0 + k = j + (j + rest))


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

/- All claims about the initial ancestry tape refer to immutable original
incidence indices of X. No branch field or selected matrix enters these words. -/
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

include bounds before enough ranks labels in
/-- Every shape and frozen-digit field is read at its own chronological native snapshot. -/
theorem snapshot_fields : b.path.exteriorFields base radix hop_ init rep := by
  have large : size₀+1≤Snapshots.stride size₀:=Nat.le_pow_clog (by decide) _
  have reserved : Snapshots.stride size₀≤(S.length+1)*Snapshots.stride size₀:=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have low : scratch<2^bw:=by omega
  have hold (a : ℕ) (ha : a< scratch) : init a=lit a := Snapshots.seed_low _ _ _ _ ha
  have formed:=b.path.snapshot_fields A start frozen_ scratch size₀ S.length first init le_rfl
    bounds before low hold ranks labels
  apply printed_fields X G S b hp base width hop_ init formed
  intro t active a
  have litVal:=(A.literal_fields start frozen_ scratch size₀ S.length t first init active before low hold).2.2
    a (by have :=a.isLt;omega)
  exact litVal

include width bounds before enough ranks labels in
theorem snapshot_roster (L : DescentTerminalPacketHomeRAM.Layout)
    (ok : DescentTerminalPacketHomeRAM.Room L bw rows₀ size₀)
    (last : Snapshots.page scratch size₀ S.length=L.frozen)
    (fresh : ℕ) (room : DescentTerminalCohortArena.stop fresh frozen_ capBits size₀ H<2^bw)
    (original : L.frozen.Fits bw fresh) (alive : 0<H) (payload : (frozen_+1)*2^capBits ≤ bw) :
    let bins_:=DescentTerminalCohortArena.shelf fresh frozen_ capBits size₀ H room
    let ord:=DescentTerminalCohortArena.order fresh frozen_ capBits size₀ H
    let rank:=DescentTerminalCohortArena.indexBase fresh frozen_ capBits size₀ H
    let act:=(steps bw size₀ (schedule hop_ S.length)).seq (DescentTerminalCohortArena.machine fresh frozen_ capBits size₀ H room L.frozen)
    let fee:=clocks size₀ (schedule hop_ S.length)+DescentTerminalCohortArena.ticks fresh frozen_ capBits size₀ H room L.frozen
    ∃o,((earlyCode).seq act).Exec first o ((A.clocks frozen_ S.length+seedTicks)+fee) ∧ CheapCode ((earlyCode).seq act) ∧
      (∀v:Fin H,(o (bins_.bins+v.val)).val=(codes v).val ∧ (o (ord.counts+v.val)).val=count home₀ v) ∧
      (∀v:(finalWorld).Site,∀pin:Attached finalWorld v,
        let at_:=cohort X G S b hp base pin.val
        o (rank+(dest home₀ at_).val)=(densePin X G S b hp base v pin:Computability.VPVNP.BurstRAM.Word bw) ∧
        DescentExterior.terminalPin initialBits retained frozen_ (matrixCode (pinSpine X G S b hp base).matrix).val
          (o (bins_.bins+(b.target.home v).val)).val pin.val.1.val=densePin X G S b hp base v pin) ∧
      ∀a<fresh,o a=stage hop_ size₀ init S.length a := by
  intro bins_ ord rank act fee
  have reserve : size₀+1≤Snapshots.stride size₀:=Nat.le_pow_clog (by decide) _
  have cells : Snapshots.stride size₀≤(S.length+1)*Snapshots.stride size₀:=Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have fits : scratch+Snapshots.stride size₀<2^bw:=by omega
  have boot:=A.run start frozen_ first S.length (lt_of_le_of_lt before (by omega))
  have seed:=Snapshots.seed_run scratch (seedAncestry X G S b) lit fits
  have cap (t : ℕ) (_live : t<S.length) : size₀≤(hop_ t).dest.size ∧ (hop_ t).dest.size<2^bw :=
    ⟨by change size₀≤Snapshots.stride size₀;omega,by change Snapshots.stride size₀<2^bw;omega⟩
  have left : start≤ scratch:=(A.start_mono start frozen_ (Nat.zero_le S.length)).trans before
  have roomRanks t (live:t<S.length) B (at_ : A.compact t=some B) : B.Fits bw scratch := by
    have fit:=b.path.snapshot_rank_rooms A start first ranks t live B at_
    exact ⟨fit.1,fit.2.1,fit.2.2.trans left⟩
  obtain ⟨o,ran,cheap,counters,ports,frame⟩:=frozen_roster X G S b hp base width hop_ L init ok
    (A.rooms bw start frozen_ scratch size₀ S.length before enough roomRanks)
    (Snapshots.seed_read scratch (seedAncestry X G S b) lit fits)
    (snapshot_fields X G S b hp base width A start scratch first bounds before enough ranks labels)
    (fun _ _=>rfl) cap last fresh room original alive payload
  refine ⟨o,?_,cheap_seq (cheap_seq boot.2 seed.2.1) cheap,counters,ports,frame⟩
  exact Procedure.Exec.then (Procedure.Exec.then boot.1 seed.1) ran

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.publicSpine Branch.publicLayout
  Branch.originalPin Branch.cohortHome Branch.cohort Branch.atCohort Branch.densePin
