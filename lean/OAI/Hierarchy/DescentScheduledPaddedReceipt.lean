import OAI.Hierarchy.DescentScheduledPaddedDate
import OAI.Hierarchy.DescentResetPriorHostPadHeld
import OAI.Hierarchy.DescentResetPriorHostPadRead

namespace OAI
/-! # The genuine prior venue and all normalized operand pages in one reached state -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSixParty.Chronology DescentSIMDLookup DescentWalshPrecision DescentSixParty.PackedFlow.Padded ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentPackedColony ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ)
    (ports : Chronology.DatePorts)
local notation "old" => ports.venue
local notation "io" => ports.io

local notation "a" => scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z ports
variable (floor w : ℕ)
local notation "ap" => (a) floor
local notation "post" => ports.afterPad k floor
local notation "next" => ports.priorStart k floor
local notation "pack" => ports.resetPad k
local notation "L" => (ap).inner.successor.setup.retained
local notation "cap" => ((capCalendar G.b S.rounds gain S.height).take age).prod*256
local notation "support" => ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
  ports.operandLanes ports.roleLanes old io next w (post).archive

local notation "raw" => previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor

local notation "publisher" => priorArchivePhase G S board k tail age p f gain drift degree h ordinary op s Z ports floor w

open DescentOrdinaryHostPad
variable {V : Type} {width : ℕ} {bits : V→ℕ} {U : MarkedWorld F width V bits}
    {q ε : ℝ} {z D wire hist : ℕ}
local notation "loaded" => ({raw with hosts:=(old).hosts} : DescentResetRetainedSetup.Layout)

theorem archive_seed_metadata (layout : DescentResetRetainedSetup.Layout) (archive : PriorResetArchive)
    (seed : archive.seed=true) (field : Fin 2) (block : Fin layout.blocks) :
    archive.prior layout (layout.sourceID (if field=0 then layout.occupiedField else layout.arityField) block) =
      layout.previousChart.seedBank archive.nodeBase field block := by
  unfold PriorResetArchive.prior
  rw [seed]
  simp only [ite_true,DescentResetRetainedSetup.Layout.seedPrior,DescentResetRetainedSetup.Layout.priorBanks]
  fin_cases field
  · exact (layout.directory_role _ _ block).1
  · exact (layout.directory_role _ _ block).2

theorem archive_operand_bank (layout : DescentResetRetainedSetup.Layout) (archive : PriorResetArchive)
    (field : Fin 7) (arg : Fin layout.previousArgs) (block : Fin layout.blocks) :
    archive.prior layout (layout.sourceID (layout.operandField field arg) block) =
      DescentDatedPriorOperand.previousBank layout.previousLayout archive.arguments block
        (DescentOperandStateBanks.page field arg) := by
  unfold PriorResetArchive.prior
  split <;> simp only [DescentResetRetainedSetup.Layout.seedPrior,
    DescentResetRetainedSetup.Layout.laterPrior,DescentResetRetainedSetup.Layout.priorBanks]
  all_goals
    exact layout.directory_property _
      (fun pg x => DescentDatedPriorOperand.previousBank layout.previousLayout archive.arguments x pg) field arg block

theorem scheduled_pad_issued (r : Reached U G q ε S k age z D wire hist) (m : Memory w)
    (seen : ports.held r floor m) (count : ports.archive.count.base<floor) (wires : ports.WireRoom w floor)
    (blocks : (old).k=k) (capDate : (old).cap=r.placement.cap) (groups : (old).groups=S.groupCount age)
    (native : ports.archive.Fits raw floor) (roleBlocks : 2^k≤ports.archive.roles.blocks)
    (roleLimit : ports.archive.roles.endAddress≤floor) (room : next<2^w)
    (live : 0<ports.roleLanes) (data : Fin (pack).dataRect.pages→Fin ports.operandHosts→Fin (old).groups→Cell (ports.operandBits*ports.nodes))
    (roles : Fin (2^k)→Fin ports.operandHosts→Fin (old).groups→Cell (ports.tokenBits*ports.nodes))
    (stored : ∀j,ports.operandHosts*chunks (old).groups ports.operandLanes≤(ports.archive.prior raw j).size ∧
      Reads (ports.archive.prior raw j) (data j) ports.operandLanes m)
    (tokens : ∀j,ports.operandHosts*chunks (old).groups ports.roleLanes≤(ports.archive.roles.bank j.val).size ∧
      Reads (ports.archive.roles.bank j.val) (roles j) ports.roleLanes m) :
    let after:=(publisher).image m
    (publisher).Runs m ∧ (post).held r next after ∧
      (∀(f : Fin 2) (x : Fin (2^k)),Reads ((post).archive.prior (loaded)
          ((loaded).sourceID (if f=0 then (loaded).occupiedField else (loaded).arityField) x))
        (if f=0 then fun h g=>(ports.presence k).readings (extend (old).hosts (roles x) h g)
          else extend (old).hosts (data (ports.arityIndex k x))) ports.operandLanes after) ∧
      (∀(f : Fin 7) (arg : Fin ports.argumentsPerNode) (x : Fin (2^k)),let j:=(loaded).sourceID ((loaded).operandField f arg) x
        Reads ((post).archive.prior (loaded) j) (extend (old).hosts (data j)) ports.operandLanes after) ∧
      (∀j : Fin (2^k),Reads ((post).archive.roles.bank j.val)
        (extend (old).hosts (roles j)) ports.roleLanes after) ∧
      ∀z,z<floor ∨ next≤z→after z=m z :=by
  intro after
  have start:floor≤next:=(ports.pad_order k floor).1.trans (ports.pad_order k floor).2
  have oldFit:=start.trans_lt room
  have safe:∀j,(ports.archive.prior raw j).Fits w floor:=
    (raw).prior_registers ports.archive.seed ports.archive.nodeBase ports.archive.arguments floor w native.1 native.2 oldFit
  have bounds : ∀j : Fin (2^k),(ports.archive.roles.bank j.val).Fits w floor:=
    fun j=>ports.archive.roles.fits w floor j.val (j.isLt.trans_le roleBlocks) roleLimit oldFit
  have run:=ports.full_pad_any k floor (ports.archive.prior raw) (fun j=>ports.archive.roles.bank j.val)
    m safe bounds room
  have held:=(ports.held_below r floor next m after seen count wires blocks capDate groups start
      (fun i lt=>run.2 i (.inl lt)))
  have reads:=ports.full_pad_reads k floor (ports.archive.prior raw) (fun j=>ports.archive.roles.bank j.val) m
    safe bounds room live data roles stored tokens
  refine ⟨run.1,held,?_,?_,reads.2.2,run.2⟩
  · intro f x
    have bank : (post).archive.prior (loaded) ((loaded).sourceID (if f=0 then (loaded).occupiedField else (loaded).arityField) x) =
        (ports.presence k).bank ((pack).endAddress floor) f x:=by
      exact (archive_seed_metadata (loaded) (post).archive rfl f x).trans rfl
    rw [bank]
    exact reads.1 f x
  · intro f arg x j
    have native : (post).archive.prior (loaded) j=(pack).operandBank floor j:=by
      let original := (ports.padded ((loaded).inputShape ports) floor).archive
      exact (archive_operand_bank (loaded) (post).archive f arg x).trans
        ((archive_operand_bank (loaded) original f arg x).symm.trans ((loaded).padded_operand ports floor j))
    rw [native]
    exact reads.2.1 j

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
