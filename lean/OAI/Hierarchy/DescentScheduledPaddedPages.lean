import OAI.Hierarchy.DescentScheduledPaddedReceipt
import OAI.Hierarchy.DescentResetPriorFieldCases
import OAI.Hierarchy.DescentResetOperandMovedSources

namespace OAI
/-! # All prior source banks at the numeric input of the reset operand mover -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentPackedColony DescentBundleHistory DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSixParty.Chronology DescentSIMDLookup DescentWalshPrecision DescentSixParty.PackedFlow.Padded ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
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

/-- Old physical source words after reindexing onto the full incoming host rectangle. -/
def padValues
    (data : Fin (pack).dataRect.pages→Fin ports.operandHosts→Fin (old).groups→Cell (ports.operandBits*ports.nodes))
    (roles : Fin (2^k)→Fin ports.operandHosts→Fin (old).groups→Cell (ports.tokenBits*ports.nodes)) :
    (loaded).Values :=
  (loaded).directory (fun flag x=>if flag=0 then
      fun h g=>(ports.presence k).readings (extend (old).hosts (roles x) h g)
    else extend (old).hosts (data (ports.arityIndex k x)))
    (fun pg x=>let pair : Fin 7×Fin ports.argumentsPerNode:=finProdFinEquiv.symm pg
      extend (old).hosts (data ((loaded).sourceID ((loaded).operandField pair.1 pair.2) x)))

theorem scheduled_pad_pages (r : Reached U G q ε S k age z D wire hist) (m : Memory w)
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
    ∀j : Fin (loaded).sources,
      let bank:=(post).archive.prior (loaded) j
      bank.Fits w next ∧ (old).hosts*chunks (old).groups ports.operandLanes≤bank.size ∧
        Reads bank (padValues G S board k tail age p f gain drift degree h ordinary op s Z ports floor data roles j)
          ports.operandLanes ((publisher).image m) :=by
  have receipt:=scheduled_pad_issued G S board k tail age p f gain drift degree h ordinary op s Z ports floor w
    r m seen count wires blocks capDate groups native roleBlocks roleLimit room live data roles stored tokens
  have oldRoom:=(ports.pad_order k floor).2
  apply (loaded).source_cases
  · intro flag x
    let field:=if flag=0 then (loaded).occupiedField else (loaded).arityField
    have address:(post).archive.prior (loaded) ((loaded).sourceID field x)=
        (ports.presence k).bank ((pack).endAddress floor) flag x:=by
      exact (archive_seed_metadata (loaded) (post).archive rfl flag x).trans rfl
    have bounds:=(ports.presence k).placed ((pack).endAddress floor) room flag x
    refine ⟨address.symm ▸ bounds.1,address.symm ▸ bounds.2,?_⟩
    have done:=receipt.2.2.1 flag x
    fin_cases flag
    · unfold padValues
      erw [((loaded).directory_role _ _ x).1]
      exact done
    · unfold padValues
      erw [((loaded).directory_role _ _ x).2]
      exact done
  · intro f arg x
    let j:=(loaded).sourceID ((loaded).operandField f arg) x
    have address:(post).archive.prior (loaded) j=(pack).operandBank floor j:=by
      let original := (ports.padded ((loaded).inputShape ports) floor).archive
      exact (archive_operand_bank (loaded) (post).archive f arg x).trans
        ((archive_operand_bank (loaded) original f arg x).symm.trans ((loaded).padded_operand ports floor j))
    have bounds:=(pack).operand_fit floor (oldRoom.trans_lt room) j
    refine ⟨address.symm ▸ ⟨bounds.1.1,bounds.1.2.1,bounds.1.2.2.trans oldRoom⟩,address.symm ▸ bounds.2,?_⟩
    have done:=receipt.2.2.2.1 f arg x
    unfold padValues
    rw [(loaded).directory_property]
    dsimp only [DescentOperandStateBanks.page]
    erw [finProdFinEquiv.symm_apply_apply]
    exact done

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
