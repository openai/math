import OAI.Hierarchy.DescentScheduledPaddedPages
import OAI.Hierarchy.DescentRetainedPanelPresence
import OAI.Hierarchy.DescentRetainedPanelRange
import OAI.Hierarchy.DescentPackedReadUnique

namespace OAI
/-! # The old registered words inside the scheduled primary donor panel -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
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


open DescentRetainedRangeDigits DescentDatedPriorOperand DescentLocalArchiveOrder DescentKernelHistory
open DescentGL DescentColonies DescentPackedColony DescentSixParty.PackedFlow.Channels
variable (data : Fin (ports.resetPad k).dataRect.pages→Fin ports.operandHosts→Fin ports.venue.groups→Cell (ports.operandBits*ports.nodes))
    (roles : Fin (2^k)→Fin ports.operandHosts→Fin ports.venue.groups→Cell (ports.tokenBits*ports.nodes))
local notation "X" => padValues G S board k tail age p f gain drift degree h ordinary op s Z ports floor data roles
local notation "l" => loaded
variable (size : 2^((previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor).high+(previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor).low)=ports.venue.groups*(2^k))
    (cut : (previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor).cut≤(previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor).high+(previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor).low) (matrix : DescentGL.Layout ((previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor).high+(previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor).low))
    (carrier : Fin ports.venue.hosts) (hi : Block (previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor).cut) (d₀ : Fin (previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor).donors)
local notation "physical" => (l).site (fun j=>blockValues cut ((l).before size (X) j) matrix) carrier hi
local notation "src_" => (rearrange matrix).symm (DescentIssuedFallbackPanel.join cut hi d₀)
local notation "coords" => (finProdFinEquiv.symm (Fin.cast size src_) : Fin (l).groups × Fin (l).blocks)
local notation "prior" => ({(l).previousLayout with hosts:=ports.operandHosts} : DescentDatedPriorOperand.Layout)

theorem scheduled_original_presence (positive : 0<ports.operandBits) (n₀ : Fin ports.nodes) :
    ((l).entry physical d₀ n₀ (l).occupiedField).val≠0 ↔
      ((encode ports.tokenBits ports.nodes).symm
        (extend (old).hosts (roles (coords).2) carrier (coords).1) n₀).val≠0 :=by
  apply (l).issued_presence size cut matrix (X) carrier hi d₀ ports.tokenBits ports.roleLanes
    (fun x=>extend (old).hosts (roles x)) _ positive n₀
  intro x hx gx
  unfold padValues
  rw [((l).directory_role _ _ x).1]
  rfl

/-- Each of the seven fields comes from the same previous host, group, block and node after
the physical host padding and the GL matrix permutation. -/
theorem scheduled_original_seven (f₁ : Fin 7) (j : Fin ports.argumentsPerNode)
    (sourceHost : Fin ports.operandHosts) (same : carrier.val=sourceHost.val) (n₀ : Fin ports.nodes) :
    ((l).entry physical d₀ n₀ ((l).operandField f₁ j)).val=
      ((encode ports.operandBits ports.nodes).symm
        (data ((l).sourceID ((l).operandField f₁ j) (coords).2) sourceHost (coords).1) n₀).val :=by
  rw [(l).prior_digit (X) size cut matrix carrier hi d₀ n₀ ((l).operandField f₁ j)]
  unfold padValues
  erw [(l).directory_property]
  have inside : carrier.val<ports.operandHosts:=by rw [same];exact sourceHost.isLt
  unfold extend
  erw [dite_eq_left inside]
  erw [show (⟨carrier.val,inside⟩ : Fin ports.operandHosts)=sourceHost by exact Fin.ext same]
  have pair : (finProdFinEquiv.symm (DescentOperandStateBanks.page f₁ j) : Fin 7 × Fin ports.argumentsPerNode) = (f₁,j) := finProdFinEquiv.symm_apply_apply _
  erw [pair]
  rfl

/-- The old primitive's arity survives the very same padded, remixed bank
that determines its primary node number. Only the genuine prior metadata word
is required, at the original host pitch. -/
theorem scheduled_original_arity (rBank : Bank) (mem : Memory w) (live : 0<ports.operandLanes)
    (amount : Fin ports.operandHosts→Fin (old).groups→Fin ports.nodes→ℕ)
    (actual : Reads rBank (data (ports.arityIndex k (coords).2)) ports.operandLanes mem)
    (header : Reads rBank (fun h' g'=>encode ports.operandBits ports.nodes
      (fun n₀=>(amount h' g' n₀:Cell ports.operandBits))) ports.operandLanes mem)
    (capacity : ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (h' : Fin ports.operandHosts) (same : carrier.val=h'.val) (n₀ : Fin ports.nodes)
    (fit : amount h' (coords).1 n₀<2^ports.operandBits) :
    ((l).entry physical d₀ n₀ (l).arityField).val=amount h' (coords).1 n₀ :=by
  have measured:=actual.determined header live capacity
  rw [(l).prior_digit (X) size cut matrix carrier hi d₀ n₀ (l).arityField]
  unfold padValues
  rw [((l).directory_role _ _ (coords).2).2]
  change (DescentOrdinaryAtomFieldRAM.ScalarOperand.take n₀
    (extend (old).hosts (data (ports.arityIndex k (coords).2)) carrier (coords).1)).val=_
  have present : carrier.val<ports.operandHosts:=by rw [same];exact h'.isLt
  have place : (⟨carrier.val,present⟩:Fin ports.operandHosts)=h':=Fin.ext same
  simp only [measured,extend,dite_eq_left present,place,DescentOrdinaryAtomFieldRAM.ScalarOperand.take,
    Equiv.symm_apply_apply,Fin.val_cast_of_lt fit]

variable {B : BitDescription U} (mem : Memory w) (live : 0<ports.operandLanes)
    (block : NodeOrder.All B→Fin (2^k)) (host : NodeOrder.All B→Fin ports.operandHosts)
    (groupOf : NodeOrder.All B→Fin ports.venue.groups) (number : NodeOrder.All B→Fin ports.nodes)
local notation "registered" => fromRAM ports.archive prior ports.operandBits mem live block host groupOf number

theorem scheduled_original_range (y : NodeOrder.All B) (j : Fin ports.argumentsPerNode) (f₀ : Fin 3)
    (read : Reads (previousBank prior ports.archive.arguments (block y)
      (DescentOperandStateBanks.page (page f₀) j))
      (data ((l).sourceID ((l).operandField (page f₀) j) (block y))) ports.operandLanes mem)
    (width : ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (hosted : carrier.val=(host y).val) (located : coords=(groupOf y,block y)) :
    ((l).entry physical d₀ (number y) ((l).operandField (page f₀) j)).val=(registered).word y j.val f₀ := by
  apply (l).issued_prior_range size cut matrix (X) carrier hi d₀ ports.archive mem live
    block host groupOf number y j f₀ _ read width _ hosted located
  unfold padValues
  refine ((l).directory_property _ _ (page f₀) j (block y)).trans ?_
  have pair : (finProdFinEquiv.symm (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f₀) j) :
      Fin 7 × Fin ports.argumentsPerNode) = (DescentRetainedRangeDigits.page f₀,j) := finProdFinEquiv.symm_apply_apply _
  erw [pair]
  rfl

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
