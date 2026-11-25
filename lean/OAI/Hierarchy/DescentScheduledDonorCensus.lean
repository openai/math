import OAI.Hierarchy.DescentPackedReadUnique
import OAI.Hierarchy.DescentScheduledRangeInput
import OAI.Hierarchy.DescentRetainedRoleOccupancy
import OAI.Hierarchy.DescentArchivePaddedNodes

namespace OAI
/-! # The full original local-node census in a paid remixed primary -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSixParty.Chronology DescentSIMDLookup DescentWalshPrecision DescentSixParty.PackedFlow.Padded ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
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


open DescentBundleHistory
open DescentRetainedRangeDigits DescentDatedPriorOperand DescentLocalArchiveOrder DescentKernelHistory
open DescentGL DescentColonies DescentPackedColony DescentSixParty.PackedFlow.Channels
variable (data : Fin (pack).dataRect.pages→Fin ports.operandHosts→Fin (old).groups→Cell (ports.operandBits*ports.nodes))
    (roles : Fin (2^k)→Fin ports.operandHosts→Fin (old).groups→Cell (ports.tokenBits*ports.nodes))
local notation "X" => padValues G S board k tail age p f gain drift degree h ordinary op s Z ports floor data roles
local notation "l" => loaded
variable (size : 2^((l).high+(l).low)=(l).groups*(l).blocks)
    (cut : (l).cut≤(l).high+(l).low) (matrix : DescentGL.Layout ((l).high+(l).low))
    (carrier : Fin (l).hosts) (hi : Block (l).cut) (d₀ : Fin (l).donors)
local notation "physical" => (l).site (fun j=>blockValues cut ((l).before size (X) j) matrix) carrier hi
local notation "src_" => (rearrange matrix).symm (DescentIssuedFallbackPanel.join cut hi d₀)
local notation "coords" => (finProdFinEquiv.symm (Fin.cast size src_) : Fin (l).groups × Fin (l).blocks)
local notation "prior" => ({(l).previousLayout with hosts:=ports.operandHosts} : DescentDatedPriorOperand.Layout)

variable (r₀ : Reached U G q ε S k age z D wire hist) (B : BitDescription U) (number : Local B)
variable (groups : S.groupCount age=(old).groups)
variable (population : Fintype.card r₀.V≤ports.operandHosts) (topHosts : Fintype.card r₀.V≤(old).hosts)
local notation "groupAt" => (coords).1.cast groups.symm
local notation "blockAt" => (coords).2
local notation "homeName" => r₀.vertex.trans (Fin.castLEEmb topHosts)
variable (role : NodeOrder.All B→Cell ports.tokenBits)
variable (trueRows : ∀x h' g',roles x h' g'=encode ports.tokenBits ports.nodes (fun n'=>
  (Reached.NodeCells.atPhysical r₀ B number x n' h' (g'.cast groups.symm)).elim 0 role))

include trueRows population in
theorem scheduled_original_count (positive : 0<ports.operandBits) (nonzero : ∀y,(role y).val≠0)
    (enough : ∀v,Fintype.card (B.recipe v).Node≤ports.nodes) :
    (l).originalCount physical d₀=∑v,if DescentPaidResidentCount.occupies r₀.placement
      (Equiv.refl _) homeName carrier groupAt blockAt v then Fintype.card (B.recipe v).Node else 0 := by
  classical
  apply Reached.NodeCells.original_count r₀ B number homeName (fun _=>rfl) blockAt carrier groupAt
    (l) physical d₀ enough role nonzero
  intro j
  rw [scheduled_original_presence G S board k tail age p f gain drift degree h ordinary op s Z
    ports floor data roles size cut matrix carrier hi d₀ positive j]
  by_cases found : carrier.val<ports.operandHosts
  · unfold extend
    erw [dite_eq_left found]
    erw [trueRows (coords).2 ⟨carrier.val,found⟩ (coords).1, Equiv.symm_apply_apply]
    rfl
  · have absent : Reached.NodeCells.atPhysical r₀ B number blockAt j carrier groupAt=none:=by
      cases candidate:Reached.NodeCells.atPhysical r₀ B number blockAt j carrier groupAt with
      | none=>rfl
      | some y=>
        rcases y with ⟨v',n'⟩
        have where_ := (Reached.NodeCells.atPhysical_some r₀ B number blockAt j carrier groupAt v' n').mp candidate
        have hostFits:=(r₀.vertex (r₀.placement.pos v').2).isLt.trans_le population
        exact False.elim (found (where_.1 ▸ hostFits))
    have zero : encode ports.tokenBits ports.nodes (fun _=>0)=0:=by
      apply Fin.ext
      change (finFunctionFinEquiv (fun _ : Fin ports.nodes=>(0:Cell ports.tokenBits))).val=0
      simp
    simp only [extend,dite_eq_right found,absent,Option.elim_none]
    rw [←zero,Equiv.symm_apply_apply]

private theorem packed_cast {b₀ b₁ n : ℕ} (eqn : b₀=b₁) (y : Fin n→Cell b₁) :
    (encode b₀ n (fun i=>(y i).cast (congrArg (2^·) eqn.symm))).val=(encode b₁ n y).val :=by
  subst b₁;rfl

open DescentPrimitivePalette DescentBundleHistory
/-- All four pointer header digits of an occupied donor come from its genuine previous argument page. -/
theorem registered_original_header {bound : ℕ} (room : DatePorts.RangeRoom ports r₀ B)
    (spec : WorldShape p bound B) (label : NodeOrder.All B→Label G s Z op)
    (pointer : NodeOrder.All B→ℕ→DescentOperandStateBanks.Pointer)
    (flags : Fin (2^(old).k)→Fin ports.nodes→Fin ports.operandHosts→Fin (old).groups→ℕ)
    (mem : Memory w) (archive : DatePorts.ArchiveRead ports r₀ B number room spec op label pointer flags mem)
    (host : Fin ports.operandHosts) (hosted : carrier.val=host.val) (node : Fin ports.nodes) (y : NodeOrder.All B)
    (j : Fin ports.argumentsPerNode) (field : Fin 4)
    (width : ports.operandBits*ports.nodes*ports.operandLanes≤w) :
    let sourceBlock:=(coords).2.cast (congrArg (2^·) room.radix)
    let f₁:=field.castLE (by decide : 4≤7)
    Reads (previousBank ports.rangeLayout ports.archive.arguments sourceBlock (DescentOperandStateBanks.page f₁ j))
      (data ((l).sourceID ((l).operandField f₁ j) (coords).2)) ports.operandLanes mem →
    DatePorts.slotAt ports r₀ B number room sourceBlock node host (coords).1=some y →
    j.val<(occurrences (spec.sites y.1) y.2).length →
    ((l).entry physical d₀ node ((l).operandField f₁ j)).val=(pointer y j.val).header field :=by
  intro sourceBlock f₁ paid present live
  obtain ⟨cells,written,read⟩:=archive.headers sourceBlock j field
  rw [scheduled_original_seven G S board k tail age p f gain drift degree h ordinary op s Z ports floor
    data roles size cut matrix carrier hi d₀ f₁ j host hosted node]
  rw [paid.determined written room.positive width]
  exact read host (coords).1 node y present live

include population in
theorem registered_original_count {bound : ℕ} (room : DatePorts.RangeRoom ports r₀ B)
    (shape : WorldShape p bound B) (label : NodeOrder.All B→Label G s Z op)
    (pointer : NodeOrder.All B→ℕ→DescentOperandStateBanks.Pointer)
    (flags : Fin (2^(old).k)→Fin ports.nodes→Fin ports.operandHosts→Fin (old).groups→ℕ)
    (mem : Memory w) (archive : DatePorts.ArchiveRead ports r₀ B number room shape op label pointer flags mem)
    (sizes : ports.RoleRows) (width : ports.tokenBits=printedBits G s Z op)
    (rolePitch : 0<ports.roleLanes) (capWord : ports.tokenBits*ports.nodes*ports.roleLanes≤w)
    (source : ∀x : Fin (2^k),Reads (ports.archive.roles.bank x.val) (roles x) ports.roleLanes mem)
    (positive : 0<ports.operandBits) :
    (l).originalCount physical d₀=∑v,if DescentPaidResidentCount.occupies r₀.placement
      (Equiv.refl _) homeName carrier ((coords).1.cast room.groups.symm) blockAt v
      then Fintype.card (B.recipe v).Node else 0 := by
  classical
  let token_ (y : NodeOrder.All B):=(token G s Z op (label y)).cast (congrArg (2^·) width.symm)
  have nn (y : NodeOrder.All B) : (token_ y).val≠0:=by simp [token_,token_val]
  obtain ⟨_,known,seen,printed⟩:=archive.pad_witness (l) width sizes
  have rows (x : Fin (2^k)) (h' : Fin ports.operandHosts) (g' : Fin (old).groups) :
      roles x h' g'=encode ports.tokenBits ports.nodes (fun j=>
        (Reached.NodeCells.atPhysical r₀ B number x j h' (g'.cast room.groups.symm)).elim 0 token_) :=by
    let x':=x.cast (congrArg (2^·) room.radix)
    have equal:roles x=known x':=(source x).determined (seen x').2 rolePitch capWord
    rw [equal]
    apply Fin.ext
    apply (printed x' h' g').trans
    symm
    have same (j : Fin ports.nodes) : (DatePorts.slotAt ports r₀ B number room x' j h' g')=
        Reached.NodeCells.atPhysical r₀ B number x j h' (g'.cast room.groups.symm):=by
      simp only [DatePorts.slotAt,x',Fin.cast_cast,Fin.cast_eq_self]
    have cells (j : Fin ports.nodes) : ((DatePorts.slotAt ports r₀ B number room x' j h' g').elim 0
        (fun y=>token G s Z op (label y))).cast (congrArg (2^·) width.symm)=
        (Reached.NodeCells.atPhysical r₀ B number x j h' (g'.cast room.groups.symm)).elim 0 token_ :=by
      rw [same j]
      cases Reached.NodeCells.atPhysical r₀ B number x j h' (g'.cast room.groups.symm) <;> rfl
    rw [show (fun j : Fin ports.nodes=>(Reached.NodeCells.atPhysical r₀ B number x j h'
        (g'.cast room.groups.symm)).elim 0 token_)=fun j=>((DatePorts.slotAt ports r₀ B number room
        x' j h' g').elim 0 (fun y=>token G s Z op (label y))).cast (congrArg (2^·) width.symm)
        from funext fun j=>(cells j).symm]
    exact packed_cast width _
  exact scheduled_original_count G S board k tail age p f gain drift degree h ordinary op s Z ports floor
    data roles size cut matrix carrier hi d₀ r₀ B number room.groups population topHosts token_
    rows positive nn room.capacity

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
