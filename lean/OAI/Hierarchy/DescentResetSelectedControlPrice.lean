import OAI.Hierarchy.DescentResetControlTablesPrice
import OAI.Hierarchy.DescentResetSelectedVenueWork
import OAI.Hierarchy.DescentResetReceivedVolume

namespace OAI
/-! The repeated quantity census between signed pages and operand setup uses only the current receiver pitch. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentDatedAddressBook DescentCompiler TerminalScale DescentPackedWalsh ProtocolRAM
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false

private theorem rootLookupUnit (output : ResetOutput) :
    2^output.middle.rootDepth * Nat.clog 2 (2^output.middle.rootDepth+1) ∈ output.rootUnits := by
  simp [ResetOutput.rootUnits]

private theorem rotorLookupUnit (output : ResetOutput) :
    output.setup.rotorBits+1 ∈ output.receiverUnits := by
  simp [ResetOutput.receiverUnits]

open DescentVenueQuantityPlanes

private theorem controlAreaBound (h hosts jobs gain previous next : ℕ) (smaller : next≤previous) :
    1+(hosts*jobs+hosts*gain+(hosts*jobs)*previous+(hosts*gain)*next+(hosts*jobs)*next+(h+1)^3*2^(h/2)) ≤
      (12*(jobs+gain+1))*ResetOutput.receiptArea h hosts previous := by
  let A := ResetOutput.receiptArea h hosts previous
  have shared : (h+1)^3*2^(h/2) ≤ A := Nat.le_add_left ..
  have one : 1≤A := (by positivity : 0<(h+1)^3*2^(h/2)).trans_le shared
  have hostBound : hosts≤A := by dsimp only [A,ResetOutput.receiptArea]; omega
  have currentRows : hosts*previous≤A := by dsimp only [A,ResetOutput.receiptArea]; omega
  have nextRows : hosts*next≤A := (Nat.mul_le_mul_left hosts smaller).trans currentRows
  have raw : hosts*jobs≤jobs*A := by simpa only [Nat.mul_comm hosts jobs] using Nat.mul_le_mul_left jobs hostBound
  have fresh : hosts*gain≤gain*A := by simpa only [Nat.mul_comm hosts gain] using Nat.mul_le_mul_left gain hostBound
  have priorJobs : hosts*jobs*previous≤jobs*A := by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left jobs currentRows
  have nextJobs : hosts*jobs*next≤jobs*A := by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left jobs nextRows
  have gained : hosts*gain*next≤gain*A := by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left gain nextRows
  change _ ≤ (12*(jobs+gain+1))*A
  nlinarith only [one,raw,fresh,priorJobs,nextJobs,gained,shared,Nat.zero_le (jobs*A),Nat.zero_le (gain*A)]

private theorem controlFactorBound (blocks : ℕ) :
    resetPlaneFactor blocks+4096≤2*resetPlaneFactor 1*(blocks+1) := by
  have big : 4096≤resetPlaneFactor 1 := by
    have enough : 2≤CandidateFront.volumeFactor 1 1 := by decide
    unfold resetPlaneFactor
    omega
  have linear := planeFactor_linear blocks
  have large : 4096≤resetPlaneFactor 1*(blocks+1) :=
    big.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  rw [Nat.mul_assoc]
  omega

set_option maxHeartbeats 1500000
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail i p f g drift degree h nextM C packet oldLanes primitiveLanes printedBits : ℕ)
    (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ)
local notation "prev" => resetCut S k tail p f h i
local notation "e" => PhysicalReset.receiverCut G S board k tail i p f g drift degree h prev nextM C packet oldLanes primitiveLanes printedBits old
local notation "date" => PhysicalReset.selected G S board k tail i p f g drift degree h prev nextM C packet oldLanes primitiveLanes
  printedBits old io.wire io.roster floor
local notation "v" => (date).successor
local notation "pr" => ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old
local notation "at₀" => (date).rebased ((date).stageStart floor)
local notation "cap" => ((capCalendar G.b S.rounds g S.height).take i).prod*256

open DescentVenueQuantityPlanes DescentDatedAddressBook.CandidateFront DescentSIMDLookup
local notation "pop" => S.groupCount i
local notation "res" => S.groupCount (i+1)
local notation "H" => S.hostSize i
local notation "M" => 2^e
local notation "N" => 2^k

theorem selected_control_work (D rate : ℕ) (live : i<S.length) (radix : S.radix=2^k)
    (origin : old.hosts=H) (size : old.k=k) (degreeAt : old.degree=D) (rootRoom : 8*(v).groupWidth≤h)
    (blocks : N≤ TerminalScale.scale S.height rate) (previous : cap≤ TerminalScale.scale S.height rate)
    (grow : 2^S.hostGain*S.radix≤ TerminalScale.scale S.height rate) :
    (v).controlRegisters.fee≤ResetOutput.venueLead n d D f g*TerminalScale.scale S.height (3*rate)*
      ResetOutput.receiptArea h H (chunks pop M) := by
  let issued := ResetOutput.fromBoard G S board k tail i p f g drift degree h e prev (2^e) nextM C packet pr at₀
  have output : (v) = issued := PhysicalReset.named_successor G S board k tail i p f g drift degree h e prev
    (2^e) nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  have inventory := PhysicalReset.selected_inventory G S board k tail i p f g drift degree h prev nextM C
    packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  let seed := ResetOutput.fromBoard G S board k tail i p f g drift degree h 0 prev 1 nextM C packet pr 0
  have width : (v).groupWidth = seed.groupWidth := by
    have roots : (v).rootUnits = seed.rootUnits := inventory.1
    have receivers : (v).receiverUnits = seed.receiverUnits := inventory.2.1
    unfold ResetOutput.groupWidth
    rw [roots, receivers]
  have bought (x : ℕ) (used : x∈issued.rootUnits ∨ x∈issued.receiverUnits) : x*2^e ≤ h/2 := by
    rw [←output] at used
    have paid := PhysicalReset.selected_room G S board k tail i p f g drift degree h prev nextM C
      packet oldLanes primitiveLanes printedBits old io.wire io.roster floor x (width ▸ rootRoom) used
    rwa [inventory.2.2.1] at paid
  rw [output]
  let c:=issued.controlRegisters
  let jobs:=issued.venue.dense.shapes
  let gain:=2^S.hostGain*S.radix
  let A:=ResetOutput.receiptArea h H (chunks pop M)
  let coeff:=12*(jobs+gain+1)
  have blockRoom : N*M≤h/2:=by
    have lookupBound:=bought (2^issued.middle.rootDepth*Nat.clog 2 (2^issued.middle.rootDepth+1))
      (.inl (rootLookupUnit _))
    change (N*Nat.clog 2 (N+1))*M≤h/2 at lookupBound
    have high:0<Nat.clog 2 (N+1):=Nat.clog_pos (by decide) (by have nPos:=Nat.two_pow_pos k;omega)
    exact (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ high)).trans lookupBound
  have half : M≤h/2 := (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)).trans blockRoom
  have wide:=half.trans (Nat.div_le_self ..)
  have dict : (c.bits+1)*M≤h/2:=bought (issued.setup.rotorBits+1)
    (.inr (rotorLookupUnit _))
  have phys:=c.fee_funded h (Nat.two_pow_pos k) (Nat.two_pow_pos e) wide wide
    (by change 1*M≤h/2;simpa only [Nat.one_mul] using half)
    (by change (1*N)*M≤h/2;simpa only [Nat.one_mul] using blockRoom) dict
  have group:res*N=pop:=by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits live radix)).symm
  have reduce : res≤pop:=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)).trans_eq group
  have rows : chunks res M≤chunks pop M:=Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right reduce _) _)
  have step:S.hostSize (i+1)=H*gain:=by simp only [AtomSchedule.hostSize,pow_succ,Nat.mul_assoc,gain]
  have area : planeEnvelope c.dims h≤coeff*A := by
    change 1+(old.hosts*jobs+S.hostSize (i+1)+(old.hosts*jobs)*chunks (res*N) M+
      S.hostSize (i+1)*chunks res M+(old.hosts*jobs)*chunks res M+(h+1)^3*2^(h/2))≤_
    rw [origin,step,group]
    exact controlAreaBound h H jobs gain (chunks pop M) (chunks res M) rows
  have scaleFactor := ResetOutput.original_venue_coefficient G S board k tail i p f g drift degree h e prev nextM C packet pr at₀
    D S.height rate degreeAt size blocks previous grow
  have localBound : (resetPlaneFactor c.dims.blocks+4096)*coeff≤ResetOutput.venueFactor issued.venue gain := by
    unfold ResetOutput.venueFactor
    apply Nat.mul_le_mul_right
    change resetPlaneFactor N+4096≤2*resetPlaneFactor 1*(N+1)+_+_
    exact (controlFactorBound N).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  calc
    _ ≤ (resetPlaneFactor c.dims.blocks+4096)*(coeff*A) := phys.trans (Nat.mul_le_mul_left _ area)
    _ = ((resetPlaneFactor c.dims.blocks+4096)*coeff)*A := (Nat.mul_assoc ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ (localBound.trans scaleFactor)

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
