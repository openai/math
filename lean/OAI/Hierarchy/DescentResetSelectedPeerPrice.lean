import OAI.Hierarchy.DescentResetSelectedMaskPrice

namespace OAI
/-! # The four true compact peer rows and their broadcast at the selected pitch -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentDatedAddressBook DescentSIMDLookup DescentPackedWalsh DescentFallbackPeriod
open ProtocolRAM DescentStaticWordColumn
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {d k i D n C f g rate tail h₀ : ℕ}
    {G : PoweredGadget F} {S : AtomSchedule} (rates : ResetRates G S k D n h₀ C f g rate tail)
    (p h drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ)
    (old : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor : ℕ)
local notation "cut₀" => resetCut S k tail p f h i
local notation "date₀" => PhysicalReset.selected G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
local notation "e₀" => PhysicalReset.receiverCut G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old
local notation "v" => (date₀).successor
local notation "s" => (v).sheets
local notation "base₀" => (date₀).rebased ((date₀).stageStart floor)
local notation "inc" => 2^S.hostGain*S.radix
local notation "budget" => compiledSourceWork (v).front.peer.oldDegree
local notation "G₀" => chunks (S.groupCount i) (2^e₀)
local notation "H₀" => S.hostSize i

private theorem endpoint_positive (D sh cap : ℕ) : 0< CandidateFront.endpointWidth D sh cap :=
  ((Nat.clog_pos (by decide) (by omega) : 0< Nat.clog 2 (D+2)).trans_le
    (Nat.le_add_right _ (Nat.clog 2 (sh+1)))).trans_le (le_max_right ..)

private theorem peer_bound (jobs degree hosts raw rows pages X : ℕ)
    (one : 1≤ X) (h : hosts≤ X) (sparse : raw≤ X) (r : rows≤ X) (p : pages≤ X) :
    7*(18000*(hosts+1)*(degree+1)+150*(raw+1)+25*(2*rows+pages)+38) ≤
      32768*(jobs+1)*(compiledSourceWork degree+1)*X := by
  have weighted := Nat.mul_le_mul_right (degree+1) (Nat.add_le_add h one)
  unfold compiledSourceWork mixedSourceWork
  nlinarith only [weighted,sparse,r,p,one,Nat.zero_le (jobs*degree*X),Nat.zero_le (jobs*X),Nat.zero_le (degree*X)]

private theorem rectangle_parts (rows raw half X : ℕ) (bound : 1+rows+raw+half≤X) :
    1≤X ∧ raw≤X ∧ rows≤X := by omega

private theorem meta_mem (output : ResetOutput) : output.sheets.metaBits∈output.rootUnits :=
  by simp [ResetOutput.rootUnits]

private theorem instruction_bound (ticks words limit : ℕ) (billed : ticks+words≤limit) :
    ticks+7*words ≤ 7*limit := by omega

set_option maxHeartbeats 850000 in
theorem selected_peer_volume {w : ℕ} (u : (date₀).DateInputs ((date₀).stageStart floor) w)
    (radix : S.radix=2^k) (live : i< S.length) (rootRoom : 8*(v).groupWidth≤ h) :
    let actual := (v).jointPhase base₀ u.earlier w
    PhysicalReset.instructionWords actual.program actual.ticks ≤
      ResetOutput.maskFactor (s).jobs budget (v).front.peer.shapes inc*ResetOutput.receiptArea h H₀ G₀ := by
  intro actual
  let A := ResetOutput.receiptArea h H₀ G₀
  let X := (2+(v).front.peer.shapes+inc)*A
  have rawShape := ResetOutput.mask_envelope_area G S rates.board k tail i p f g drift degree h e₀
    cut₀ nextM C packet (ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old)
    base₀ radix live
  let pr := ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits old
  let out := ResetOutput.fromBoard G S rates.board k tail i p f g drift degree h e₀ cut₀ (2^e₀)
    nextM C packet pr base₀
  have outputEq : (v) = out := PhysicalReset.named_successor G S rates.board k tail i p f g drift degree h
    e₀ cut₀ (2^e₀) nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
  change 1+out.sheets.hosts*chunks out.sheets.groups out.sheets.lanes+out.front.peer.hosts+2^(h/2) ≤
    (2+out.front.peer.shapes+inc)*A at rawShape
  rw [←outputEq] at rawShape
  obtain ⟨positive,rawLe,rowsLe⟩ := rectangle_parts _ _ _ _ rawShape
  have oldRooms : H₀ ≤ A := by dsimp only [A,ResetOutput.receiptArea];omega
  have newRoom : (s).hosts ≤ X := by
    change S.hostSize (i+1) ≤ _
    calc
      _ = inc*H₀ := by simp only [AtomSchedule.hostSize,pow_succ];ring
      _ ≤ inc*A := Nat.mul_le_mul_left _ oldRooms
      _ ≤ _ := Nat.mul_le_mul_right A (by omega)
  have oneArea : A ≤ X := Nat.le_mul_of_pos_left _ (by omega)
  have bits : 0 < (s).metaBits := endpoint_positive _ _ _
  have lanes : 0 < (s).lanes := Nat.two_pow_pos _
  have member := meta_mem (v)
  have exp_eq := selected_root_exponent (i:=i) rates p h drift degree nextM packet oldLanes
    primitiveLanes printedBits old io.wire io.roster floor
  have packed := (v).operand_room cut₀ cut₀ (S.groupWidth k tail (i+1)) h rootRoom (Or.inl member)
  rw [exp_eq] at packed
  change (s).metaBits*(s).lanes ≤ h/2 at packed
  have bcap := (Nat.le_mul_of_pos_right _ lanes).trans packed
  have mcap := (Nat.le_mul_of_pos_left _ bits).trans packed
  have page : ((s).lanes+1)*2^(s).metaBits ≤ X := by
    have mm : (s).lanes+1 ≤ (h+1)^3 := by
      have hh : h+1 ≤ (h+1)^3 := by nlinarith only [Nat.zero_le (h*h*h),Nat.zero_le (h*h),Nat.zero_le h]
      omega
    apply le_trans (Nat.mul_le_mul mm (Nat.pow_le_pow_right (by decide) bcap))
    exact (Nat.le_add_left .. : (h+1)^3*2^(h/2) ≤ A).trans oneArea
  have billed := (v).peerJoint_price base₀ u.earlier w
  have native : PhysicalReset.instructionWords actual.program actual.ticks ≤
      7*(18000*((s).hosts+1)*((v).front.peer.oldDegree+1)+150*((v).front.peer.hosts+1)+
          25*(2*((s).hosts*chunks (s).groups (s).lanes)+((s).lanes+1)*2^(s).metaBits)+38) := by
    change actual.ticks+names actual.program ≤ _ at billed
    unfold PhysicalReset.instructionWords
    dsimp only [DescentResetPeerJointBroadcast.count,DescentResetHaloBroadcast.count] at billed
    exact instruction_bound _ _ _ billed
  apply native.trans
  simpa only [ResetOutput.maskFactor,X,A,Nat.mul_assoc] using
    peer_bound (s).jobs (v).front.peer.oldDegree (s).hosts (v).front.peer.hosts
      ((s).hosts*chunks (s).groups (s).lanes) (((s).lanes+1)*2^(s).metaBits) X
      positive newRoom rawLe rowsLe page

local notation "bits₀" => S.localWalshBits p ((S.groupWidth k tail i)+k) f (quota S.rounds)

theorem selected_peer_invoice {w : ℕ} (u : (date₀).DateInputs ((date₀).stageStart floor) w)
    (localRate receiver ratio saving lead exponent : ℕ)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (live : i< S.length)
    (localRoom : 8*bits₀≤ h) (rootRoom : 8*(v).groupWidth≤ h)
    (jobs : (s).jobs≤ TerminalScale.scale S.height localRate)
    (oldDegree : (v).front.peer.oldDegree≤ TerminalScale.scale S.height localRate)
    (shapes : (v).front.peer.shapes≤ TerminalScale.scale S.height localRate)
    (growth : inc≤ TerminalScale.scale S.height localRate)
    (blocks : 2^k≤ TerminalScale.scale S.height localRate) (low : bits₀≤ TerminalScale.scale S.height localRate)
    (units : (v).groupWidth≤ TerminalScale.scale S.height receiver)
    (age : S.height≤ Nat.log 2 h) (ambient : 2^h≤ S.initialSites) (word : w≤ ratio*h)
    (quote : ∀ j jcount D shapes growth H groups δ copies N b width rows w fee,
      j≤ Nat.log 2 h → 2^h≤ copies → jcount≤ TerminalScale.scale j localRate → D≤ TerminalScale.scale j localRate →
      shapes≤ TerminalScale.scale j localRate → growth≤ TerminalScale.scale j localRate →
      N≤ TerminalScale.scale j localRate → b≤ TerminalScale.scale j localRate → width≤ TerminalScale.scale j receiver →
      w≤ ratio*h → rows*h≤(2+N)*h+groups*(32*N*b+16*width) →
      fee≤ ResetOutput.maskFactor jcount (compiledSourceWork D) shapes growth*ResetOutput.receiptArea h H rows → 1≤δ →
      fee*w≤ H*h*(lead*TerminalScale.scale j exponent)+H*(groups*δ)*(lead*TerminalScale.scale j exponent)+copies/(2^j)^saving) :
    PhysicalReset.instructionWords ((v).jointPhase base₀ u.earlier w).program ((v).jointPhase base₀ u.earlier w).ticks*w ≤
      H₀*h*(lead*TerminalScale.scale S.height exponent)+
        H₀*(S.groupCount i*S.radix)*(lead*TerminalScale.scale S.height exponent)+S.initialSites/(2^S.height)^saving := by
  have amount := selected_peer_volume rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io floor u radix live rootRoom
  exact selected_mask_invoice_of_volume rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old
    io floor _ _ localRate receiver ratio saving lead exponent baseGroups radix live localRoom rootRoom jobs oldDegree shapes
    growth blocks low units age ambient word quote amount

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
