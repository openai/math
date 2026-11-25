import OAI.Hierarchy.DescentSeedOperandLanePositive
import OAI.Hierarchy.DescentTerminalCubicRecordBits
import OAI.Hierarchy.DescentNormalizedWordPurchase
import OAI.Hierarchy.DescentNamedEarnedCensusRate
import OAI.Hierarchy.DescentNormalizedPreflightWitness
import OAI.Hierarchy.DescentNormalizedLastLookup
import OAI.Hierarchy.DescentOriginalRoleTableRoom

namespace OAI
/-! # A single machine-word ratio for the original seed, all dates, replay and final census -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentDatedSeedStartup DescentDatedAddressBook
open DescentDatedAddressBook.PhysicalReset Chronology.RegisterTimeline Filter
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F) {n d:ℕ} (board:NonlinearExpanders.Graph n d) (op:RotorSpec)
    (t f g rate cut drift limit:ℕ) (branch:G.b≤2^(capRate G t g))

def censusThreshold (τ:ℕ) :=
  max (seedCutoff G t f g rate τ)
    (max (2*bookRate G t f g rate τ) (2*(6*PreflightCalendar.fieldExponent G t f g rate τ+11)))

theorem census_cut_at (τ β:ℕ) (tail:2*localSocketRate G t g≤τ) (divisor:censusThreshold G t f g rate τ≤β) :
    CensusCut G t f g rate τ β :=by
  unfold censusThreshold seedCutoff at divisor
  constructor <;> dsimp only [groupRate] at * <;> omega

structure OriginalWord (head dates billed last W τ β h driftR slots:ℕ) : Prop where
  calendar : CalendarPurchase G board op t f g rate cut drift limit branch head dates billed W τ β h
  pitches : PitchCalendar.Purchased G board op t f g rate drift driftR limit slots W τ β h
  receiver : ReceiverCalendar G board op t f g rate τ drift limit β h
  roleTables : RoleWordsAt G op t f g rate τ β drift h
  started : 0<Nat.log 2 h/(2*β)
  lookup : LastSliceAt G board op t f g rate τ drift limit β h
  census : CensusWordAt G t f g rate τ β n d op.C op drift (t+1+max dates head+2) last h
  finalFits : (2*last+7)*h≤W*h
  cubicRecords : ∀M tail k drift₀ degree p,degree≤limit →
    let S:=stageNumbers G t (Nat.log 2 h/(2*β)) f g rate M tail
    DescentOperandWidth.recordBits G S k tail drift₀ degree p=
      DescentOperandWidth.recordBits G S k tail drift₀ 3 p
  seedOperandLanes : SeedOperandLanesAt G t f g rate drift limit τ β h

/-- The payload threshold can depend on the terminal tuning. The width multiplier
is fixed before either tuning, the circuit, the ballot and all runtime memories. -/
theorem original_machine_above_ratio (saving:ℕ) :
    ∃lower head dates billed last:ℕ,∀W≥lower,∀driftR slots:ℕ,∃τ₀:ℕ,∀τ≥τ₀,∃β₀:ℕ,∀β≥β₀,∀ᶠh:ℕ in atTop,
      OriginalWord G board op t f g rate cut drift limit branch head dates billed last W τ β h driftR slots:=by
  obtain ⟨head,dates,billed,least,book⟩:=normalized_word_purchase G board op t f g rate cut drift limit saving branch
  obtain ⟨last,earned⟩:=earned_census_rate G t f g rate n d op.C op drift (t+1+max dates head+2) branch
  refine ⟨max least (2*last+7),head,dates,billed,last,?_⟩
  intro W enough driftR slots
  have paidWord : least≤W:=(le_max_left ..).trans enough
  have paidLast : 2*last+7≤W:=(le_max_right ..).trans enough
  obtain ⟨startTail,calendar⟩:=book W paidWord driftR slots
  refine ⟨max 1 (max startTail (2*localSocketRate G t g)),?_⟩
  intro τ bought
  obtain ⟨startBus,scheduled⟩:=calendar τ (by omega)
  let pitch:=PitchCalendar.threshold G board op t f g rate drift driftR limit slots τ
  let receiverRate:=ResetOutput.receiverRate G board op t f g rate (atRound t)
  let digits:=1+operandExponent G (stageNumbers G t 0 f g rate 0 0)
  let decoder:=max (2*(τ+(receiverRate+digits))) (2*(τ+groupRate G t f g rate+receiverRate))
  refine ⟨max decoder (max pitch (max startBus (censusThreshold G t f g rate τ))),?_⟩
  intro β tall
  have settled:=census_cut_at G t f g rate τ β (by omega) (by omega)
  have paid : pitch≤β:=by omega
  have lastLookup:=original_last_lookup_cofinal G board op t f g rate τ drift limit β branch
    (by have:=settled.large;omega) (show 2*(τ+(receiverRate+digits))≤β by dsimp only [decoder] at tall;omega)
    (show 2*(τ+groupRate G t f g rate+receiverRate)≤β by dsimp only [decoder] at tall;omega)
  have roles:=original_role_words G op t f g rate τ β drift branch (by have:=settled.large;omega) settled.cohorts
  filter_upwards [scheduled β (by omega),earned τ β settled,lastLookup,roles,age_room β (by have:=settled.large;omega),
    PitchCalendar.eventually_purchased G board op t f g rate drift driftR limit slots W τ β (by omega) paid,
    paid_receiver_calendar G board op t f g rate τ drift driftR limit slots β paid,
    DescentOperandWidth.eventually_cubic_records G t f g rate β limit (by have:=settled.large;omega),
    seed_operand_lane_positive G t f g rate drift limit τ β (by have:=settled.large;omega)]
    with h stage readout decoded role age lanes recv cubic seedLanes
  exact ⟨stage,lanes,recv,role,age.1,decoded,readout,Nat.mul_le_mul_right h paidLast,cubic,seedLanes⟩

theorem original_machine_ratio (saving:ℕ) :
    ∃W head dates billed last:ℕ,∀driftR slots:ℕ,∃τ₀:ℕ,∀τ≥τ₀,∃β₀:ℕ,∀β≥β₀,∀ᶠh:ℕ in atTop,
      OriginalWord G board op t f g rate cut drift limit branch head dates billed last W τ β h driftR slots:=by
  obtain ⟨lower,head,dates,billed,last,allWidths⟩:=
    original_machine_above_ratio G board op t f g rate cut drift limit branch saving
  exact ⟨lower,head,dates,billed,last,allWidths lower le_rfl⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
