import OAI.Hierarchy.DescentMeasuredResetLaneNumbers
import OAI.Hierarchy.DescentResetActorWordCalibration
import OAI.Hierarchy.DescentSnapshotEstimatorLimits

namespace OAI
/-! # Simultaneous scalar room for every selected reset in the original schedule -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentPackedWalsh Filter
noncomputable section
set_option quotPrecheck false

/-- The low subcube, the Walsh arena, and the return register use the same word. -/
structure SnapshotWordRoom (S : AtomSchedule) (n d k tail p f g payload w : ℕ) : Prop where
  actor : ResetActorWords d (atRound S.rounds) n k f g w
  lanes : ∀i≤S.length, let dim:=S.groupWidth k tail i+k
    k≤laneBits dim payload (S.localWalshBits p dim f (quota S.rounds))
  estimator : ∀i≤S.length, let dim:=S.groupWidth k tail i+k
    ResetEstimatorWords (S.hostSize i) dim (S.localWalshBits p dim f (quota S.rounds))
      (S.censusBits p) (atRound S.rounds) w

variable {F : Type} [Field F] (G : PoweredGadget F)
theorem profiled_snapshot_word_room (t f g reset τ B n d : ℕ) (den : 0<B)
    (cutoff : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)≤B) :
    ∀ᶠ h:ℕ in atTop, ∀M p w, M≤2^(2*h)→p≤h→9*h≤w→
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      SnapshotWordRoom S n d k (tail τ J) p f g h w :=by
  filter_upwards [reset_actor_words G t f g reset n d B den,
    measured_lane_room G t f g reset τ B (quota t) cutoff,
    reset_estimator_words G t f g reset τ B (atRound t)] with h actor lanes score
  intro M p w sites inputSize bus
  dsimp only
  exact ⟨actor w (by omega),fun i hi=>lanes M i p hi inputSize,
    fun i hi=>score M p i (atRound t) w sites inputSize hi le_rfl bus⟩

end
end Hierarchy.DescentSixParty

end OAI
