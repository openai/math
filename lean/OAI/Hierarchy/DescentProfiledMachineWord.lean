import OAI.Hierarchy.DescentNormalizedSeedEntry
import OAI.Hierarchy.DescentProfiledUniformRates
import OAI.Hierarchy.DescentProfiledObservationScalars

namespace OAI
/-! # Simultaneous machine-word purchase for the initial state and dated RAM -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentDatedSeedStartup Chronology.RegisterTimeline Filter
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F) {n d:ℕ} (board:NonlinearExpanders.Graph n d) (op:RotorSpec)
    (t f g rate drift n₀ degree C limit:ℕ)

structure CalendarWord (head dates W τ β h:ℕ) : Prop where
  seed : NormalizedEntry G board op t f g rate drift n₀ degree C head τ β h
  steps : ProfiledRate.Covers G board op t f g rate τ drift limit β h dates
  seedFits : head*h<W*h
  datesFit : (t+1+max dates head+2)*h≤W*h
  observations : ∀M:ℕ,M≤(2^h)^2→∀w,W*h≤w→
    let J:=Nat.log 2 h/(2*β)
    ObservationRoom G (stageNumbers G t J f g rate M (tail τ J)) h w

/-- The factor can be increased to cover the terminal replay. The same choice
still works for every event and all original circuit and profile inputs. -/
theorem uniform_calendar_word (branch : G.b≤2^(capRate G t g)) :
    ∃head dates least:ℕ,∀W,least≤W→∀_driftR _slots:ℕ,∃τ₀:ℕ,∀τ≥τ₀,∃β₀:ℕ,∀β≥β₀,
      ∀ᶠh:ℕ in atTop,CalendarWord G board op t f g rate drift n₀ degree C limit head dates W τ β h:=by
  obtain ⟨head,seedBound,entry⟩:=normalized_seed_entry G board op t f g rate drift n₀ degree C branch
  obtain ⟨dates,posted⟩:=ProfiledRate.uniform_addresses G board op t f g rate drift limit
  obtain ⟨obs,observed⟩:=observation_room_uniform G t f g rate
  let least:=max obs (t+1+max dates head+2)
  refine ⟨head,dates,least,?_⟩
  intro W width _driftR _slots
  refine ⟨max 1 (2*localSocketRate G t g),?_⟩
  intro τ tailOK
  let turn:=ProfiledRate.threshold G board op t f g rate τ drift _driftR limit _slots
  refine ⟨max 1 (max (seedBound τ) turn),?_⟩
  intro β chosen
  have large : seedBound τ≤β:=by omega
  have avail : turn≤β:=by omega
  filter_upwards [entry τ β tailOK large,posted _driftR _slots τ β avail,observed τ β (by omega),
    eventually_ge_atTop 1] with h first schedule sees pos
  have clock : t+1+max dates head+2≤W:=(le_max_right obs _).trans width
  have observation : obs≤W:=(le_max_left obs _).trans width
  refine ⟨first,schedule,Nat.mul_lt_mul_of_pos_right (by omega) pos,
    Nat.mul_le_mul_right _ clock,?_⟩
  intro M smaller w fit
  exact sees M smaller w ((Nat.mul_le_mul_right h observation).trans fit)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
