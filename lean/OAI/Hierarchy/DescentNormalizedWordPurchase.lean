import OAI.Hierarchy.DescentProfiledMachineWord
import OAI.Hierarchy.DescentNormalizedCalendarLive

namespace OAI
/-! # The same word and payload pay the calendar and its observation registers -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F) {n d:ℕ} (board:NonlinearExpanders.Graph n d) (op:RotorSpec)
    (t f g rate cut drift limit saving:ℕ) (branch:G.b≤2^(capRate G t g))

structure CalendarPurchase (head dates billed W τ β h:ℕ) : Prop where
  words : CalendarWord G board op t f g rate drift n d op.C limit head dates W τ β h
  grain : GrainRoom G t f g rate W τ β h
  invoice : NormalizedRuns G board op t f g rate cut drift limit branch billed W τ β h

include saving in
theorem normalized_word_purchase :
    ∃head dates billed least:ℕ,∀W≥least,∀_driftR _slots:ℕ,∃τ₀:ℕ,∀τ≥τ₀,∃β₀:ℕ,∀β≥β₀,∀ᶠh:ℕ in atTop,
      CalendarPurchase G board op t f g rate cut drift limit branch head dates billed W τ β h :=by
  obtain ⟨head,dates,first,offer⟩:=uniform_calendar_word G board op t f g rate drift n d op.C limit branch
  obtain ⟨second,billed,prices⟩:=normalized_calendar_live_at_ratio G board op t f g rate cut drift limit saving branch
  refine ⟨head,dates,billed,max first second,?_⟩
  intro W purchased _driftR _slots
  obtain ⟨ta,pre⟩:=offer W ((le_max_left ..).trans purchased) _driftR _slots
  obtain ⟨tb,rateAt⟩:=prices W ((le_max_right ..).trans purchased)
  refine ⟨max ta tb,?_⟩
  intro τ adequate
  obtain ⟨ba,heads⟩:=pre τ ((le_max_left ..).trans adequate)
  obtain ⟨bb,bills⟩:=rateAt τ ((le_max_right ..).trans adequate)
  refine ⟨max ba bb,?_⟩
  intro β divisor
  filter_upwards [heads β ((le_max_left ..).trans divisor),bills β ((le_max_right ..).trans divisor)]
    with h header calendar
  exact ⟨header,calendar.1,calendar.2⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
