import OAI.Computability.VPVNP.LiveHeaderFieldState

/-!
# Padding in the unit branch of the field program

For either incident cut the unit descriptor checks the bits following the mode.
At an endpoint the descriptor uses the missing shape and checks an empty interval.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram.Fields

open LiveHeaderSchedule LiveHeaderDescriptors LiveHeader ChainAssignments

theorem interval_unit_padding (s : Sizes) (g : Fin (2^(s.h+1))) (side : Side) :
    interval s g .unit side .padding =
      span .unit (incidentWidth (Δ := s.delta) side g) s.delta s.e s.config .padding := by
  unfold interval
  by_cases empty : incidentWidth (Δ := s.delta) side g = 0
  · rw [empty]
    rfl
  · simp [shape, empty, Mode.Tag.code]

theorem validPadding_unit_iff (s : Sizes) (cuts : AllCuts s.h s.delta)
    (g : Fin (2^(s.h+1))) :
    (∀ side, ValidPadding s cuts g .unit side) ↔ unitPads cuts g s.e s.config := by
  simp only [ValidPadding, unitPads, interval_unit_padding]

end LiveHeaderProgram.Fields

end VPVNP
end Computability
end OAI
