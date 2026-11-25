import Mathlib.Data.List.Basic

namespace OAI
/-! # The public order of ordinary and reset dates -/
namespace Hierarchy.DescentSixParty.Chronology
def kindPeriod (rounds : ℕ) := List.replicate rounds false ++ [true]
def kindCalendar (rounds count : ℕ) := (List.replicate count (kindPeriod rounds)).flatten
end Hierarchy.DescentSixParty.Chronology

end OAI
