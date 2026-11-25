import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Filled original word pitches at unequal CPU and payload widths -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSIMDLookup
/-- The original CPU can use a different bit width from the address-free
dictionary. Only their fixed linear ratio enters the short price. -/
theorem pitch_fill (payload unit word factor : ℕ) (positive : 0<unit) (room : 2*unit≤payload)
    (ratio : word≤factor*payload) :
    word≤lanes payload unit*(4*factor*unit) :=by
  have known:=(occupancy payload unit positive room).2
  calc
    word≤factor*payload :=ratio
    _≤factor*(4*lanes payload unit*unit) :=Nat.mul_le_mul_left _ known
    _=_ :=by ring

end Hierarchy.DescentDatedSeedStartup

end OAI
