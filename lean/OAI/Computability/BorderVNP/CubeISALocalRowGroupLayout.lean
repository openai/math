import OAI.Computability.BorderVNP.CubeISALocalRowBootMinimum
import OAI.Computability.BorderVNP.CubeGroupNativeCheckedRun

/-! # Public histogram and assignment arrays in the physical cube arena -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open BorderVNP.Cube BorderVNP.Cube.Tally

/-- Read the histogram on the physical product labels, incoming demands, and decoded dense rows. -/
def weightLayout (a : CubeArena.Layout) (frame axis : ℕ) : GroupWeights.Layout :=
  ⟨frame,a.header.header,a.header.d,a.n+1,axis,a.header.header+13+a.header.entries,
    a.header.volume a.n (selectorWidth a.n a.K a.h),a.groupWeights,a.cells,a.publicBase,
    a.demands,a.powerBase,a.alphabet,a.h*a.b,a.header.blocks⟩

/-- The group histogram, team totals, and ownership table share the length-only arena. -/
def teamLayout (a : CubeArena.Layout) (r : ℕ) : TeamNative.Layout :=
  ⟨r,a.header.d,a.groupWeights,a.teamTotals,a.ownerBase⟩

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
