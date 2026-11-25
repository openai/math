import OAI.Optimization.LinearProgramming.Compression.SymbolicResidentLayout
import OAI.Optimization.LinearProgramming.RAM.Footprint

/-! Resident numerical data common to first entry and repeated BitRAM callbacks. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM MinorProxyCache

/-- The current row's scalar window has no cell in common with a cached
magnitude, a grid numerator, or the denominator used by the offset kernel. -/
structure RowAwayFromCache (L : Buffers) (n base : ℕ) : Prop where
  magnitudes : base+(n+1)≤L.magBase ∨ L.magBase+n≤base
  numerators : base+(n+1)≤L.gridBase ∨ L.gridBase+n≤base
  scale : L.scalePtr<base ∨ base+(n+1)≤L.scalePtr

/-- All resident numerical data required before installing a newly decoded row. -/
structure ResidentNumeric {n : ℕ} (mag : ℕ → ℚ) (L : Buffers) (fuel prec C R base : ℕ)
    (P : ℚ → Prop) (old caller : Memory ℚ) : Prop where
  cache : StableCache caller L n fuel prec mag
  workspace : SymbolicQueryLayout caller n fuel
  reservation : SymbolicCacheReservation caller L n fuel
  rowPtr : caller.index 67=base
  apart : RowAwayFromCache L n base
  callerSafe : caller.AllData P
  nativeSafe : old.AllData P
  nativeBound : Footprint C (old.atPC 0)
  capacity : caller.index 60=C+1
  callerBound : ∀ i, caller.index i≤R

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
