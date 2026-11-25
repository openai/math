import OAI.Hierarchy.DescentCensusPrecision

namespace OAI
/-! # Bit widths of the local Walsh census -/
namespace Hierarchy.DescentWalshPrecision

/-- u is the base-two upper exponent for the measured original entry. -/
def rate (m K : ℕ) := max (2+(m+7)/8) (2*Nat.clog 2 K)
def gainBits (m f K u : ℕ) := f+u+rate m K+1
def bits (m f K u : ℕ) := 3*m+2*u+gainBits m f K u+1

end Hierarchy.DescentWalshPrecision

namespace Hierarchy.DescentCompiler.AtomSchedule
open DescentWalshPrecision

def localWalshBits (S : AtomSchedule) (p m f K : ℕ) := bits m f K (S.censusBits p)

end Hierarchy.DescentCompiler.AtomSchedule

end OAI
