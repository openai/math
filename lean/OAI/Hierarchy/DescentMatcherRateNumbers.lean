import Mathlib.Data.Nat.Basic

namespace OAI
/-! # Numerical coefficients shared by the literal chooser, host preparation and matcher -/

namespace Hierarchy.DescentColonies.PackedWinnerRAM
def work (k : ℕ) := 1+(2^k-1)*(6+(1+2^(k+1)*(6+12+2))+2)

end Hierarchy.DescentColonies.PackedWinnerRAM

namespace Hierarchy.DescentPackedColony.Phase.Menu
def pages (k : ℕ) := 1+2^(k+1)+2*(2^k-1)

end Hierarchy.DescentPackedColony.Phase.Menu

namespace Hierarchy.DescentPackedColony.Phase.Arena
def sharedTables (k Δ : ℕ) := (2^k-1)*(Δ+3+4*k)+Menu.pages k+2^k*((2^k-1)*2^(k+1))

end Hierarchy.DescentPackedColony.Phase.Arena

namespace Hierarchy.DescentPacking.PackedMatch.Local
def fields (r D p : ℕ) := r+(r*p+D*r)

end Hierarchy.DescentPacking.PackedMatch.Local

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census
def columns (r cap : ℕ) := r*(1+(1+2*cap))

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census

namespace Hierarchy.DescentPackedColony.Phase
open DescentColonies
def factor (k Δ : ℕ) :=
  let q:=2^k-1
  4+q*(4+k*(8+2*(25+56*Δ)))+200*(q+1)+(8+2*(1+33*q))+
    200*(2^(k+1)+1)+(4+2^k*(8+2*PackedWinnerRAM.work k))

end Hierarchy.DescentPackedColony.Phase

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony
/-- The multiplier depends only on the public number of blocks, the degree, the
signed cable quota and the number of dyadic keys. -/
def ordinaryFactor (k D cap K : ℕ) :=
  let r:=(2:ℕ)^k
  let f:=fields r D (2*cap)
  let pages:=(1+f)+(K+6)
  let blocks:=r+r*(2*cap)
  96+Phase.factor k D + (8+20*D) + 10*(r+2+pages) + 10*(2+K) +
    (8+D*(200*(D+1)^3+4)+4*blocks) + 54*blocks + (432+4*K) + K*(668+112*f)

end Hierarchy.DescentPacking.PackedMatch.Local.Stage

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census
def multiplier (k D cap K work : ℕ) :=
  let N:=columns (2^k) cap
  12+10*N+(26+2*N*(work+6))+ordinaryFactor k D cap K

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill
open DescentPackedColony
def extraFactor (k D K : ℕ) := 200+20*Phase.Arena.sharedTables k D+134*K+10*2^k

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepared
/-- The coefficient is polynomial in the old block count, signed cable cap, host
degree and number of chart keys. -/
def namesPerWord (k D cap K : ℕ) :=
  let n := fields (2^k) D (2*cap)
  15*(4+2^k+2*D) + (26+400*(D+1)^3+(2^k+2^k*(2*cap))*111) +
    (15*(((1+n)+(K+6))+1+K+1)+15+K*(11+4*(14+n*56))+472+411*(K+1))

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepared

end OAI
