import OAI.Hierarchy.DescentDatedSeedInputText
import OAI.Hierarchy.DescentDatedSeedTariff

namespace OAI
/-! # Total original input and charged initialization before the first date -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open Catalyst DescentSeedRoot DescentColonies DescentSIMDLookup DescentPackedSeed DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F J A : Type} [Field F] [Fintype J] [DecidableEq J] {k p R d G H : ℕ}
    (X : Approximation F k p) (name : J≃Fin G) (digits : Fin R≃J×Block d) (host : Vertex X↪Fin H) (l : Layout) (w : ℕ)
local notation "M" => l.packedLanes

omit [Fintype J] [DecidableEq J] in
/-- The first term counts all real input cells, including the immutable
high exterior and chip banks. The next two terms are native ticks and the
seven-fold instruction charge before multiplication by machine word width. -/
theorem physical_bound (initialWords : ℕ) (initialBefore : initialWords≤ l.base)
    (verdictBefore : DescentPackedSeed.rows X R l.seedWidth w+1≤ l.base)
    (active : 0< chunks G l.operandLanes) :
    (initialWords+clock X l w H G d R+
      7*DescentStaticWordColumn.names (program (A:=A) X name digits host l w))*(w+1) ≤
        2700*(endAddress X l H G d+1)*(w+1) := by
  apply Nat.mul_le_mul_right
  have name:=program_names (A:=A) X name digits host l w
  have counted:=tariff X l H G d active
  have charged : DescentDatedSeedStartup.clock X l H G d=clockBound X l H G d := by
    unfold DescentDatedSeedStartup.clock operandClock clockBound
    rw [Signed.Plane.clock_eq]
  obtain ⟨s,m,t⟩:=fences X l H G d
  have limit:=s.trans (m.trans t)
  unfold clock
  rw [charged]
  omega

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
