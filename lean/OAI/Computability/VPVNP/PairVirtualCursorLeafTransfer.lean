import OAI.Computability.VPVNP.LiveVirtualPairCanonicalScan
import OAI.Computability.VPVNP.PairSimulationLeafArguments

/-! # Transferring physical cursor leaves to the virtual pair

The lane labels of the virtual scan include a cast from its address dimension
to the sum of its base and lane dimensions. Identifying these dimensions
transports the state together with the nomination parser on its network.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression BurstRAM CursorNetwork CursorRouting
open private scanInput from OAI.Computability.VPVNP.PairSimulationScanTrace

variable {d b l e w n a H s : ℕ} [NeZero d] [NeZero (b+l)]
    {L : PrimedInputRAM.Lengths} {Q : PrimedInputRAM.Layout L n a H w}
    (D : PrimedCounter.Data Q s) {k : Type*} [Field k] (S : BlockSchedule k)
    {R : Type*} [CommRing R] {Label : Type} [Fintype Label] (f : Label → R)
    (t : ℕ)

/-- The nomination clock holds at the split physical dimension. -/
theorem cursorLaneClock (split : d = b+l)
    (virtual : ProcessorBudget n d e w) (physical : ProcessorBudget n (b+l) e w)
    (vclock : NominationClock D virtual.tags virtual.capFits t) :
    NominationClock D physical.tags physical.capFits t := by
  subst d
  exact vclock

/-- Transfer a dependent property of the cursor state and its site parsers
from the physical coordinates to the lane labels of the scan. -/
theorem cursorLaneTransfer (split : d = b+l) (dim : 1 < d) (sum : 1 < b+l)
    (virtual : ProcessorBudget n d e w) (physical : ProcessorBudget n (b+l) e w)
    (vclock : NominationClock D virtual.tags virtual.capFits t)
    (pclock : NominationClock D physical.tags physical.capFits t)
    (G : (X : State (S.degreeExponent 0) l) → SiteParsers f X.network → Prop)
    (tested : G (LeafArguments.state sum (Nat.add_sub_of_le S.degree_bounds.1) (2^e) w)
      (nominationSites D physical.tags physical.capFits (cursorCoordinateLabels b l)
        sum (Nat.add_sub_of_le S.degree_bounds.1) f t pclock)) :
    G (scanInput ((finCongr split).trans (cursorCoordinateLabels b l)) dim S e w)
      (nominationSites D virtual.tags virtual.capFits ((finCongr split).trans (cursorCoordinateLabels b l))
        dim (Nat.add_sub_of_le S.degree_bounds.1) f t vclock) := by
  subst d
  exact tested

end PairSimulation.LocalHistory

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork CursorBounds LabelEvaluator BurstRAM CutSchedule ExponentTrace
open PairSimulation PairSimulation.LocalHistory NetworkKernel LiveProgram

variable {K : Type*} [Field K] {S : BlockSchedule K} {D : FixedProgramDiagonal.Program}
    {B : S.Templates} {n C : ℕ} {hn : 2 ≤ n} {p : Nat.Primes}
    {M : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
    {data : D.ScalarData B hn M} {u : PairExponents B.growthConstant} {V : D.VirtualPairs B u hn C}
    [NeZero (virtualBits D.addressFactor n)]
    {ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower)} {i : D.groupIndices n} {μ : D.pairNom n C}
    (A : CanonicalScan data V ξ i μ)

local notation "l" => reservedLanes B u n
local notation "b" => virtualBits D.addressFactor n - reservedLanes B u n
local notation "κ" => B.compressorValues hn M
local notation "e" => roundedUp 1 4 n
local notation "w" => CursorBounds.wordBits D.addressFactor n
local notation "sourceData" => V.data data.advice ξ i μ

include A in
/-- The canonical scan supplies the clock for the physical cursor parser. -/
theorem CanonicalScan.physicalCursorClock [NeZero (b+l)] (budget : ProcessorBudget n (b+l) e w) :
    NominationClock sourceData budget.tags budget.capFits (n^39) :=
  cursorLaneClock sourceData (n^39) (Nat.sub_add_cancel V.lanes).symm V.cap budget A.clock

/-- A property established on the physical leaves of the selected cursor
holds for the virtual pair's scan state and its canonical leaf readers. -/
theorem CanonicalScan.physicalCursorTransfer [NeZero (b+l)] (sum : 1 < b+l)
    (budget : ProcessorBudget n (b+l) e w)
    (clock : NominationClock sourceData budget.tags budget.capFits (n^39))
    (G : (X : State (S.degreeExponent 0) l) → SiteParsers κ X.network → Prop)
    (tested : G (LeafArguments.state sum (Nat.add_sub_of_le S.degree_bounds.1) (2^e) w)
      (nominationSites sourceData budget.tags budget.capFits (cursorCoordinateLabels b l) sum
        (Nat.add_sub_of_le S.degree_bounds.1) κ (n^39) clock)) :
    G V.scanState A.leafSites :=
  cursorLaneTransfer sourceData S κ (n^39) (Nat.sub_add_cancel V.lanes).symm V.dimension sum
    V.cap budget A.clock clock G tested

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
