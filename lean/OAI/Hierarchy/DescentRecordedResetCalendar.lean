import OAI.Hierarchy.DescentRecordedResetFromChips
import OAI.Hierarchy.DescentIssuedChronology

namespace OAI
/-! # A single physical prefix program and clock for every history at one reset date -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup
open DescentPackedWalsh DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure

noncomputable def resetPrefix (E : EstimatorArena) (HP D k R cap M short floor f K grain w : ℕ)
    (addr : ℕ→ℕ→Bank) (roster src count : Bank) : Procedure w :=
  let tokens : Tokens k (2*cap):=fun t=>addr t.1.val t.2.val
  let C:=core tokens roster HP D E.high E.low E.precision short M floor f (grain*cap) K grain
  let P:=plan tokens roster HP D E.high E.low E.precision short M floor f (grain*cap) K grain
  let low:=prep tokens roster HP D E.high E.low E.precision short M floor f (grain*cap) K grain src R w
  (low.seq (P.prepare C count k D R M w E.start)).seq ((E.header (w:=w)).program.seq (E.cpu w))

noncomputable def resetTicks (E : EstimatorArena) (HP D k R cap M short floor f K grain w : ℕ)
    (addr : ℕ→ℕ→Bank) (roster : Bank) :=
  let tokens : Tokens k (2*cap):=fun t=>addr t.1.val t.2.val
  let C:=core tokens roster HP D E.high E.low E.precision short M floor f (grain*cap) K grain
  let P:=plan tokens roster HP D E.high E.low E.precision short M floor f (grain*cap) K grain
  ticks HP D E.high E.low E.precision short M floor f (grain*cap) K k R+P.prepareTicks C k D R M w+
    (4+10*(E.staticEnd-E.origin)+E.clock)

end Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup

namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentPackedWalsh DescentSIMDLookup PackedFlow.Canvas ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {W X Y : MarkedWorld F d P bits} {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist z₀ D₀ n z₁ D₁ : ℕ}
  {first : Reached X G q ε S k 0 z₀ D₀ wire hist} {input : Reached W G q ε S k i z D wire hist}
  {last : Reached Y G q ε S k n z₁ D₁ wire hist}
local notation "A" => input.placement
local notation "HP" => S.hostSize i
local notation "R" => S.groupCount i
local notation "K" => quota S.rounds

/-- The same literal raster addresses and public captured schedule generate the program on every
choice. The count, roster, old chips and all evolving census words remain RAM inputs. -/
theorem Path.reset_prefix (pre : Path first input) (post : Path input last)
    (calendar : List ℕ) (issued : (pre.append post).capFactors=calendar) (base : first.placement.cap=256)
    (p : ℕ) (gr : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (E : EstimatorArena) (M short floor f w : ℕ) (addr : ℕ→ℕ→Bank) (roster src count : Bank) :
    let grain:=(A).wire*((A).z*G.b)
    let fixedGrain:=S.epochPower^S.priceExponent*(S.grainAt G.b p (i+1)*G.b)
    let cap:=(calendar.take i).prod*256
    let tokens : Setup.Tokens k (2*(A).cap):=fun t=>addr t.1.val t.2.val
    let C:=Setup.core tokens roster HP D E.high E.low E.precision short M floor f (grain*(A).cap) K grain
    let P:=Setup.plan tokens roster HP D E.high E.low E.precision short M floor f (grain*(A).cap) K grain
    let lower:=Setup.prep tokens roster HP D E.high E.low E.precision short M floor f (grain*(A).cap) K grain src R w
    ((lower.seq (P.prepare C count k (A).degree R M w E.start)).seq ((E.header (w:=w)).program.seq (E.cpu w)))=
      Setup.resetPrefix E HP D k R cap M short floor f K fixedGrain w addr roster src count ∧
    Setup.ticks HP D E.high E.low E.precision short M floor f (grain*(A).cap) K k R+
      P.prepareTicks C k (A).degree R M w+(4+10*(E.staticEnd-E.origin)+E.clock)=
      Setup.resetTicks E HP D k R cap M short floor f K fixedGrain w addr roster := by
  have capacity : (A).cap=(calendar.take i).prod*256:=by
    simpa only [Nat.sub_zero,base] using pre.capacity_prefix post calendar issued
  dsimp only
  simp only [input.branch]
  let liveGrain := (A).wire*((A).z*G.b)
  let fixedGrain := S.epochPower^S.priceExponent*(S.grainAt G.b p (i+1)*G.b)
  let runPrefix (cap grain : ℕ) := Setup.resetPrefix E HP D k R cap M short floor f K grain w addr roster src count
  let timePrefix (cap grain : ℕ) := Setup.resetTicks E HP D k R cap M short floor f K grain w addr roster
  change runPrefix (A).cap liveGrain = runPrefix ((calendar.take i).prod*256) fixedGrain ∧
    timePrefix (A).cap liveGrain = timePrefix ((calendar.take i).prod*256) fixedGrain
  have grain_eq : liveGrain = fixedGrain := by simp only [liveGrain,fixedGrain,input.edges,old,input.grain,gr]
  rw [capacity,grain_eq]
  exact ⟨rfl,rfl⟩

end
end Hierarchy.DescentSixParty.Chronology

end OAI
