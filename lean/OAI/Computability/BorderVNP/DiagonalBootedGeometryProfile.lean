import OAI.Computability.BorderVNP.DiagonalBootedGeometryReturn
import OAI.Computability.BorderVNP.PackedHistoryGeometryBranch

/-! # The actual full geometry return for a fixed booted private pin -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Pins
open RoutingISA.CompactMachine PackedHistoryCircuit DiagonalResidueRAM CellMacro.Generator BorderVNP.Cube.Tally

variable {R r t d link inner n w : ℕ} {Edge : Type} {gen : Fragment IO}
    {G : Wiring R r t d link inner n Edge} {pub : Fin (R+1) → Arg → Word w}
    {regs : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
    {live : Fin d → Bool} {wire : Exterior R r link → Bool} {u : Fin (R+1)}
    (B : BootedPinStart gen G pub regs args live wire u)
local notation3 (prettyPrint := false) "mac" => TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)
local notation3 (prettyPrint := false) "installed" => install gen n mac
local notation3 (prettyPrint := false) "L" => G.pinLayout u (args u).ibase (args u).hbase (args u).starbase
local notation3 (prettyPrint := false) "f" => G.transferFrame u (args u).header (args u).dst
local notation3 (prettyPrint := false) "F" => G.processorFields u live wire (args u).ibase (args u).hbase (args u).starbase
local notation3 (prettyPrint := false) "initial" => processorMemory F w

/-- The full return consumed by the frozen packet verifier uses this exact
private pin and reconstructs exactly this native register/memory pair. Its
clock, output row and saved data are read on that same trace. -/
theorem BootedPinStart.profileReturnAt {o time dest : ℕ} {ok : Prop} {words : Fin o → ℕ}
    {resident : (Fin (L).guessWidth → Bool) → Memory w → Prop}
    (paths : ProfilePaths (withStartup pinGeometry) (L).guessWidth (pub u) installed (regs u) initial ok
      time dest words resident) (g : Fin (L).guessWidth → Bool)
    (geo : Returns GeometryAdvice.reconstruct (pub u) installed (B.pins g).val.2.1 (B.pins g).val.2.2) :
    ∃ run : Returns (withStartup pinGeometry) (pub u) installed (regs u) initial,
      run.val.2=geo.val.2 ∧ run.val.1.flatMap TeamRAM.Event.choices=List.ofFn g ∧
      traceCost run.val.1=B.used+traceCost (B.pins g).val.1+traceCost geo.val.1 ∧
      traceCost run.val.1≤time ∧ signedWeight run.val.1=1 ∧ resident g geo.val.2.2 ∧
      ∀ i, readings geo.val.2.2 (dest+i.val)=words i := by
  obtain ⟨full,_⟩ := B.fullGeometryReturn g geo
  obtain ⟨choice,obs⟩ := paths.outputs (paths.passes.mp ⟨full⟩)
  have boot : Runs (pub u) installed JointHeader.bootHeader (regs u) initial B.trace B.out B.memory := by
    rw [←siteLibrary_installed gen n]
    exact B.boot
  obtain ⟨same,_,cost⟩ := profile_at_pin_return f boot B.stable B.positive B.pins
    (fun a => (B.outputs a).1) choice (fun a => (obs a).1) g geo
  have kept := paths.memory (choice g) g (obs g).1
  exact ⟨choice g,same,(obs g).1,cost,(obs g).2.1,(obs g).2.2.1,same ▸ kept,same ▸ (obs g).2.2.2⟩

/-- Read a proved property of all complete startup returns on the particular
physical geometry return. The same private digits still witness the profile's
resident input, even when the property depends on the returned registers. -/
theorem BootedPinStart.allReturns_on_pin {o time dest : ℕ} {ok : Prop} {words : Fin o → ℕ}
    {resident : (Fin (L).guessWidth → Bool) → Memory w → Prop}
    (paths : ProfilePaths (withStartup pinGeometry) (L).guessWidth (pub u) installed (regs u) initial ok
      time dest words resident) (Q : Bank w → Memory w → Prop)
    (every : ∀ run : Returns (withStartup pinGeometry) (pub u) installed (regs u) initial, Q run.val.2.1 run.val.2.2)
    (g : Fin (L).guessWidth → Bool)
    (geo : Returns GeometryAdvice.reconstruct (pub u) installed (B.pins g).val.2.1 (B.pins g).val.2.2) :
    Q geo.val.2.1 geo.val.2.2 ∧ resident g geo.val.2.2 ∧
      B.used+traceCost (B.pins g).val.1+traceCost geo.val.1≤time ∧
      ∀ i, readings geo.val.2.2 (dest+i.val)=words i := by
  obtain ⟨run,same,_,cost,clock,_,saved,read⟩ := B.profileReturnAt paths g geo
  exact ⟨same ▸ every run,saved,cost ▸ clock,read⟩

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
