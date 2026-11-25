import OAI.Computability.BorderVNP.DiagonalBootedGeometryReturn

/-! # The full native startup on the input tape used by the public header decoder -/

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

private theorem return_on_mac {width : ℕ} {c : Code} {input : Arg → Word width} {s : RoutingISA.Bank width}
    {m : Memory width} {m₀ m₁ : TeamOpcode.Macros width 8} (h : m₀=m₁) (r : Returns c input m₀ s m) :
    ∃ out : Returns c input m₁ s m, out.val=r.val := by
  subst m₁
  exact ⟨r,rfl⟩

/-- Restore the full installed startup on the original public processor tape.
The tape is fixed before any of the three scratch base addresses are used. -/
theorem BootedPinStart.fullNativeGeometryReturnAt (ib hb sb : ℕ) (g : Fin (L).guessWidth → Bool)
    (geo : Returns GeometryAdvice.reconstruct (pub u) installed (B.pins g).val.2.1 (B.pins g).val.2.2) :
    ∃ run : Returns (withStartup pinGeometry) (pub u) mac (regs u)
      (processorMemory (G.processorFields u live wire ib hb sb) w), run.val.2=geo.val.2 := by
  obtain ⟨run,same⟩ := B.fullGeometryReturn g geo
  obtain ⟨out,eqn⟩ := return_on_mac (siteLibrary_installed gen n).symm run
  exact ⟨out,(congrArg Prod.snd eqn).trans same⟩

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
