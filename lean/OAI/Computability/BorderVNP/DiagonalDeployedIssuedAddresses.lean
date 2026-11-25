import OAI.Computability.BorderVNP.DiagonalDeployedFrozenBoots

/-! # Native reference addresses on the installed signed task -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Branch Packing PackedHistoryCircuit VPVNP BurstRAM TeamContraction TeamContraction.ProcessorSlots
open RoutingISA RoutingISA.Pins RoutingISA.Transmission GeometryAdvice GeometryFrameEncoding
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins RoutingISA.Evaluator RoutingISA.CompactMachine
open RoutingISA.CellDispatch TeamSite
open scoped Classical

section Addresses

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {paid : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField paid aux q k s ord} {chart : AdvisedBranch C}
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E] {R r rw pinWidth : ℕ}
    (reader : ChosenReader chart (R+1) r rw rw rw pinWidth)

/-- Compute the actual reference and pin addresses once for a supplied
startup arena and signed task. The directory already carries the frozen
source counts and the gate stripe uses the actual reserved table size. -/
noncomputable def ChosenReader.deployedReferenceAddresses (area : StartupArena) (t : SignedTaskArena.Layout)
    (directory : Packing.Directory.Layout) (advice outside start profile gates outputs field : ℕ) :
    Fin (R+1) → UnitAddresses :=
  let origin := Allocation.dest start profile gates outputs field
  let route := routingExtension (signedBudgetWords rw outside) directory origin t.cube.cables t.cube.cells
  let stripe := GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount profile gates outputs field*rw) r
  fun u =>
    let placed := reader.frozenTaskPlacement t area u route
    let pinned := CubeHeaderInstall.pinFields placed.extension (Allocation.stop start profile gates outputs field rw)
      t.cube.header.d (t.cube.n+1) (t.cube.h*t.cube.b) t.cube.header.blocks profile
      (BorderVNP.Cube.Physical.declarationCap t.cube.n t.cube.header.d t.cube.header.blocks t.cube.b t.cube.h t.cube.s)
    let ext := Allocation.fields pinned start profile gates outputs field (area.literal/4) stripe
    area.unitAddresses advice (reader.packetAt (ReaderPlacement.inArena area placed.valuation placed.entry placed.totals ext))

end Addresses

end Diagonal

end BorderVNP
end Computability
end OAI
