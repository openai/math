import OAI.Computability.VPVNP.LiveVirtualPairCanonicalScan
import OAI.Computability.VPVNP.PairSimulationPhysicalScanData
import OAI.Computability.VPVNP.PairVertexRootPacket

/-!
# Root wire arguments of the canonical compressed occurrence

The flat bits selected in the native shared scan are grouped by the same
outgoing arcs as the canonical pair path. Both its incoming and outgoing
root fields therefore agree in the native DFS packet.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM PrivateRAM CursorBounds CursorNetwork Compression LabelEvaluator
open PairSimulation PairSimulation.LocalHistory NetworkKernel CutSchedule ExponentTrace
open private scanMachine capacity from OAI.Computability.VPVNP.LiveVirtualPairCanonicalScan

variable {K : Type*} [_root_.Field K] {S : BlockSchedule K} {D : FixedProgramDiagonal.Program}
  {B : S.Templates} {n C : ℕ} {hn : 2 ≤ n} {p : Nat.Primes}
  {M : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
  {data : D.ScalarData B hn M} {u : PairExponents B.growthConstant} {V : D.VirtualPairs B u hn C}
  [NeZero (virtualBits D.addressFactor n)]
  {ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower)} {i : D.groupIndices n} {μ : D.pairNom n C}
  (A : CanonicalScan data V ξ i μ)

local notation "W₀" => wordBits D.addressFactor n
local notation "sel" => V.selection (M := M)
local notation "linked" => FinalBits.template_linked (fun _ : Fin 1 => FinalBits.cursor W₀ 0 0)

/-- Reindex the canonical final-bit scan by the native shared worker's
complete assignment. -/
noncomputable abbrev CanonicalScan.sharedBits (z : (sel).Choices) :
    (A.arc z).Path ≃ (Fin ((sel).finalState z).totalWidth → Bool) :=
  PhysicalScanData.assignment ((sel).finalState z) (scanMachine W₀) Fin.castSucc (Function.Embedding.refl _)
    0 10 linked rfl 0 rfl (fun _ => 0) 0 (capacity A z)

theorem CanonicalScan.rootHalf (z : (sel).Choices) (x : TerminalData (A.arc z) (A.sites z))
    (v : ((sel).finalState z).network.Site) :
    let Y := (sel).finalState z
    TerminalGatherGeometry.half Y (fun j => A.sharedBits z x.arcs (Fin.cast (TerminalPrefix.width_sum Y) j)) v =
      WireTensor.edgeAssignment Y.network.src Y.network.dst ((A.arc z).payload x.arcs) v := by
  intro Y
  have payload := PhysicalScanData.payload Y (scanMachine W₀) Fin.castSucc (Function.Embedding.refl _)
    0 10 linked rfl 0 rfl (fun _ => 0) 0 (capacity A z) x.arcs
  exact congrArg (fun f => WireTensor.edgeAssignment Y.network.src Y.network.dst f v) payload.symm

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
