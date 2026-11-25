import OAI.Computability.BorderVNP.DiagonalFrozenSignedTask

/-! # Scalar and directory parameters of the original selected source -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

/-- The five geometry directories that were serialized into the physical
signed-task parameters. -/
def Parameters.sourceDirectories (p : Parameters) : GeometryDirectories :=
  ⟨p.sorted,p.padded,p.stops,p.bundlePayload,p.bundleInverse⟩

end RoutingISA.SignedTaskArena

namespace Diagonal

open Branch Crossing Cover Packing ExternalSew PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open TeamScales Filter DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins VPVNP VPVNP.BurstRAM
open RoutingISA RoutingISA.SignedTaskArena RoutingISA.CubeArena TeamContraction TeamContraction.JointHeader
open TeamContraction.ProcessorSlots GeometryAdvice _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical
open scoped Classical BorderVNP.Epoch.Cube

set_option maxRecDepth 5000
set_option maxHeartbeats 1200000

variable {F K : Type} [Field F] [Field K] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m}
    {S : SiteSchedule G} {extra E dlog Q A B j : ℕ} (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} s (E+1) dlog Q A B j)

/-- Recovering the directory and counts from the deployed layout yields
the very physical parameters used by the canonical report source. -/
theorem JointSchedule.frozenSignedTask_sourceParameters (l size headerFactor : ℕ) (initial : StartupArena)
    (dir : Directory.Layout) (profile ceiling outputs field : ℕ) (dirs : GeometryDirectories) :
    let sa := b.frozenSignedTask cube (l+1) l size headerFactor initial dir profile ceiling outputs field dirs
    physicalParameters sa.cube sa.p.sourceDirectories (l+1) sa.p.report.bundles sa.p.report.marked
      (pairedTableParameters (l+1) size) (Nat.clog 2 (stretch b.ρ (l+1)*(2*l+1)+1))
      (Fintype.card (G.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width))
      (b.physical.word (l+1)) sa.p.siteWidth sa.p.bodyCap = sa.p := rfl

end Diagonal

end BorderVNP
end Computability
end OAI
