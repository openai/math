import OAI.Computability.VPVNP.LiveVirtualPairOccurrence

/-! # The native copy stage in the paper's pair coordinates -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork LabelEvaluator BurstRAM LiveProgram LocalCount
open PairStages PairStages.Group PairStages.Group.Auxiliary ExponentTrace CutSchedule

open private headers_cast from OAI.Computability.VPVNP.LiveVirtualPairOccurrence

variable {D : FixedProgramDiagonal.Program} {n : ℕ}
    {ht : 21 ≤ 2 ^ (D.geometry n).w} {hc : 44 ≤ n ^ 10000}
    {K : Type*} [Field K] {S : BlockSchedule K} {B : S.Templates} {hn : 2 ≤ n} {p : Nat.Primes}
    {M : Model p (B.compressorDegree n) (B.compressorEquations hn D.constants.circuitExponent)}
    (data : D.ScalarData B hn M)
    (W : Conditions (D.executionGroup n ht hc) (2 ^ (D.geometry n).d) (D.geometry n).H)
    (P : PairStageConditions (D.executionGroup n ht hc) (2 ^ (D.geometry n).d) (D.geometry n).H)
    (hg : D.constants.motifLabels = Fintype.card B.Entry)
    (cut : 1 + B.denseCount n D.constants.circuitExponent * D.counterWidth n ≤
      n ^ D.constants.deltaPower)
    (I : VirtualPairs.PhysicalInput data W P rfl hg cut)

/-- The checked physical branch gives the paper-indexed prepared branch with exactly
the same copy-stage output memory. -/
theorem VirtualPairs.paperPreparedInput :
    let G := D.executionGroup n ht hc
    let i := VirtualPairs.modelIndex data W P rfl hg cut I
    let ξ := VirtualPairs.exterior data W P rfl hg cut I
    let N := Nominations.indexed G I.nominationFits (memory I.trace) I.trace.tag
    ∃ prepared : PreparedBranch G (memory I.trace) (physicalPairIndex i)
      ((physicalPairLengths (ht := ht) (hf := hc) i).symm ▸ PairedChain.headers data.advice ξ i)
      N I.μ,
      prepared.copy.memory () = I.branch.copy.memory () := by
  let i := VirtualPairs.modelIndex data W P rfl hg cut I
  let ξ := VirtualPairs.exterior data W P rfl hg cut I
  let hdr : PrimedInputRAM.Header (D.pairLengths i) → Bool := PairedChain.headers data.advice ξ i
  have eq := headers_cast heights deltas adviceSizes data.advice I.exterior I.i
    (physicalPairLengths (ht := ht) (hf := hc) i)
  change ((physicalPairLengths (ht := ht) (hf := hc) i).symm ▸ hdr) =
    PairedChain.headers (cast (congrArg Bits adviceSizes) data.advice) I.exterior I.i at eq
  dsimp only
  rw [eq]
  exact ⟨I.branch, rfl⟩

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
