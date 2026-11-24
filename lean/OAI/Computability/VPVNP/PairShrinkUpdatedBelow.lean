import OAI.Computability.VPVNP.PairShrinkPartyNative

/-!
# Retaining saved scratch below a shrinking job's staging area

The packet witness fixes the geometry of the row writes. Their destinations
and lengths apply to any saved scratch, even when its contents and stack
boundary differ from those of the witness.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM Compression Compression.ShrinkMotif MotifBlocks MotifGrid MotifConversion
open NodeArguments
open private Job.conditions from OAI.Computability.VPVNP.PairShrinkPartyNative

variable {a b g w packetEnd endAddr : ℕ} {δ factor : ℝ} {K : Type*} [_root_.Field K]
variable {X : State a (packingLaneBits a g)}
variable {F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
variable {ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ} {sel : X.ShrinkSelection F}
variable {m : X.packingData.Motif} {party : Fin 6} (J : Job X F ready sel m party w)

/-- Applying the job's writes to arbitrary saved scratch preserves each address below staging. -/
theorem Job.updated_below {baseline : Word w → Word w} (packets : J.Packets packetEnd baseline)
    (saved : DFS.Scratch w endAddr) (q : Word w) (below : q.val < J.scratch.staging) :
    rawScratch (J.updated endAddr saved) q = rawScratch saved q := by
  by_cases live : endAddr ≤ q.val
  · have kept := (ShrinkPartyColumns.memory J.scratch J.row J.scratch.staging
      (fun c i ↦ (Job.conditions J packets c i).2.1) (fun c i ↦ (Job.conditions J packets c i).2.2)
      (rawScratch saved)).2 q below
    simpa only [Job.updated, rawScratch, dite_eq_left live, DFS.scratch] using kept
  · simp only [rawScratch, dite_eq_right live]

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
