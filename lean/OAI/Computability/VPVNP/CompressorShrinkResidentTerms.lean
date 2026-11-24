import OAI.Computability.VPVNP.CompressorShrinkOutputAllocation
import OAI.Computability.VPVNP.CompressorRecordsSelectedFinish

/-! # The selected shrinking rows in the allocated output pass

The post-selection readback uses the cardinal-length motif order. The
split worker uses the state numbering of the same ordered motifs. Their
ten-word rows and all eight supply coordinates coincide.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkOutput

open Compression Compression.PackingData Compression.ShrinkMotif MotifBlocks MotifGrid MotifConversion
open BurstRAM ShrinkSliceSweep
open scoped Classical

variable {a b g w : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k}
variable (B : S.Templates) (X : State a (packingLaneBits a g))
variable (term stride selectors : Word w) (role retained : ℕ)

set_option maxHeartbeats 1200000 in
theorem resident_terms (sel : SelectedScore.Selection B X) (mem : Memory w)
    (hs : SelectedScore.Stored B X sel (SelectedScore.headAt X (SelectedArena.scoreTables X term stride selectors)) mem) :
    let T := splitBank (b := b) X B.shrink sel term stride.val role retained
    Terms X.packingData X.shrinkNumber (Shrink.packedIndex X.baseIndex) T B.shrink X.packingWidth sel mem := by
  intro T i
  let m := (ShrinkMotifOrder.stateNumber X).symm i
  let j := (SelectedScore.motifOrder X).entries.symm m
  have hj : j.val = i.val := (ShrinkMotifOrder.entries_ordinal X m).trans (congrArg Fin.val ((ShrinkMotifOrder.stateNumber X).apply_symm_apply i))
  have h := hs j
  change TermRecordScan.Fields _ _ _ _ (sel ((SelectedScore.motifOrder X).entries j)).val _ _ at h
  rw [show (SelectedScore.motifOrder X).entries j = m from (SelectedScore.motifOrder X).entries.apply_symm_apply _] at h
  have addr : SelectedScore.headAt X (SelectedArena.scoreTables X term stride selectors) j = Fin.ofNat (2^w) (term.val+i.val*stride.val) := by
    apply Fin.ext
    simp only [SelectedScore.headAt, TermScores.rowBase, TermScores.word, SelectedArena.scoreTables, Fin.val_add, Fin.val_mul, Fin.val_ofNat, hj]
    simp [Nat.add_mod, Nat.mul_mod]
  rw [addr] at h
  exact h

end CompressorRecords.ShrinkOutput

end

end VPVNP
end Computability
end OAI
