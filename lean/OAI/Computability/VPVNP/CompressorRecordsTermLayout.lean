import OAI.Computability.VPVNP.CompressorShrinkTermPhases
import OAI.Computability.VPVNP.CompressorRecordsSelectedScoreRun

/-!
# Choosing the common layout after the native term scan

The width cells read by the score passes are the cells written by the fused term
worker on the very same admitted motif choices. A legal term stream therefore
determines one global layout, and the scratch for its score does not overwrite
any earlier term words.
-/

namespace OAI
namespace Computability
namespace VPVNP

set_option maxHeartbeats 1800000

namespace CompressorRecords.SelectedScore

open Compression BurstRAM PairSimulation.LocalHistory ShrinkMotif TermScores
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {a g w : ℕ} (X : State a (packingLaneBits a g))

private theorem motifNumber (i : Fin (Fintype.card X.packingData.Motif)) :
    (ShrinkMotifOrder.stateNumber X ((ShrinkMotifOrder.entries X) i)).val = i.val := by
  change ((ShrinkMotifOrder.entries X).symm ((ShrinkMotifOrder.entries X) i)).val = i.val
  exact congrArg (fun j : Fin (Fintype.card X.packingData.Motif) => j.val)
    ((ShrinkMotifOrder.entries X).symm_apply_apply i)

/-- All eight exact inputs to the score scan are physically present immediately after
the actual fused term execution. -/
theorem stored_of_term_run (L : Tables w) (dense : Word w) (cap : ℕ) (s : Selection B X)
    (before : Memory w) (reports : List (Report w))
    (term : ShrinkTermSelection.Written B.shrink X dense L.termBase L.termStride.val cap s before reports) :
    Stored B X s (headAt X L) (after before (eventLog reports)) := by
  intro i
  let m := (motifOrder X).entries i
  have he := term.fields m
  have hb : ShrinkTermSelection.rowBase X L.termBase L.termStride.val m = headAt X L i := by
    dsimp only [ShrinkTermSelection.rowBase,headAt,TermScores.rowBase,m]
    rw [show (ShrinkMotifOrder.stateNumber X ((motifOrder X).entries i)).val = i.val from motifNumber X i]
    change ((L.termBase.val + i.val * L.termStride.val : ℕ) : Word w) = L.termBase + (i.val : Word w)*L.termStride
    have ht : (L.termBase.val : Word w) = L.termBase := Fin.ext (Nat.mod_eq_of_lt L.termBase.isLt)
    have hs : (L.termStride.val : Word w) = L.termStride := Fin.ext (Nat.mod_eq_of_lt L.termStride.isLt)
    simp [ht,hs]
  rw [hb] at he
  exact he

/-- From the supplied physical demand pairs, every admitted sequence gives an actual
term scan followed by the deterministic eight-axis layout computation. -/
theorem choose_layout (L : Tables w) (dense : Word w) (mem : Memory w) (cap : ℕ)
    (hstride : 10 ≤ L.termStride.val)
    (separate : dense.val + (motifOrder X).length*2 ≤ L.termBase.val)
    (termFit : L.termBase.val + (motifOrder X).length * L.termStride.val < 2^w)
    (pairs : ShrinkTermInputs.statePairs X dense mem)
    (hw : ShrinkTermSelection.fitConstant B.shrink + 4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (hcap : TermWorker.budget B.shrink 2 8 w X.maxWireWidth ≤ cap)
    (hc : 8 ≤ 2^w) (hweights : ∀ t, MotifAdmission.weight relativeMass t < 2^w)
    (hselectors : L.selectorBits.val = B.shrink.selectorBits)
    (scratch : TermScores.Layout L (motifOrder X).length (List.ofFn axes))
    (s : Selection B X)
    (hscore : ∀ l, layoutScore relativeMass (X.packingData.termWidths B.shrink X.shrinkNumber X.packingWidth s) l < 2^w) :
    let n := (motifOrder X).length
    let chosen := X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth s
    ∃ terms scores, ShrinkTermSelection.Written B.shrink X dense L.termBase L.termStride.val cap s mem terms ∧
      TermScores.run L n (List.ofFn axes) (after mem (eventLog terms)) = some scores ∧
      after mem (eventLog (terms++scores)) L.levelCell.val = (chosen.toNat : Word w) ∧
      (∀ j, j ≠ L.levelCell.val → (∀ l, j ≠ (counter L l).val) →
        after mem (eventLog (terms++scores)) j = after mem (eventLog terms) j) ∧
      scores.length = 8*n+2 ∧ RAMBuckets.probeCount Report.probes scores = 32*n+5 := by
  obtain ⟨terms,ht⟩ := (ShrinkTermSelection.native B.shrink X dense L.termBase L.termStride.val
    hstride separate termFit mem pairs hw cap hcap).2 s
  let m := after mem (eventLog terms)
  obtain ⟨scores,hr,chosen,_,frame,count,probes⟩ := run_selected B X L m s
    (stored_of_term_run B X L dense cap s mem terms ht) hstride termFit.le hc hweights hselectors scratch hscore
  have hm : after mem (eventLog (terms++scores)) = after m (eventLog scores) := by
    simp only [eventLog, List.flatMap_append, after, List.foldl_append,m]
  exact ⟨terms,scores,ht,hr,hm ▸ chosen,hm ▸ frame,count,probes⟩

end CompressorRecords.SelectedScore

end VPVNP
end Computability
end OAI
