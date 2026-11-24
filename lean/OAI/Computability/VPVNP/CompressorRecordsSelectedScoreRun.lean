import OAI.Computability.VPVNP.CompressorRecordsSelectedScore
import OAI.Computability.VPVNP.CompressorRecordTermScores

/-!
# Native selection of the actual shrinking layout

The two accumulators and the level's chosen-layout cell lie in the allocated
workspace. Each of eight coordinate passes visits the selected term rows in
motif order and reads the payload and repetition words directly.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SelectedScore

open Compression BurstRAM PairSimulation.LocalHistory ShrinkMotif TermScores
open scoped Fin.CommRing Classical

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {a g w : ℕ} (X : State a (packingLaneBits a g))

/-- The coordinate number, layout side, and integer weight used by one of the eight
score-accumulation passes. -/
def axes (j : Fin 8) : Axis w :=
  let e := supplyOrder.entries j
  ⟨TermScores.word j.val, e.1, TermScores.word (MotifAdmission.weight relativeMass e.2)⟩

theorem axes_side (j : Fin 2 × Fin 4) :
    (axes (w := w) (finProdFinEquiv j)).side = finTwoEquiv j.1 := by
  change ((finTwoEquiv.prodCongr (Equiv.refl _)) (finProdFinEquiv.symm (finProdFinEquiv j))).1 = _
  rw [Equiv.symm_apply_apply]; rfl

/-- Address of the term record for a motif at the given position in the physical score scan. -/
def headAt (L : Tables w) (i : Fin (motifOrder X).length) := rowBase L (TermScores.word i.val)

theorem total_score (L : Tables w) (m : Memory w)
    (hstride : 10 ≤ L.termStride.val)
    (hterm : L.termBase.val + (motifOrder X).length * L.termStride.val ≤ 2^w)
    (hc : 8 ≤ 2^w) (hw : ∀ t, MotifAdmission.weight relativeMass t < 2^w)
    (hs : L.selectorBits.val = B.shrink.selectorBits) (l : Bool) :
    total L m (motifOrder X).length (List.ofFn axes) l = score B X (headAt X L) m l := by
  rw [total_fin_axes L m _ axes axes_side]
  unfold score
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro i _
  let j := coordinate l t
  have hcoord : (axes (w := w) j).coordinate.val = j.val := Nat.mod_eq_of_lt (j.isLt.trans_le hc)
  have weight : (axes (w := w) j).weight.val = MotifAdmission.weight relativeMass t := by
    change (TermScores.word (w := w) (MotifAdmission.weight relativeMass (supplyOrder.entries j).2)).val = _
    rw [show supplyOrder.entries j = (l,t) from supplyCoordinate l t]
    exact Nat.mod_eq_of_lt (hw t)
  have room : L.termBase.val+i.val*L.termStride.val+2+j.val < 2^w := by
    have h := Nat.mul_le_mul_right L.termStride.val i.isLt
    rw [Nat.succ_mul] at h
    have := j.isLt
    omega
  have hr := repetitions_val L (i := i.val) (by omega)
  have hv := payload_val L (axes (w := w) j) (i := i.val) (hcoord ▸ room)
  have hb := rowBase_val L (i := i.val) (by omega)
  change (axes j).weight.val * supplyWidth L (axes j) m i.val ^ 2 = _
  rw [weight,supplyWidth,hr,hv,hcoord,hs]
  change _ = _ * ((m ((rowBase L (TermScores.word i.val)).val+2+j.val)).val +
    (m ((rowBase L (TermScores.word i.val)).val+1)).val * B.shrink.selectorBits)^2
  rw [hb]

/-- Run all eight native scans on the true selected term records. Read the chosen
layout in the resulting memory, with exact call/probe charges and the frame. -/
theorem run_selected (L : Tables w) (m : Memory w) (s : Selection B X)
    (stored : Stored B X s (headAt X L) m)
    (hstride : 10 ≤ L.termStride.val)
    (hterm : L.termBase.val + (motifOrder X).length * L.termStride.val ≤ 2^w)
    (hc : 8 ≤ 2^w) (hw : ∀ t, MotifAdmission.weight relativeMass t < 2^w)
    (hs : L.selectorBits.val = B.shrink.selectorBits)
    (layout : TermScores.Layout L (motifOrder X).length (List.ofFn axes))
    (fit : ∀ l, layoutScore relativeMass (X.packingData.termWidths B.shrink X.shrinkNumber X.packingWidth s) l < 2^w) :
    let n := (motifOrder X).length
    let chosen := X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth s
    ∃ rs, TermScores.run L n (List.ofFn axes) m = some rs ∧
      after m (eventLog rs) L.levelCell.val = (chosen.toNat : Word w) ∧
      endState (some 0) rs = some (chosen.toNat : Word w) ∧
      (∀ j, j ≠ L.levelCell.val → (∀ l, j ≠ (counter L l).val) → after m (eventLog rs) j = m j) ∧
      rs.length = 8*n+2 ∧ RAMBuckets.probeCount Report.probes rs = 32*n+5 := by
  let N := (motifOrder X).length
  let htot (l : Bool) := total_score B X L m hstride hterm hc hw hs l
  have valid (l : Bool) : total L m N (List.ofFn axes) l < 2^w := by
    rw [htot l, score_eq B X s _ _ stored]
    exact fit l
  obtain ⟨rs,hr,_,hcell,hframe,hstate,hcalls,hprobes⟩ := run_eight L N axes m layout valid
  have bit : (if total L m N (List.ofFn axes) true < total L m N (List.ofFn axes) false then
      (1 : Word w) else 0) =
      ((X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth s).toNat : Word w) := by
    rw [htot true,htot false, ← chosenLayout_eq B X s _ _ stored]
    by_cases hlt : score B X (headAt X L) m true < score B X (headAt X L) m false <;> simp [hlt]
  exact ⟨rs,hr,hcell.trans bit,hstate.trans (congrArg some bit),hframe,hcalls,hprobes⟩

end CompressorRecords.SelectedScore

end VPVNP
end Computability
end OAI
