import OAI.Computability.NearSquareRoot.PrecisionBatchPhaseRead
import OAI.Computability.NearSquareRoot.PrecisionGridInstruction
import OAI.Computability.NearSquareRoot.SynchronizedNumberedBits

/-! # Preparing a phase for an actual local descriptor and packed address -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Strip Staff Carry BoxFin SynchronizedBlocks ShortFourier ShortFourier.BatchWord

/-- The scalar physically selected at one local address of the indicated coprime-box block. -/
noncomputable def actualBlockPhase {k l : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k l box)
    (j : Fin (box.length/4)) (precision : ℕ) (z : SlotDescriptor) (x : BlockAddress (BoxAxis box) j) : ℂ :=
  letI := modulus_neZero hb
  let a u := BoxFin.modulus box (axis j u)
  let c u := padding box (axis j u)
  phaseAt a c (fun u => paddedLog (a u)) (blockSpectators hb j) (numberedBits hb j) precision z x

theorem actualBlockPhase_unit {k l : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k l box)
    (j : Fin (box.length/4)) (precision : ℕ) (z : SlotDescriptor) (x : BlockAddress (BoxAxis box) j) :
    ‖actualBlockPhase hb j precision z x‖ = 1 := by
  dsimp only [actualBlockPhase, phaseAt]
  split
  · split
    · unfold typedPhase phaseField
      split
      · exact placedCoefficient_unit ..
      · exact RoutedWalsh.table_norm ..
    · simp
  · simp

variable {I : Type} {s : Regime I} {k l precision : I → ℕ} {box : I → List (ℕ × ℕ)}
    (hb : ∀ i, BoxShape.Valid (k i) (l i) (box i))
    (header : s.Has (fun i => (box i).map (fun p => (tally p.1,tally p.2))))
    (j : ∀ i, Fin ((box i).length/4)) (J : Realizes s (fun i => (j i).val))

private theorem hasLength {u : I → Tally} (U : s.Has u) : Realizes s (fun i => (u i).length) := by
  simpa only [Realizes, Function.comp_def, Staff.box, recover_tally] using U

include hb header J in
private theorem count_realizes : Realizes s (fun i => count (j i)) := by
  have picks := (Regime.Has.pair (groupedRadices hb header) J).ez (Iter.facile ([] : List Tally))
  let row (i : I) := List.ofFn (fun t : Fin (count (j i)) => tally (2 ^ ((box i).get (axis (j i) t)).1))
  have rows : s.Has row := by simpa only [Realizes, Function.comp_apply, Staff.box, Iter.entry] using picks
  have C := hasLength (rows.ez (Easy.ruler Easy.identity))
  simpa [Function.comp_def, row] using C

include header J in
/-- The physical selector and remaining pair number are direct mixed-radix
readouts of the same packed rank used to enumerate the block on tape. -/
private theorem numbered_realizes (q : ∀ i, Fin (blockRadix (box i) (j i)))
    (Q : Realizes s (fun i => (q i).val)) :
    let physical i :=
      letI := modulus_neZero (hb i)
      numberedBits (hb i) (j i) ((blockAddressRank (hb i) (j i)).symm (q i))
    Realizes s (fun i => (physical i).1.val) ∧ Realizes s (fun i => (physical i).2.val) := by
  let _ (i : I) := modulus_neZero (hb i)
  let low i := lowRadix (box := box i) (j i)
  have f := (blockExtractionRulers hb header j (fun i => firstAxis (j i)) J (Realizes.fix 0)).2.1
  have L := f.dividing (Realizes.fix 2)
  have H (i : I) : 2 ^ ((box i).get (axis (j i) (firstAxis (j i)))).1 / 2 = low i := by
    change blockFieldRadix (box i) (j i) (firstAxis (j i)) / 2 = _
    rw [firstRadix_eq (hb i), Nat.mul_div_cancel _ (by decide : 0 < 2)]
  have Low : Realizes s low := by simpa only [H] using L
  have hbq i := numberedBits_fields (hb i) (j i) ((blockAddressRank (hb i) (j i)).symm (q i))
  dsimp only
  constructor
  · convert FieldSplit.col_realizes Low (Realizes.fix 2) Q using 1
    funext i
    simpa only [Equiv.apply_symm_apply, low] using (hbq i).1
  · convert FieldSplit.row_realizes Low (Realizes.fix 2) Q using 1
    funext i
    simpa only [Equiv.apply_symm_apply, low] using (hbq i).2

include header J in
/-- Prepare the scalar from the actual box header, block number, descriptor
and packed local address. Malformed fields require only the unit coefficient. -/
theorem prepareActualBlockPhase (z : I → SlotDescriptor) (q : ∀ i, Fin (blockRadix (box i) (j i)))
    (Z : s.Has z) (Q : Realizes s (fun i => (q i).val)) (P : Realizes s precision) :
    Prepared s precision (fun i =>
      letI := modulus_neZero (hb i)
      actualBlockPhase (hb i) (j i) (precision i) (z i) ((blockAddressRank (hb i) (j i)).symm (q i))) := by
  let I₀ i := (z i).1.1.length
  let B₀ i := (z i).1.2.1.length
  let op i := (z i).1.2.2
  let T₀ i := (z i).2.length
  have A : Realizes s I₀ := hasLength ((Z.ez Easy.fst).ez Easy.fst)
  have B : Realizes s B₀ := hasLength (((Z.ez Easy.fst).ez Easy.snd).ez Easy.fst)
  have O : s.Has op := ((Z.ez Easy.fst).ez Easy.snd).ez Easy.snd
  have M : Realizes s T₀ := hasLength (Z.ez Easy.snd)
  let t (i : I) : Fin (count (j i)) := ⟨I₀ i % count (j i), Nat.mod_lt _ (by have := (count_bounds (j i)).1; omega)⟩
  let batch (i : I) : Fin 15 := ⟨B₀ i % 15,Nat.mod_lt _ (by decide)⟩
  have dims := count_realizes hb header j J
  have T : Realizes s (fun i => (t i).val) := A.rem dims
  have batchN : Realizes s (fun i => (batch i).val) := B.rem (.fix 15)
  have direct := prepareBlockInstruction hb header j t batch op q J T batchN P O Q
  let _ (i : I) := modulus_neZero (hb i)
  let axisSize (i : I) := BoxFin.modulus (box i) (axis (j i) (t i))
  let rows (i : I) := Fintype.card (Spectators (fun x => BoxFin.modulus (box i) (axis (j i) x))
    (fun x => padding (box i) (axis (j i) x)) (t i))
  have occ : Realizes s axisSize := selectedAxisOrder header j t J T
  have widths : Realizes s (fun i => paddedLog (axisSize i)) :=
    (Figure.of_spoken (((Realizes.fix 2).times occ).minused (.fix 1))).short_log
  have EX := blockExtractionRulers hb header j t J T
  have C : Realizes s rows := by
    have hrows (i : I) := blockSpectatorQuotient (hb i) (j i) (t i)
    simp only [rows, hrows]
    exact EX.2.2.dividing EX.2.1
  have activeCount := (Figure.of_spoken (SynchronizedBorrowing.size_realizes C batchN)).multiplied
    ((Figure.natural 2).repeated widths)
  let addr i := (blockAddressRank (hb i) (j i)).symm (q i)
  let pairBits i := numberedBits (hb i) (j i) (addr i)
  have fields := numbered_realizes hb header j J q Q
  have inside := Prepared.phaseField P M activeCount (fun i => (pairBits i).1) (fun i => (pairBits i).2)
    (Figure.of_spoken fields.1) (Figure.of_spoken fields.2) direct
  have full := Prepared.conditional (A.below dims) (Prepared.conditional (B.below (.fix 15)) inside (Prepared.one P)) (Prepared.one P)
  convert full using 1
  funext i
  by_cases ha : I₀ i < count (j i)
  · by_cases hbatch : B₀ i < 15
    · have ht : t i = ⟨I₀ i,ha⟩ := Fin.ext (Nat.mod_eq_of_lt ha)
      have hB : batch i = ⟨B₀ i,hbatch⟩ := Fin.ext (Nat.mod_eq_of_lt hbatch)
      simp only [ha,hbatch,ite_true]
      unfold actualBlockPhase phaseAt
      simp only [show (z i).1.1.length < count (j i) from ha, dite_true,
        show (z i).1.2.1.length < 15 from hbatch]
      rw [← ht, ← hB]
      rfl
    · change (z i).1.1.length < count (j i) at ha
      change ¬ (z i).1.2.1.length < 15 at hbatch
      simp [actualBlockPhase, phaseAt, I₀, B₀, ha, hbatch]
  · change ¬ (z i).1.1.length < count (j i) at ha
    simp [actualBlockPhase, phaseAt, I₀, ha]

end PhaseTable

end NearSquareRoot
end Computability
end OAI
