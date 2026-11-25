import OAI.Computability.NearSquareRoot.PrecisionGridLocalRulers
import OAI.Computability.NearSquareRoot.PrecisionGridSplitRank
import OAI.Computability.NearSquareRoot.SynchronizedBatchPhases
import OAI.Computability.NearSquareRoot.SynchronizedBlockCardinality

/-! # Computing a given synchronized phase gate on its physical block -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Strip Staff BoxFin SynchronizedBlocks SynchronizedBorrowing
open ShortFourier ShortFourier.BatchWord ShortFourier.AxisWord

variable {k l : ℕ} {b : List (ℕ × ℕ)}

private theorem selectedPos (hb : BoxShape.Valid k l b) (j : Fin (b.length/4)) (t : Fin (count j)) :
    0 < BoxFin.modulus b (axis j t) := by
  have H := (hb.axisBounds _ (List.get_mem b (axis j t))).2.2.1
  unfold BoxFin.modulus
  omega

/-- The number of spectator rows can be computed by division of the two
padded sizes read from the header. -/
theorem blockSpectatorQuotient (hb : BoxShape.Valid k l b) [∀ i, NeZero (BoxFin.modulus b i)]
    (j : Fin (b.length/4)) (t : Fin (count j)) :
    Fintype.card (Spectators (fun u => BoxFin.modulus b (axis j u)) (fun u => padding b (axis j u)) t) =
      blockRadix b j / blockFieldRadix b j t := by
  have hr : BoxFin.modulus b (axis j t) + padding b (axis j t) = blockFieldRadix b j t :=
    Nat.add_sub_of_le (hb.axisBounds _ (List.get_mem b (axis j t))).2.2.2
  rw [← spectator_mul_axis hb j t, hr]
  exact (Nat.mul_div_cancel _ (Nat.two_pow_pos _)).symm

/-- Value of the phase gate at the canonical physical address of this block,
after interpreting the program's current axis and borrowing batch. -/
noncomputable def instructionPhase (hb : BoxShape.Valid k l b) (j : Fin (b.length/4)) (t : Fin (count j))
    (batch : Fin 15) (op : Inst) (bits : ℕ) (x : BlockAddress (BoxAxis b) j) : ℂ :=
  letI := modulus_neZero hb
  let a u := BoxFin.modulus b (axis j u)
  let c u := padding b (axis j u)
  let B := Fintype.card (Spectators a c t)
  let y := axisLayout a c (blockSpectators hb j) t x
  placedCoefficient (SlotQuery.ofInstruction (a t) bits op (selectedPos hb j t))
    (first B batch) (SynchronizedBorrowing.size B batch) y.1.val (finSumFinEquiv y.2).val

/-- Reading this phase at every entry yields precisely the mathematical gate
of the short Fourier program. -/
theorem instructionPhase_matrix (hb : BoxShape.Valid k l b) (j : Fin (b.length/4)) (t : Fin (count j))
    (batch : Fin 15) (op : Inst) (ht : op.1.length ∈ phaseTags) (bits : ℕ) :
    letI := modulus_neZero hb
    let a u := BoxFin.modulus b (axis j u)
    let c u := padding b (axis j u)
    let w u := paddedLog (a u)
    ∀ (har : ∀ u, a u ≤ 2 ^ w u) (hborrow : ∀ u, 2 * 2 ^ w u ≤ 8 * a u),
      gateMatrix a c w (blockSpectators hb j) har hborrow (t,batch,op) =
        Matrix.diagonal (instructionPhase hb j t batch op bits) := by
  let _ := modulus_neZero hb
  dsimp only
  intro har hborrow
  exact gateMatrix_phase _ _ _ _ har hborrow t batch op ht bits

/-- A single setup program produces the phase at the chosen physical block
rank from unary box, instruction and rank data. -/
theorem prepareBlockInstruction {I : Type} {s : Regime I} {k l bits : I → ℕ} {b : I → List (ℕ × ℕ)}
    (hb : ∀ i, BoxShape.Valid (k i) (l i) (b i))
    (header : s.Has (fun i => (b i).map (fun p => (tally p.1, tally p.2))))
    (j : ∀ i, Fin ((b i).length/4)) (t : ∀ i, Fin (count (j i))) (batch : I → Fin 15)
    (op : I → Inst) (q : ∀ i, Fin (blockRadix (b i) (j i)))
    (J : Realizes s (fun i => (j i).val)) (T : Realizes s (fun i => (t i).val))
    (B : Realizes s (fun i => (batch i).val)) (P : Realizes s bits) (Op : s.Has op)
    (Q : Realizes s (fun i => (q i).val)) :
    Prepared s bits (fun i =>
      letI := modulus_neZero (hb i)
      instructionPhase (hb i) (j i) (t i) (batch i) (op i) (bits i)
        ((blockAddressRank (hb i) (j i)).symm (q i))) := by
  let rad i := blockFieldRadix (b i) (j i)
  let a i := BoxFin.modulus (b i) (axis (j i) (t i))
  let p i := CRT.«prefix» (rad i) (t i)
  obtain ⟨pr,axisRad,total⟩ := blockExtractionRulers hb header j t J T
  have pre : Realizes s p := by
    simp only [p,FieldSplit.prefix_take]
    exact pr
  have ar : Realizes s (fun i => rad i (t i)) := axisRad
  have occ : Realizes s a := selectedAxisOrder header j t J T
  have prog := prepareInstructionBatch occ (fun i => selectedPos (hb i) (j i) (t i))
    P Op (total.dividing ar) B (FieldSplit.row_realizes pre ar Q) (FieldSplit.col_realizes pre ar Q)
  convert prog using 2
  rename_i i
  let _ := modulus_neZero (hb i)
  let x := (blockAddressRank (hb i) (j i)).symm (q i)
  obtain ⟨hf,hg⟩ := blockAxisLayout_fields (hb i) (j i) (t i) x
  rw [show blockAddressRank (hb i) (j i) x = q i from Equiv.apply_symm_apply ..] at hf hg
  dsimp only [x] at hf hg
  dsimp only [instructionPhase]
  rw [hf, hg, blockSpectatorQuotient (hb i) (j i) (t i)]

end PhaseTable

end NearSquareRoot
end Computability
end OAI
