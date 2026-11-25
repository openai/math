import OAI.Computability.NearSquareRoot.PermutationLayoutConjugate
import OAI.Computability.NearSquareRoot.PermutationLayoutPorts
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBatchBits

/-! # A physical sparse-mask operation on the actual packed Beneš address -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PermutationLayout
open IntegerMultiplication IntegerMultiplication.Adic PositionProgram BoxFin

noncomputable section
variable {p b G low c L : ℕ} {box : List (ℕ × ℕ)} [∀ i, NeZero (modulus box i)]
variable (hb : BoxShape.Valid (maskWidth p b G low) L box) (hd : 4 ≤ box.length)
  (pos : 0 < G) (fit : low+2*((b+1)*G)+c ≤ maskWidth p b G low)
  (π : Equiv.Perm (Fin (maskWidth p b G low)))
  (control : Block 2 p → Fin b → Bool) (which : Fin (box.length / 4) → ℕ)
  (tables : Fin (box.length / 4) → Benes.RawTable) (stage : Bool × ℕ) (batch : ℕ)

/-- Conjugating the physical sparse XOR with its position permutation performs the
requested batched Beneš layer on the packed residue address. The local table
read is needed only for blocks having a port at the current stage. -/
theorem natural_batch (active : Fin b → Fin (box.length / 4))
    (wide : ∀ q, stage.2 < physicalWidth (box := box) (active q))
    (selected : ∀ q, which (active q) = batch)
    (complete : ∀ j, which j = batch → stage.2 < physicalWidth (box := box) j → ∃ q, active q = j)
    (placed : ∀ q, π (targetPos pos fit q) = packedPort hb hd ⟨active q,⟨stage.2,wide q⟩⟩)
    (y : Block 2 (maskWidth p b G low))
    (read : ∀ q, control (prefixWord (permuteNative π y)) q =
      let s := Benes.rawSetting (tables (active q)) stage.2 (List.ofFn ((packedRecord hb hd (flatAddress 2 _ y)).2 (active q)))
      if stage.1 then s.2 else s.1) :
    packedRecord hb hd (flatAddress 2 _ (naturalStage π control y)) =
      Benes.batchStage which (physicalWidth (box := box)) (fun _ : Unit => tables) stage batch
        (packedRecord hb hd (flatAddress 2 _ y)) := by
  apply Prod.ext
  · apply Subsingleton.elim
  funext j r
  rw [Benes.batchStage_bit]
  by_cases h : which j = batch ∧ stage.2 = r.val
  · obtain ⟨q,rfl⟩ := complete j h.1 (h.2.symm ▸ r.isLt)
    have hr : r = ⟨stage.2,wide q⟩ := Fin.ext h.2.symm
    rw [ite_eq_left h, packedRecord_blockBit, packedRecord_blockBit, hr, ← placed q,
      natural_target pos fit, read q]
  · rw [ite_eq_right h, packedRecord_blockBit, packedRecord_blockBit]
    apply natural_other pos fit
    intro q heq
    rw [placed q] at heq
    have same := (packedPort hb hd).injective heq
    have hj := congrArg Sigma.fst same
    have hr := congrArg (fun v : Σ j, Fin (physicalWidth (box := box) j) => v.2.val) same
    exact h ⟨(congrArg which hj).trans (selected q),hr.symm⟩

end
end Controlled.PermutationLayout

end NearSquareRoot
end Computability
end OAI
