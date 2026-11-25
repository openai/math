import OAI.Computability.BorderVNP.CellPacketGeometryExecute

/-! # Exact readback of the inverse descriptor permutation from the joint output -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry

open ParseBatchSort Packing.Word VPVNP.VerifierNetwork
open private joint_second descRows pre from OAI.Computability.BorderVNP.CellPacketGeometryDirectory

variable {σ E : Type*} [Fintype σ] [Fintype E] {p d k w : ℕ}

/-- The actual inverse descriptor array is the inverse of the second
permutation in the joint geometry output. Its ordinal bound holds
independently of the descriptor payload values. -/
theorem descriptorInverse_of_output (source : Frame σ (Columns p d k w E))
    (expr : Fin (2^d) → WidthExpr (E ⊕ Fin (2^p))) (x : σ → Bool) (dest : ℕ)
    (mem : ℕ → ℕ) (wide : 2^d ≤ 2^w)
    (output : ∀ i : Fin (Total p d), mem (dest+i.val) =
      value (fun j => (joint source expr).eval x (.inl (i,j)))) :
    ∃ π : Equiv.Perm (Fin (2^d)), ∀ i, mem (descriptorBank dest p+2^d+i.val) = (π.symm i).val := by
  let rows := (descRows (k := k) (w := w) expr).eval ((pre source).eval x)
  obtain ⟨π,_,_,inverse⟩ := sortedFrame_values rows wide
  refine ⟨π,fun i => ?_⟩
  have atWord := output (outputIndex (.inr (.inr i)))
  have bits := funext (joint_second source expr x (.inr i))
  simpa only [descriptorBank,Nat.add_assoc,outputIndex,Sum.map_inr,finSumFinEquiv_apply_right,Fin.val_natAdd] using
    (atWord.trans ((congrArg value bits).trans (inverse i)))

end CellPacketGeometry

end BorderVNP
end Computability
end OAI
