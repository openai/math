import OAI.Computability.BorderVNP.CrossingFusionVerifierInput
import OAI.Computability.BorderVNP.CrossingParallelFrame
import OAI.Computability.VPVNP.OracleBinaryTarget

/-!
# Wiring all signed stages to one Boolean input

Every vertex compares the bits of its terminal and mode against the possible
labels. It reads the shared occupation masks directly from the two adjacent
boundaries. The energy tests and local signed verifiers run in parallel.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.FusionStage

open VPVNP VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr.eval Expr.size)

variable {m d : ℕ} {w : WireStates (leastEnergy m) (2^m)} {left : Bool} {b : Fin d → Bool}

private noncomputable def stageExpr (f : Checkers w left b) (i : Fin d) :
    Query (2^m) (leastEnergy m) (i.val*leastEnergy m) ⊕ Fin (f i).guesses → Expr (Raw f)
  | .inl (.inl x) => OracleBinaryTarget.expr (fun k => .inl (i.rev,k)) x.val
  | .inl (.inr (.inl j)) => OracleBinaryTarget.expr (fun k => .inr (.inl (i.rev,k))) j.val
  | .inl (.inr (.inr (.inl k))) => .input (.inr (.inr (.inl ⟨i.castSucc,k⟩)))
  | .inl (.inr (.inr (.inr k))) =>
    .input (.inr (.inr (.inl ⟨i.succ,k.cast (Nat.succ_mul i.val (leastEnergy m)).symm⟩)))
  | .inr k => .input (.inr (.inr (.inr ⟨i,k⟩)))

/-- The local signed flags read from the shared inputs and the private witness block. -/
noncomputable def stageFrame (f : Checkers w left b) (i : Fin d) : Frame (Raw f) Bool :=
  (f i).frame.subst ((Frame.initial id).step (stageExpr f i))

private theorem stageExpr_encode (f : Checkers w left b) (i : Fin d) (g : Data f) :
    (fun k => (stageExpr f i k).eval (encode f g)) =
      Sum.elim (stageQuery i g.1 g.2.1 g.2.2.1) (g.2.2.2 i) := by
  funext k
  rcases k with (x | j | v | v) | a
  · change (OracleBinaryTarget.expr _ x.val).eval _ = decide (x = g.1 i.rev)
    rw [OracleBinaryTarget.expr_eval (fun k => (.inl (i.rev,k) : Raw f)) x.val
      (g.1 i.rev).val (g.1 i.rev).isLt (encode f g)
      (fun a => (LiveHeader.testBit_wordBits (g.1 i.rev) a).symm)]
    simp [Fin.ext_iff, eq_comm]
  · change (OracleBinaryTarget.expr _ j.val).eval _ = decide (j = g.2.1 i.rev)
    rw [OracleBinaryTarget.expr_eval (fun k => (.inr (.inl (i.rev,k)) : Raw f)) j.val (g.2.1 i.rev).val
      ((g.2.1 i.rev).isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two _)) (encode f g)
      (fun a => (LiveHeader.testBit_wordBits ((g.2.1 i.rev).castLE (Nat.le_pow_clog Nat.one_lt_two _)) a).symm)]
    simp [Fin.ext_iff, eq_comm]
  · exact (stageQuery_old ..).symm
  · exact (stageQuery_next ..).symm
  · rfl

/-- Correctness of the wiring at every canonical guess, before summing local paths. -/
theorem stageFrame_encode (f : Checkers w left b) (i : Fin d) (g : Data f) (sign : Bool) :
    (stageFrame f i).eval (encode f g) sign = stageFlags f g.1 g.2.1 g.2.2.1 g.2.2.2 i sign := by
  have init : (Frame.initial (id : Raw f → Raw f)).eval (encode f g) = encode f g :=
    funext (fun k => Frame.initial_eval id _ k)
  rw [stageFrame, Frame.subst_eval]
  change (f i).frame.eval _ sign = (f i).frame.eval _ sign
  congr 1
  funext k
  rw [Frame.step_eval, init]
  exact congrFun (stageExpr_encode f i g) k

/-- Gate bound for a wired stage, including the input comparators. -/
theorem stageFrame_size (f : Checkers w left b) (i : Fin d) :
    (stageFrame f i).size ≤ (f i).frame.size +
      (2^m + 2*leastEnergy m + i.val*leastEnergy m + (i.val*leastEnergy m + leastEnergy m) +
        (f i).guesses) * (3*(m + Nat.clog 2 (2*leastEnergy m))+2) := by
  have h := Frame.step_size_le (Frame.initial (id : Raw f → Raw f)) (stageExpr f i)
    (3*(m + Nat.clog 2 (2*leastEnergy m))+2) (by
      rintro ((k|k|k|k)|k)
      · have := OracleBinaryTarget.expr_size_le (fun j : Fin m => (Sum.inl (i.rev,j) : Raw f)) k.val
        change (OracleBinaryTarget.expr _ _).size ≤ _
        omega
      · have := OracleBinaryTarget.expr_size_le
          (fun j : Fin (Nat.clog 2 (2*leastEnergy m)) => (Sum.inr (Sum.inl (i.rev,j)) : Raw f)) k.val
        change (OracleBinaryTarget.expr _ _).size ≤ _
        omega
      all_goals change 1 ≤ _; omega)
  simp only [Frame.initial_size, zero_add, Query, Fintype.card_sum, Fintype.card_fin] at h
  rw [stageFrame, Frame.subst_size, add_comm]
  apply Nat.add_le_add_left
  simpa only [Nat.add_assoc] using h

/-- The validity bit is obtained by reusing the occupancy bits for the appropriate boundary. -/
noncomputable def stateFrame (f : Checkers w left b) (i : Fin (d+1)) : Frame (Raw f) Unit :=
  (StateIndex.validFrame (i.val * leastEnergy m)).subst
    (Frame.initial (fun k => .inr (.inr (.inl ⟨i,k⟩))))

@[simp] theorem stateFrame_eval (f : Checkers w left b) (i : Fin (d+1)) (r : Raw f → Bool) :
    (stateFrame f i).eval r () = (StateIndex.validFrame _).eval (readState f r i) () := by
  rw [stateFrame, Frame.subst_eval]
  congr 1
  funext k
  exact Frame.initial_eval _ _ _

@[simp] theorem stateFrame_size (f : Checkers w left b) (i : Fin (d+1)) :
    (stateFrame f i).size = (StateIndex.validFrame (i.val * leastEnergy m)).size := by
  simp [stateFrame]

end Crossing.FusionStage

end BorderVNP
end Computability
end OAI
