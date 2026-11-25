import OAI.Computability.NearSquareRoot.InterchangeRepairSchedule
import OAI.Computability.NearSquareRoot.InterchangeStageTape

/-!
# Charged execution of the full packed predictor

The clock repeatedly executes the same finite script. Each moved register is
charged once for every original ground-field component stored in the bank.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace Interchange.StageScript

variable {M E A X : Type} [Fintype A]

/-- Execute an endomorphism of a finite register set exactly `k` times. -/
def repeatProgram (p : Program M E A A) : ℕ → Program M E A A
  | 0 => .table id
  | k+1 => .seq (repeatProgram p k) p

theorem eval_repeatProgram (perm : M → Equiv.Perm X) (p : Program M E A A) (k : ℕ)
    (x : A → X → E) : eval perm (repeatProgram p k) x = (eval perm p)^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [repeatProgram, eval_seq, ih, Function.iterate_succ_apply']

theorem cost_repeatProgram (price : M → ℕ) (p : Program M E A A) (k : ℕ) :
    cost price (repeatProgram p k) = k * cost price p := by
  induction k with
  | zero => simp [repeatProgram]
  | succ k ih => rw [repeatProgram, cost_seq, ih, Nat.succ_mul]

end Interchange.StageScript

namespace Interchange.RepairSchedule

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  InterchangeBank StageScript StageRoute SwapRepair

variable {U Y L B H K : Type} [Field K] [Fintype L] [DecidableEq L] [Fintype B] [Fintype H]
  {m : ℕ} {X : U → Type} {ρ : Regime U} {job : Job Y} {N l : U → ℕ} {zone : U → Y → Prop}

/-- Endpoint of the scalar bank representation for abstract extension rows. -/
def streams {s : ℕ} (x : (i : U) → Data K L (X i) s m) :
    (i : U) → (Fin s × BasisIndex m) × L → X i → K :=
  fun i t a => components K m (x i t.2 t.1.1 a) t.1.2

/-- A single charged P192 program computes the predictor simultaneously on
all labels. Its budget is exactly the clock order times the one-stage ledger. -/
theorem execute_predict
    (rect : B → Rectangle L) (I J : H → L) (mid : Matrix H H K) (e : Environment K m)
    (g : (i : U) → Layout rect (Fin m) (X i))
    (quote : Move rect (Fin m) I J → ℕ) (hi : quote .idle = 0)
    (ha : ∀ j t, quote (.align j t) = 0) (hu : ∀ j t, quote (.unalign j t) = 0)
    (machine : Compiler ρ N l job zone K (fun i => (g i).perm) quote 1)
    (rows : Series (PackedPencil.Index m)) (labels : Series L)
    (x : (i : U) → Data K L (X i) (width m) m) :
    let render := machine.render (rows.cart labels)
    Hopto job ρ N l zone ((order m * (moveCharges (PackedPencil.Index m) quote).count : ℕ) : ℤ)
      (together ρ.header (render (streams x)))
      (render (streams fun i => predict rect I J mid e (g i) (x i))) := by
  let p := PackedPencil.program rect I J mid e
  let v (i : U) (w : L) (a : X i) (t : PackedPencil.Index m) := components K m (x i w t.1 a) t.2
  have h := (machine.lanes rows).run (repeatProgram p (order m)) labels labels v
  simp_rw [eval_repeatProgram] at h
  have hcost : Fintype.card (PackedPencil.Index m) * cost quote p =
      (moveCharges (PackedPencil.Index m) quote).count := by
    exact scalar_stage_cost (PackedPencil.Index m) mid _ _ quote hi ha hu
  have total : (1 * Fintype.card (PackedPencil.Index m)) * cost quote (repeatProgram p (order m)) =
      order m * (moveCharges (PackedPencil.Index m) quote).count := by
    rw [cost_repeatProgram, Nat.one_mul, Nat.mul_left_comm _ (order m), hcost]
  rw [total] at h
  have hstream :
      streams (fun i => predict rect I J mid e (g i) (x i)) =
       fun i (t : PackedPencil.Index m × L) a =>
         (eval (g i).perm p)^[order m] (v i) t.2 a t.1 := by
    funext i t a
    rcases t with ⟨⟨u,d⟩,w⟩
    dsimp only [streams, predict]
    rw [LinearEquiv.apply_symm_apply]
  rw [hstream]
  exact h

end Interchange.RepairSchedule

end

end NearSquareRoot
end Computability
end OAI
