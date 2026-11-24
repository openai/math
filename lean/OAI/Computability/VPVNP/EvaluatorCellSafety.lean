import OAI.Computability.VPVNP.EvaluatorDigitAction
import OAI.Computability.VPVNP.EvaluatorDigitSafety
import OAI.Computability.VPVNP.EvaluatorRoutineSafety

/-!
# Time and peak storage for one complete label action

A deterministic lookup uses a polynomial number of temporary bits. Once the
lookup returns, its temporary stacks are empty and only one digit's worth of
counter storage is live. The subsequent countdown can invoke exponentially
many callbacks without accumulating any of their work space.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorCellSafety

open RAMTape EvaluatorDigitFetch EvaluatorDigitRepeat EvaluatorDigitCallbacks
open EvaluatorDigitSafety EvaluatorRadixRows EvaluatorDigitAction EvaluatorRoutineSafety

variable {P S : Type} [DecidableEq P] (body : FiniteRoutine (Port P))
    (safe : Stacks (Port P) → Prop) (payload : S → Stacks P)
    {t Z : ℕ} (e : Fin t → BurstRAM.Word Z) (ℓ Q B : ℕ) (hq : 0 < Q) (hfit : Q ≤ 2^ℓ)
    (i : Fin t) (j : Fin Z) (labelsLeft colsLeft : ℕ)

local notation "pre" => bank (packedTable ℓ Q (List.ofFn e)) t Z ℓ i.val j.val labelsLeft colsLeft ∘ payload
local notation "fetchBound" => (19*(t*Z)+13*(t*Z*ℓ)+4)

include hq hfit in
/-- All normal returns preserve the scheduler bank outside the evaluator
payload. Both successful and rejecting paths obey the cell clock. -/
theorem cell_bounded
    (room : ∀ x s, (∀ k, (s k).length ≤ (pre x k).length+fetchBound) → safe s)
    (frames : ∀ x (xs ys : List Bool), xs.length+ys.length ≤ ℓ →
      safe (frame .digit .borrow (pre x) xs ys))
    (callback : ∀ (bits : List Bool), bits.length = ℓ →
      Bounded body.body safe (fun x => frame .digit .borrow (pre x) bits [])
        (fun x => frame .digit .borrow (pre x) bits []) B) :
    Bounded (cellRoutine body).body safe pre pre (cellBudget t Z ℓ Q B) := by
  let d := (e i).val / Q^(Z-1-j.val) % Q
  let bits := PrimedCounter.digits ℓ d
  let loaded (x : S) := frame .digit .borrow (pre x) bits []
  have hw : bits.length = ℓ := by simp [bits, PrimedCounter.digits]
  have hd : d < Q := Nat.mod_lt _ hq
  have hv : TapeWord.value bits = d := by
    simp [bits, PrimedCounter.digits, TapeWord.value_wordBits, Nat.mod_eq_of_lt (hd.trans_le hfit)]
  have fetchSafe : Bounded fetch.body safe pre loaded fetchBound := by
    apply Bounded.of_runs_with_room (g := id) _ room
    intro x
    exact ⟨_, fetchTicks_le_cells i.isLt j.isLt ℓ, fetch_cell_runs payload e ℓ Q i j labelsLeft colsLeft x⟩
  have loopSafe : Bounded (repeatRoutine .digit .borrow body.body) safe loaded pre (repeatBudget ℓ B d) := by
    intro extra fuel hf x c hc
    apply repeat_safe Port.digit .borrow (by intro h; cases h) body.body safe c pre ℓ B frames _
      d bits hw hv x extra fuel hf
    · intro y n hn
      rw [Function.comp_apply, frame_digit]
      have hempty : Function.update (pre y) Port.digit [] = pre y := Function.update_eq_self ..
      exact hempty.symm ▸ hc y n hn
    · intro y counter hl rest n enough cont finish
      exact callback counter hl rest n enough y cont finish
  apply (fetchSafe.followedBy loopSafe).mono
  exact Nat.add_le_add_left (Nat.mul_le_mul_right (4*ℓ+B+3) hd) fetchBound

end EvaluatorCellSafety

end VPVNP
end Computability
end OAI
