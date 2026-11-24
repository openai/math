import OAI.Computability.VPVNP.EvaluatorMonomialSchedule
import OAI.Computability.VPVNP.EvaluatorChronologicalSafety
import OAI.Computability.VPVNP.EvaluatorCellSafety

/-! # The exponent scheduler's all-branch time and space bounds

The largest intermediate digit counter has the bit width of the field
cardinality, regardless of how many times the label callback is invoked.
The fixed control therefore preserves a polynomial storage cap even on
branches that reject inside a matrix-entry query.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorMonomialSchedule

open RAMTape EvaluatorChronologicalLoop EvaluatorDigitFetch EvaluatorCellSafety
  EvaluatorDigitAction EvaluatorRadixRows EvaluatorRoutineSafety

variable {P S : Type} [DecidableEq P] {t Z : ℕ} (e : Fin t → BurstRAM.Word Z)
  (ℓ Q BF BM space : ℕ) (payload : S → Stacks P)
  (hp : ∀ x p, (payload x p).length ≤ space)
  (frobenius multiply : FiniteRoutine (Port P))

local notation "data" => packedTable ℓ Q (List.ofFn e)
local notation "cap" => schedulerSpace (List.length data) t Z ℓ space
local notation "fits" => stackFits cap

include hp in
/-- For callbacks with the indicated all-path contracts, the complete
monomial traversal uses the same clock as its count computation and keeps
every stack within the polynomial scheduler allowance. -/
theorem machine_bounded (hq : 0 < Q) (hfit : Q ≤ 2^ℓ)
    (hf : ∀ (j : Fin Z) left, j.val + left < Z → Bounded frobenius.body fits
      (fun x => bank data t Z ℓ 0 j 0 left (payload x))
      (fun x => bank data t Z ℓ 0 j 0 left (payload x)) BF)
    (hm : ∀ (i : Fin t) (j : Fin Z) labels cols, i.val + labels < t → j.val + cols < Z →
      ∀ bits : List Bool, bits.length = ℓ →
      let pre (x : S) := EvaluatorDigitRepeat.frame Port.digit Port.borrow
        (bank data t Z ℓ i j labels cols (payload x)) bits []
      Bounded multiply.body fits pre pre BM) :
    Bounded (machine frobenius multiply).body fits
      (fun x => bank data t Z ℓ 0 0 0 Z (payload x)) (fun x => bank data t Z ℓ 0 0 0 0 (payload x))
      (budget t Z ℓ Q BF BM) := by
  apply traverse_bounded data t Z ℓ space payload hp frobenius (cellRoutine multiply) BF (cellBudget t Z ℓ Q BM)
  · intro j left hj
    exact hf ⟨j, by omega⟩ left hj
  · intro j cols hj i labels hi
    let i' : Fin t := ⟨i, by omega⟩
    let j' : Fin Z := ⟨j, by omega⟩
    apply cell_bounded multiply fits payload e ℓ Q BM hq hfit i' j' labels cols _ _ (hm i' j' labels cols hi hj)
    · intro x s hs k
      have h₀ := bank_length data t Z ℓ space payload hp hi.le hj.le x k
      have h₁ := hs k
      change (s k).length ≤ (bank data t Z ℓ i j labels cols (payload x) k).length + _ at h₁
      unfold schedulerSpace
      omega
    · intro x xs ys hlen k
      have h₀ := bank_length data t Z ℓ space payload hp hi.le hj.le x k
      by_cases hd : k = .digit
      · subst k
        simp only [EvaluatorDigitRepeat.frame, Function.update_self,
          Function.update_of_ne (show (Port.digit : Port P) ≠ .borrow by intro h; cases h)]
        unfold schedulerSpace
        omega
      · by_cases hb : k = .borrow
        · subst k
          simp only [EvaluatorDigitRepeat.frame, Function.update_self]
          unfold schedulerSpace
          omega
        · simp only [EvaluatorDigitRepeat.frame, Function.update_of_ne hb, Function.update_of_ne hd]
          exact h₀.trans (by unfold schedulerSpace; omega)

/-- The bounded contract implies a physical stopping statement and the peak
bound on all reachable stack states, even if an intermediate branch rejects. -/
theorem machine_space_clock (outcome : Bool) (x : S)
    (hpost : ∀ y, fits (bank data t Z ℓ 0 0 0 0 (payload y)))
    (h : Bounded (machine frobenius multiply).body fits
      (fun y => bank data t Z ℓ 0 0 0 Z (payload y)) (fun y => bank data t Z ℓ 0 0 0 0 (payload y))
      (budget t Z ℓ Q BF BM)) :
    let r := (machine frobenius multiply).body
    let start := bank data t Z ℓ 0 0 0 Z (payload x)
    StopsWithin (r.close outcome) (1+budget t Z ℓ Q BF BM) (some r.entry) start ∧
      ∀ ⦃q s⦄, StackCompiler.Reach (r.close outcome) (some r.entry) start q s → fits s := by
  have hs := h 1 (1+budget t Z ℓ Q BF BM) le_rfl x (fun n s => 0<n ∧ fits s)
    (fun y n hn => ⟨hn, hpost y⟩)
  exact ⟨hs.stopsWithin outcome (fun _ _ hh => hh.1), fun _ _ hr => hs.reach outcome (fun _ _ hh => hh.2) hr⟩

end EvaluatorMonomialSchedule

end VPVNP
end Computability
end OAI
