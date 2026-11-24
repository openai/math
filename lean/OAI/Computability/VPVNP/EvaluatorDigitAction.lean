import OAI.Computability.VPVNP.EvaluatorDigitFetch
import OAI.Computability.VPVNP.EvaluatorDigitCallbacks
import OAI.Computability.VPVNP.EvaluatorRadixRows
import OAI.Computability.VPVNP.EvaluatorRoutine

/-!
# Executing one label at one radix position

The cell control reads its binary counter from the packed table. At the
most-significant-first position `j` of exponent `eᵢ`, it executes the
label callback precisely `⌊eᵢ / Q^(Z-1-j)⌋ mod Q` times on every successful
path. The returned scheduler bank is ready for the next label.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorDigitAction

open RAMTape EvaluatorDigitFetch EvaluatorDigitRepeat EvaluatorDigitCallbacks
open EvaluatorRadixRows EvaluatorRoutine

variable {P S I : Type}

/-- Both the lookup control and the decrement loop are fixed across all
rows, columns, field cardinalities, and input widths. -/
def cellRoutine (body : FiniteRoutine (Port P)) : FiniteRoutine (Port P) :=
  fetch.followedBy (.ofRoutine (repeatRoutine .digit .borrow body.body))

/-- A per-label clock independent of the two cursor positions. -/
def cellBudget (t Z ℓ Q B : ℕ) :=
  19*(t*Z) + 13*(t*Z*ℓ) + 4 + Q*(4*ℓ+B+3)

theorem frame_digit [DecidableEq P] (data : List Bool)
    (t Z ℓ i j labelsLeft colsLeft : ℕ) (p : Stacks P) (bits : List Bool) :
    frame Port.digit .borrow (bank data t Z ℓ i j labelsLeft colsLeft p) bits [] =
      Function.update (bank data t Z ℓ i j labelsLeft colsLeft p) Port.digit bits := by
  funext k
  cases k <;> rfl

variable [DecidableEq P] [Fintype I] (body : FiniteRoutine (Port P))
    (payload : S → Stacks P) (next : S → I → S) {t Z : ℕ} (e : Fin t → BurstRAM.Word Z)
    (ℓ Q B : ℕ) (hq : 0 < Q) (hfit : Q ≤ 2 ^ ℓ) (i : Fin t) (j : Fin Z)
    (labelsLeft colsLeft : ℕ)

local notation "data" => packedTable ℓ Q (List.ofFn e)
local notation "pre" => bank data t Z ℓ i.val j.val labelsLeft colsLeft ∘ payload
local notation "digitValue" => Fin.val (e i) / Q^(Z-1-j.val) % Q

/-- At any legal pair of cursor positions the deterministic lookup
prepares the exact radix digit for the countdown. -/
theorem fetch_cell_runs (x : S) :
    fetch.Runs (fetchTicks i.val Z j.val ℓ) (pre x)
      (frame .digit .borrow (pre x) (PrimedCounter.digits ℓ digitValue) []) := by
  have hi : i.val < (List.ofFn e).length := by simp
  have fits : (i.val*Z+j.val)*ℓ+ℓ ≤ (data).length := by
    simpa [Nat.mul_assoc] using EvaluatorDigitAddress.cell_fits i.isLt j.isLt ℓ
  have cell : (((data).drop ((i.val*Z+j.val)*ℓ)).take ℓ) = PrimedCounter.digits ℓ digitValue := by
    simpa using packedTable_cell ℓ Q (List.ofFn e) [] i.val j.val hi j.isLt
  have h := fetch_runs data t Z ℓ i.val j.val labelsLeft colsLeft (payload x) fits
  rw [cell, ← frame_digit] at h
  exact h

include hq hfit in
/-- A callback preserves the scheduler registers on every normal return. Its
integer count can include any finite number of distinct outcomes, including
outcomes that share a successor state. -/
theorem cellRoutine_realizes
    (callback : ∀ x bits fuel, (bits : List Bool).length = ℓ → B ≤ fuel →
      ∃ delay : I → ℕ, (∀ a, delay a ≤ B) ∧ ∀ c,
        body.body.count c fuel (frame .digit .borrow (pre x) bits []) =
          ∑ a, c (fuel-delay a) (frame .digit .borrow (pre (next x a)) bits [])) :
    Realizes (cellRoutine body).body pre pre (cellBudget t Z ℓ Q B)
      (fun f x => ∑ z : Fin digitValue → I, f ((List.ofFn z).foldl next x)) := by
  let d := digitValue
  let bits := PrimedCounter.digits ℓ d
  let loaded (x : S) := frame .digit .borrow (pre x) bits []
  have hw : bits.length = ℓ := by simp [bits, PrimedCounter.digits]
  have hd : d < Q := Nat.mod_lt _ hq
  have hv : TapeWord.value bits = d := by
    simp [bits, PrimedCounter.digits, TapeWord.value_wordBits, Nat.mod_eq_of_lt (hd.trans_le hfit)]
  let fetchBound := 19*(t*Z)+13*(t*Z*ℓ)+4
  have prefixRun : Realizes fetch.body pre loaded fetchBound (fun f x => f x) := by
    apply Realizes.of_runs (g := id)
    intro x
    exact ⟨fetchTicks i.val Z j.val ℓ, fetchTicks_le_cells i.isLt j.isLt ℓ,
      fetch_cell_runs payload e ℓ Q i j labelsLeft colsLeft x⟩
  have loop : Realizes (repeatRoutine .digit .borrow body.body) loaded pre (repeatBudget ℓ B d)
      (fun f x => ∑ z : Fin d → I, f ((List.ofFn z).foldl next x)) := by
    apply Realizes.of_delay (next := fun x z => (List.ofFn z).foldl next x)
    intro x fuel hf
    obtain ⟨delay, hdelay, he⟩ := repeat_count_of_bound Port.digit .borrow (by intro h; cases h) body.body
      pre next ℓ B callback d bits hw hv x fuel hf
    refine ⟨delay, hdelay, fun c => ?_⟩
    rw [he c]
    apply Finset.sum_congr rfl
    intro z _
    have empty (y : S) : frame .digit .borrow (pre y) [] [] = pre y := by
      rw [Function.comp_apply, frame_digit]
      exact Function.update_eq_self ..
    rw [empty]
  apply (prefixRun.followedBy loop).mono
  exact Nat.add_le_add_left (Nat.mul_le_mul_right (4*ℓ+B+3) hd) fetchBound

end EvaluatorDigitAction

end VPVNP
end Computability
end OAI
