import OAI.Computability.VPVNP.EvaluatorDigitAddress
import OAI.Computability.VPVNP.EvaluatorDigitLookup

/-!
# Fetching a packed digit during the column and label loops

The scheduler stores both forward indices on tally stacks. Each fetch computes
the bit address, reads the selected cell, and restores the table. Only the
digit stack changes across the whole call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorDigitFetch

open RAMTape

/-- The scheduler owns the address counters, packed table, and digit scratch
stacks. The callback's own registers occupy the `work` ports. -/
inductive Port (P : Type) where
  | addr (k : EvaluatorDigitAddress.Port)
  | table | saved | rev | digit | borrow | labels | labelsLeft | colsLeft | copyTmp
  | work (p : P)
  deriving DecidableEq, Fintype

variable {P : Type}

/-- Between matrix queries all lookup and decrement scratch is empty. -/
def bank (data : List Bool) (t Z ℓ i j labelsLeft colsLeft : ℕ) (payload : Stacks P) :
    Stacks (Port P)
  | .addr k => EvaluatorDigitAddress.ready i Z j ℓ k
  | .table => data
  | .labels => List.replicate t true
  | .labelsLeft => List.replicate labelsLeft true
  | .colsLeft => List.replicate colsLeft true
  | .work p => payload p
  | _ => []

private def lookupPort : EvaluatorDigitLookup.Port → Port P
  | .src => .table
  | .offset => .addr .offset
  | .width => .addr .cellWidth
  | .saved => .saved
  | .revDigit => .rev
  | .digit => .digit

private theorem lookupPort_injective : Function.Injective (lookupPort (P := P)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [lookupPort]

/-- Compute the row-major bit address and read one digit without consuming
the packed table or any of the scheduler's loop indices. -/
def fetch : FiniteRoutine (Port P) :=
  (EvaluatorDigitAddress.addressRoutine.onPorts .addr).followedBy
    (EvaluatorDigitLookup.lookupRoutine.onPorts lookupPort)

/-- Instruction count for computing a packed digit's bit address and then reading that cell
while restoring the table. -/
def fetchTicks (i Z j ℓ : ℕ) := EvaluatorDigitAddress.addressTicks i Z j ℓ +
  EvaluatorDigitLookup.lookupTicks ((i*Z+j)*ℓ) ℓ

theorem fetch_runs [DecidableEq P] (data : List Bool) (t Z ℓ i j labelsLeft colsLeft : ℕ)
    (payload : Stacks P) (fits : (i*Z+j)*ℓ+ℓ ≤ data.length) :
    fetch.Runs (fetchTicks i Z j ℓ) (bank data t Z ℓ i j labelsLeft colsLeft payload)
      (Function.update (bank data t Z ℓ i j labelsLeft colsLeft payload) .digit
        ((data.drop ((i*Z+j)*ℓ)).take ℓ)) := by
  let s := bank data t Z ℓ i j labelsLeft colsLeft payload
  let offset := (i*Z+j)*ℓ
  let mid := Function.update (Function.update s (.addr .offset) (List.replicate offset true))
    (.addr .cellWidth) (List.replicate ℓ true)
  let out := Function.update s Port.digit ((data.drop offset).take ℓ)
  have h₁ : (EvaluatorDigitAddress.addressRoutine.onPorts Port.addr).Runs
      (EvaluatorDigitAddress.addressTicks i Z j ℓ) s mid :=
    EvaluatorDigitAddress.addressRoutine_runs_framed (p := Port.addr) (fun _ _ h => Port.addr.inj h) (fun _ => rfl)
  have h₂ : (EvaluatorDigitLookup.lookupRoutine.onPorts lookupPort).Runs
      (EvaluatorDigitLookup.lookupTicks offset ℓ) mid out := by
    apply EvaluatorDigitLookup.lookupRoutine.runs_onPorts_framed lookupPort_injective
      (EvaluatorDigitLookup.lookupRoutine_runs_at data [] offset ℓ fits)
    · intro k
      cases k <;> rfl
    · intro k
      cases k with
      | digit => simp only [out, lookupPort, Function.update_self, List.append_nil]; rfl
      | src | offset | width | saved | revDigit => rfl
    · intro k hk
      change Function.update s Port.digit _ k = Function.update (Function.update s (.addr .offset) _)
        (.addr .cellWidth) _ k
      have hd : k ≠ .digit := (hk .digit).symm
      have hw : k ≠ .addr .cellWidth := (hk .width).symm
      have ho : k ≠ .addr .offset := (hk .offset).symm
      rw [Function.update_of_ne hd, Function.update_of_ne hw, Function.update_of_ne ho]
  exact h₁.followedBy h₂

/-- A uniform fetch bound works across the full pair of loops. -/
theorem fetchTicks_le_cells {i t j Z : ℕ} (hi : i < t) (hj : j < Z) (ℓ : ℕ) :
    fetchTicks i Z j ℓ ≤ 19*(t*Z) + 13*(t*Z*ℓ) + 4 := by
  have h := EvaluatorDigitAddress.addressTicks_le_cells hi hj ℓ
  have h' := EvaluatorDigitAddress.cell_fits hi hj ℓ
  unfold fetchTicks EvaluatorDigitLookup.lookupTicks
  omega

theorem fetchTicks_le {i t j Z ℓ : ℕ} (hi : i < t) (hj : j < Z) (hℓ : 0 < ℓ) :
    fetchTicks i Z j ℓ ≤ 32*(t*Z*ℓ) + 4 := by
  have h := fetchTicks_le_cells hi hj ℓ
  have hc : t*Z ≤ t*Z*ℓ := by simpa using Nat.mul_le_mul_left (t*Z) hℓ
  omega

/-- Every intermediate stack of a fetch grows by at most a linear function
of the table dimensions, even with arbitrary callback registers in the bank. -/
theorem fetch_space [DecidableEq P] (data : List Bool) (t Z ℓ i j labelsLeft colsLeft : ℕ)
    (payload : Stacks P) (hi : i < t) (hj : j < Z) (fits : (i*Z+j)*ℓ+ℓ ≤ data.length)
    {n : ℕ} {q : Option (fetch (P := P)).State} {u : Stacks (Port P)}
    (run : StackRuns fetch.body.standalone n (some fetch.body.entry)
      (bank data t Z ℓ i j labelsLeft colsLeft payload) q u) (k : Port P) :
    (u k).length ≤ (bank data t Z ℓ i j labelsLeft colsLeft payload k).length +
      (19*(t*Z) + 13*(t*Z*ℓ) + 4) := by
  have hdone := fetch_runs data t Z ℓ i j labelsLeft colsLeft payload fits
  have hn := EvaluatorRadixDivision.ticks_le_at_return hdone (by rfl) run
  exact (EvaluatorRadixDivision.run_length run k).trans
    (Nat.add_le_add_left (hn.trans (fetchTicks_le_cells hi hj ℓ)) _)

end EvaluatorDigitFetch

end VPVNP
end Computability
end OAI
