import OAI.Computability.BorderVNP.TeamSignedControl
import OAI.Computability.VPVNP.RAMTapeCoefficient
import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Realizing signed finite-stack validators inside the universal processor

The signed path count of a fixed stack machine is realized by a single literal two-tape
program. A halt in a designated negative state writes the sign symbol. The quadratic physical
overhead is explicit, so the `n^25` private calls and polynomial local work of Lemma 7.1
fit the signed universal clock whenever their elementary stack steps meet its local bound.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamStack

open VPVNP.RAMTape VPVNP.UniversalMachine StackCompiler Filter

variable {k : ℕ} {Q : Type*}

/-- Signed leaves of a stack program. A control label fixes the sign on an accepting halt. -/
def paths {K : Type*} [DecidableEq K] (code : StackCode K Q) (neg : Q → Bool) : ℕ → Q → Stacks K → ℤ
  | 0, _, _ => 0
  | n + 1, q, s => match code q with
    | .push i b r => paths code neg n r (Function.update s i (b :: s i))
    | .pop i f => paths code neg n (f (s i).head?) (Function.update s i (s i).tail)
    | .goto r => paths code neg n r s
    | .choose low high => paths code neg n low s + paths code neg n high s
    | .halt accept => TeamTape.haltWeight accept (neg q)

/-- Only ready phases of the stack interpreter can reach a halt instruction. -/
def phaseNegative (neg : Q → Bool) : Phase k Q → Bool
  | .ready q => neg q
  | _ => false

variable [Fintype Q]

/-- The actual signed two-tape table for a finite stack machine. -/
noncomputable abbrev machine (code : StackCode (Fin k) Q) (neg : Q → Bool) (start : Q) : Program :=
  TeamTape.table (.ready start) (rows code) (phaseNegative neg)

private noncomputable abbrev physical (code : StackCode (Fin k) Q) (neg : Q → Bool) (start : Q)
    (ticks : ℕ) (q : Q) (s : Stacks (Fin k)) : ℤ :=
  TeamTape.value (.ready start) (rows code) (phaseNegative neg) ticks (.ready q)
    (tapeList (packed s)) (tapeList [])

private theorem physical_step (code : StackCode (Fin k) Q) (neg : Q → Bool) (start : Q)
    {t B ticks : ℕ} {q s r s'} (step : StackStep code q s r s') (size : (packed s).length+t+1 ≤ B)
    (clock : (t+1)*(6*B+4) ≤ ticks)
    (ih : ∀ left, (packed s').length+t ≤ B → t*(6*B+4) ≤ left →
      physical code neg start left r s' = paths code neg t r s') :
    physical code neg start ticks q s = paths code neg t r s' := by
  obtain ⟨d, hd, run⟩ := step_run code step
  have grow := step_size code step
  have bound : d ≤ 6*B+4 := by omega
  rw [Nat.succ_mul] at clock
  have he : ticks - d + d = ticks := by omega
  have hr := TeamTape.runs_value run (.ready start) (phaseNegative neg) (ticks-d)
  rw [he] at hr
  exact hr.trans (ih _ (by omega) (by omega))

/-- Every elementary stack path has its signed weight in the compiled machine, with the
same quadratic tape overhead as the unsigned compiler. -/
theorem physical_eq (code : StackCode (Fin k) Q) (neg : Q → Bool) (start : Q)
    (t : ℕ) (q : Q) (s : Stacks (Fin k)) (B ticks : ℕ)
    (stops : StopsWithin code t q s) (size : (packed s).length+t ≤ B) (clock : t*(6*B+4) ≤ ticks) :
    TeamTape.value (.ready start) (rows code) (phaseNegative neg) ticks (.ready q)
      (tapeList (packed s)) (tapeList []) = paths code neg t q s := by
  induction t generalizing q s ticks with
  | zero => exact stops.elim
  | succ t ih =>
    cases h : code q with
    | push i b r =>
      simp only [StopsWithin, h] at stops
      simp only [paths, h]
      exact physical_step code neg start (.push h) (by omega) clock (fun _ => ih _ _ _ stops)
    | pop i f =>
      simp only [StopsWithin, h] at stops
      simp only [paths, h]
      exact physical_step code neg start (.pop h) (by omega) clock (fun _ => ih _ _ _ stops)
    | goto r =>
      simp only [StopsWithin, h] at stops
      simp only [paths, h]
      exact physical_step code neg start (.goto h) (by omega) clock (fun _ => ih _ _ _ stops)
    | choose low high =>
      simp only [StopsWithin, h] at stops
      rw [Nat.succ_mul] at clock
      obtain ⟨ticks, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ticks ≠ 0)
      rw [TeamTape.value_step]
      simp only [rows, h, TeamTape.after, update_stay, paths]
      exact congrArg₂ Int.add (ih low s ticks stops.1 (by omega) (by omega))
        (ih high s ticks stops.2 (by omega) (by omega))
    | halt b =>
      rw [Nat.succ_mul] at clock
      obtain ⟨ticks, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ticks ≠ 0)
      rw [TeamTape.value_step]
      simp only [rows, h, TeamTape.after, phaseNegative, paths]

/-- On its own prefix and arbitrary payload the signed table contributes exactly its signed
stack path sum to the coefficient in (2.1). -/
theorem prefix_value (code : StackCode (Fin (k+1)) Q) (neg : Q → Bool) (start : Q)
    (payload : Word) (T : ℕ) :
    let P := machine code neg start
    let raw := programPrefix P ++ payload
    StopsWithin code T start (inputStacks raw) →
    T * (6 * (raw.length + (k+1) + T) + 4) ≤ raw.length^100 →
    signedCount raw.get = paths code neg T start (inputStacks raw) := by
  intro P raw stops clock
  simp only [signedCount, List.ofFn_get, raw, decode_programPrefix]
  change signedPaths P (raw.length^100) (initial (program code start) raw) = _
  rw [physical_initial]
  exact physical_eq code neg start T start (inputStacks raw) (raw.length+(k+1)+T) _ stops
    (by simp [packed_input]) clock

/-- The published local bound allows `n` private routines of `O(n^25)` elementary steps
and `O(n²)` record operations of `O(n⁴)` steps. Even after physical compilation, a single
length threshold for the fixed program puts every such path inside `n^100`. -/
theorem eventually_physical_clock (c ports : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ T : ℕ, T ≤ c * (n * n^25 + n^2 * n^4) →
      T * (6 * (n + ports + T) + 4) ≤ n^100 := by
  filter_upwards [eventually_ge_atTop (max 28 (max (2*c) ports))] with n hn
  have hn28 := (le_max_left ..).trans hn
  have hco := (le_max_left ..).trans ((le_max_right ..).trans hn)
  have hp := (le_max_right ..).trans ((le_max_right ..).trans hn)
  have hn1 : 1 ≤ n := by omega
  have hn27 : n ≤ n^27 := Nat.le_self_pow (by decide) _
  have six : n^6 ≤ n^26 := Nat.pow_le_pow_right hn1 (by decide)
  intro T hT
  rw [← Nat.pow_succ', ← pow_add] at hT
  have hb : T ≤ n^27 := calc
    _ ≤ c * (n^26 + n^26) := hT.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left six _))
    _ = (2*c)*n^26 := by ring
    _ ≤ n*n^26 := Nat.mul_le_mul_right _ hco
    _ = n^27 := (Nat.pow_succ' ..).symm
  calc
    _ ≤ n^27 * (28*n^27) := Nat.mul_le_mul hb (by omega)
    _ = 28 * n^54 := by ring
    _ ≤ n * n^54 := Nat.mul_le_mul_right _ hn28
    _ = n^55 := (Nat.pow_succ' ..).symm
    _ ≤ n^100 := Nat.pow_le_pow_right hn1 (by decide)

end TeamStack

end BorderVNP
end Computability
end OAI
