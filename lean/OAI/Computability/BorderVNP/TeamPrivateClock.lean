import OAI.Computability.BorderVNP.TeamPrivateCompiler
import OAI.Computability.BorderVNP.TeamScales

/-! # The processor clock for compiled private tape calls

Each private call starts from the bits of its actual read words. Its loader, native steps,
and final cleanup together cost a fixed multiple of the private time bound. Summing these
costs over the calls of one processor and adding the local record operations gives the
elementary time used by the two-tape compiler.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateClock

open Filter TeamPrivateTape
open VPVNP.BurstRAM (Word)

variable {Q Γ : Type} {m g w n k : ℕ}

/-- One native path on the fixed-width words read by the team RAM. The table and its
entry may vary between calls on the same processor. -/
structure Path (Q Γ : Type) (m g w : ℕ) where
  /-- Native alphabet and its fixed bit-plane width. -/
  alphabet : Alphabet Γ g
  /-- Native symbol for each supplied binary digit. -/
  digit : Bool → Γ
  /-- Tape receiving the word interval. -/
  inputTape : Fin m
  /-- The private machine selected at this call. -/
  table : TapeTable Q Γ m
  /-- Entry state of the native call. -/
  start : Q
  /-- Words read from the burst interval in increasing address order. -/
  words : List (Word w)
  /-- Number of continuing native transitions on this path. -/
  time : ℕ
  /-- Choices taken at native nondeterministic branches. -/
  choices : List Bool
  /-- Signed terminal result. -/
  sign : Option Bool
  /-- The occupied tape cells at return, before cleanup. -/
  finalTapes : Fin (m*g) → Track
  /-- The actual path of the machine starting from these read words. -/
  run : TeamPrivateFragment.Run (trackTable alphabet table) time start
    (tracks alphabet (input alphabet.blank digit inputTape (TeamPrivateCall.inputBits words)))
    choices sign finalTapes

/-- Exact stack instructions in the compiled replay from raw input to clean signed return. -/
def Path.cost (p : Path Q Γ m g w) : ℕ :=
  TeamPrivateInput.steps g (TeamPrivateCall.inputBits p.words) +
    (p.time * (2*(m*g)+2) + 1 + TeamPrivateCleanup.steps (bank p.finalTapes))

/-- Machine-dependent constant for a private call, uniform in the binary input and clock. -/
def coefficient (m g : ℕ) : ℕ := (2*g+4) + (3*(m*g)+2) + (2*(m*g)+5)

/-- The cost counts an actual deterministic replay of the original branch choices. -/
theorem Path.replay (p : Path Q Γ m g w) (suffix : List Bool) :
    VPVNP.RAMTape.StackRuns (TeamPrivateFragment.replay
      (TeamPrivateCompiler.code p.alphabet p.digit p.inputTape p.table p.start)) p.cost
      (.load .start, p.choices ++ suffix) (TeamPrivateInput.initial (TeamPrivateCall.inputBits p.words))
      (.result p.sign, suffix) (fun _ => []) :=
  TeamPrivateCompiler.run_input p.alphabet p.digit p.inputTape p.table p.start _ p.run suffix

/-- A private call reading at most the rounded square-root burst of words and running
for at most the native time bound fits a fixed multiple of that bound in stack instructions. -/
theorem Path.cost_le (p : Path Q Γ m g w) (hn : 1 ≤ n) (hw : w ≤ n)
    (hq : p.words.length ≤ TeamScales.width n (1/2)) (ht : p.time ≤ n^25) :
    p.cost ≤ coefficient m g * n^25 := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hwidth : TeamScales.width n (1/2) ≤ n := by
    have h := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1/2 : ℝ) ≤ 1))
    simpa only [TeamScales.width, Real.rpow_one, Nat.floor_natCast] using h
  have hlen : (TeamPrivateCall.inputBits p.words).length ≤ n^25 := by
    rw [TeamPrivateCall.inputBits_length]
    calc
      _ ≤ n*n := Nat.mul_le_mul (hq.trans hwidth) hw
      _ = n^2 := (sq n).symm
      _ ≤ _ := Nat.pow_le_pow_right hn (by decide)
  have hc := TeamPrivateCompiler.run_input_cost_le p.alphabet p.digit p.inputTape p.table p.start _ p.run
  have h1 : 1 ≤ n^25 := one_le_pow₀ hn
  calc
    _ ≤ (2*g+4)*(TeamPrivateCall.inputBits p.words).length + p.time*(3*(m*g)+2) + 2*(m*g)+5 := hc
    _ ≤ (2*g+4)*n^25 + n^25*(3*(m*g)+2) + (2*(m*g)+5)*n^25 := by
      have hconst := Nat.mul_le_mul_left (2*(m*g)+5) h1
      have hinput := Nat.mul_le_mul_left (2*g+4) hlen
      have htime := Nat.mul_le_mul_right (3*(m*g)+2) ht
      omega
    _ = _ := by unfold coefficient; ring

/-- The sum of the exact private-path costs of a processor with at most one call per
local step is bounded by a fixed multiple of the twenty-sixth power of its length. -/
theorem private_sum_le (paths : Fin k → Path Q Γ m g w) (hn : 1 ≤ n) (hw : w ≤ n)
    (hk : k ≤ n) (hq : ∀ j, (paths j).words.length ≤ TeamScales.width n (1/2))
    (ht : ∀ j, (paths j).time ≤ n^25) :
    ∑ j, (paths j).cost ≤ coefficient m g * n^26 := by
  calc
    _ ≤ ∑ _ : Fin k, coefficient m g * n^25 := Finset.sum_le_sum fun j _ =>
      (paths j).cost_le hn hw (hq j) (ht j)
    _ = k * (coefficient m g * n^25) := by simp
    _ ≤ n * (coefficient m g * n^25) := Nat.mul_le_mul_right _ hk
    _ = _ := by ring

/-- Uniform physical clock for all processors of a fixed tape count and alphabet width.
The additional local work consists of at most a quadratic number of operations, each
using at most a fixed multiple of the fourth power of the processor length. -/
theorem eventually_processor_clock (m g ports c : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {w k records : ℕ} (paths : Fin k → Path Q Γ m g w)
      (other : Fin records → ℕ), w ≤ n → k ≤ n →
      (∀ j, (paths j).words.length ≤ TeamScales.width n (1/2)) →
      (∀ j, (paths j).time ≤ n^25) → records ≤ n^2 → (∀ j, other j ≤ c*n^4) →
      let T := (∑ j, (paths j).cost) + ∑ j, other j
      T * (6*(n+ports+T)+4) ≤ n^100 := by
  filter_upwards [eventually_ge_atTop 1, TeamStack.eventually_physical_clock
    (max (coefficient m g) c) ports] with n hn clock
  intro w k records paths other hw hk hq ht hr ho
  have hprivate := private_sum_le paths hn hw hk hq ht
  have hother : ∑ j, other j ≤ n^2*(c*n^4) := calc
    _ ≤ ∑ _ : Fin records, c*n^4 := Finset.sum_le_sum fun j _ => ho j
    _ = records*(c*n^4) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hr
  apply clock
  rw [Nat.mul_add]
  apply Nat.add_le_add
  · exact hprivate.trans (by
      rw [← Nat.pow_succ']
      exact Nat.mul_le_mul_right _ (le_max_left ..))
  · exact hother.trans (by
      rw [Nat.mul_left_comm]
      exact Nat.mul_le_mul_right _ (le_max_right ..))

end TeamPrivateClock

end BorderVNP
end Computability
end OAI
