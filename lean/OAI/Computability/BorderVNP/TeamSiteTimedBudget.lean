import OAI.Computability.BorderVNP.TeamPrivateMeterCallCost
import OAI.Computability.BorderVNP.TeamSiteProcessorRowClock
import OAI.Computability.BorderVNP.TeamSiteTrustedClock

/-! # Physical site time with per-call trusted clock reset and cleanup

A private call pays for its actual bit string, its independently reset timer,
the physical tape interpreter and cleanup. The sum of these charges is covered
by the local logical block time. The site pays the clock-generation startup once.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedBudget

open VPVNP TeamPrivateTape TeamSite.Processor TeamPrivateMeterCall Filter

/-- Fixed constant for the concrete timed macro and its two dispatch jumps. -/
def meterCoefficient (m g : ℕ) := (2*g+4)+(2*g+9)+(3*((m+1)*g)+2)+(2*((m+1)*g)+12)

/-- The actual clocked stack run, including the two outer jumps, is bounded in its
original input size and the inclusive source timer. -/
theorem meter_steps {Q Γ : Type} {m g : ℕ} (M : Macro Q Γ m g) (mark : Γ) (bs : List Bool)
    (N : ℕ) {steps choices out u}
    (native : TeamPrivateFragment.Run (trackTable M.alphabet (TeamPrivateTimeout.table M.alphabet.blank mark M.table))
      steps M.start (timedInput M mark bs N) choices out u) (cap : steps ≤ N+1) :
    TeamPrivateMeterCall.steps bs N steps u+2 ≤ meterCoefficient m g*(N+1+bs.length) := by
  let total := N+1+bs.length
  have data : bs.length ≤ total := by dsimp [total]; omega
  have reset : N ≤ total := by dsimp [total]; omega
  have exec : steps ≤ total := cap.trans (Nat.le_add_right ..)
  have unit : 1 ≤ total := by dsimp [total]; omega
  have head := TeamPrivateMeterCall.steps_le M mark bs N native
  calc
    _ ≤ (2*g+4)*bs.length+(2*g+9)*N+steps*(3*((m+1)*g)+2)+(2*((m+1)*g)+12) := by omega
    _ ≤ (2*g+4)*total+(2*g+9)*total+(3*((m+1)*g)+2)*total+(2*((m+1)*g)+12)*total := by
      apply Nat.add_le_add
      · apply Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ data) (Nat.mul_le_mul_left _ reset))
        rw [Nat.mul_comm steps]
        exact Nat.mul_le_mul_left _ exec
      · simpa using Nat.mul_le_mul_left (2*((m+1)*g)+12) unit
    _ = _ := by simp [meterCoefficient,Nat.add_mul,total]

/-- At most one timed call is charged per source instruction. A burst of `q` words
contributes exactly `q*w` input bits in the physical word spelling. -/
def calls {w : ℕ} (K N : ℕ) (es : List (TeamRAM.Event w)) : ℕ :=
  (es.map fun z => K*(N+1+z.action.extra*w)).sum

/-- All private resets and burst moves are covered by the same logical charge used by the scheduler. -/
theorem calls_le {w : ℕ} (K N : ℕ) (es : List (TeamRAM.Event w)) :
    calls K N es ≤ TeamTapeHandoff.cost es * (K*(N+1+w)) := by
  induction es with
  | nil => simp [calls,TeamTapeHandoff.cost,RAMBuckets.cost]
  | cons z es ih =>
    change K*(N+1+z.action.extra*w)+calls K N es ≤ (1+z.action.extra+TeamTapeHandoff.cost es)*_
    rw [Nat.add_mul]
    apply Nat.add_le_add _ ih
    rw [Nat.mul_left_comm (1+z.action.extra) K]
    apply Nat.mul_le_mul_left
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_add]
    omega

/-- The clock for the actual instruction block with metered private callbacks.
Charging the original instruction loop as well includes all register guards,
record emission, finite-PC handoffs and the terminal fetch. -/
def body {w : ℕ} (m g K N : ℕ) (es : List (TeamRAM.Event w)) :=
  Row.nativeCost w m g (N+1) es + calls K N es

/-- A pointwise bound at the paper's exact per-private-call cutoff, independent of
the number or placement of the calls within the block. -/
theorem body_le {w n : ℕ} (m g K : ℕ) (es : List (TeamRAM.Event w)) (hn : 1 ≤ n)
    (width : w ≤ n) (charge : TeamTapeHandoff.cost es ≤ n) :
    body m g K (n^25) es ≤ (Work.coefficient m g+4500+3*K)*n^26 := by
  have p : n ≤ n^25 := Nat.le_self_pow (by decide) n
  have c : n^25+1+w ≤ 3*n^25 := by omega
  have overhead := (calls_le K (n^25) es).trans (Nat.mul_le_mul charge (Nat.mul_le_mul_left K c))
  have coef : n*(K*(3*n^25)) = (3*K)*n^26 := by ring
  exact (Nat.add_le_add (Work.chunk_budget_le m g es hn width le_rfl charge)
    (overhead.trans_eq coef)).trans_eq (Nat.add_mul _ _ _).symm

/-- The entire concrete row fits under the inner site clock, leaving room for the
trusted input-dependent `n^25`-timer preparation within the outer `n^36` horizon. -/
theorem eventually_row (r k m g K : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {w d e dataLength : ℕ} (es : List (TeamRAM.Event w)) (rowCount : ℕ) (last : Bool),
      w+1 ≤ n → 2^e ≤ n → 2+e+d ≤ n → dataLength ≤ n → TeamTapeHandoff.cost es ≤ n →
      let t := Budget.total r k n d e w dataLength (body m g K (n^25) es) rowCount last
      t ≤ n^35 ∧ t+TeamClocked.prepSteps 25 n ≤ n^36 := by
  filter_upwards [eventually_ge_atTop 4000010,eventually_ge_atTop (r+2),eventually_ge_atTop (k+8),
    eventually_ge_atTop (Work.coefficient m g+4500+3*K),TrustedClock.eventually_prep_room] with n big hr hk coeff prep
  intro w d e dataLength es rowCount last hw capacity dim data charge t
  have positive : 1 ≤ n := by omega
  have inner := (body_le m g K es positive (by omega) charge).trans (Nat.mul_le_mul_right (n^26) coeff)
  have fit : body m g K (n^25) es ≤ n^28 := by
    apply inner.trans
    rw [← pow_succ']
    exact Nat.pow_le_pow_right positive (by decide)
  have spent : t ≤ n^35 := (Budget.total_le rowCount last big hr hk hw capacity dim data fit).trans
    (Nat.pow_le_pow_right positive (by decide))
  exact ⟨spent,(Nat.add_le_add_right spent _).trans prep⟩

end TeamSite.TimedBudget

end BorderVNP
end Computability
end OAI
