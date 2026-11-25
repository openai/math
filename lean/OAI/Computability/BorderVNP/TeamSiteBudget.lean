import OAI.Computability.BorderVNP.TeamSiteRun

/-! # Elementary clock for an entire signed processor instruction segment

Each successful instruction includes physical dispatch, its actual callback and
the timestamp reset. Their costs add over a block. Both the number of calls and
the total number of burst words are bounded by the block's logical charge.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Work

open VPVNP Filter

/-- Total physical stack-instruction bound for a given block of local events. -/
def chunkBudget (w m g fuel : ℕ) (es : List (TeamRAM.Event w)) : ℕ :=
  (es.map fun e => instructionBudget w m g fuel e.action.extra).sum

@[simp] theorem chunkBudget_nil (w m g fuel : ℕ) :
    chunkBudget w m g fuel ([] : List (TeamRAM.Event w)) = 0 := rfl

@[simp] theorem chunkBudget_cons (w m g fuel : ℕ) (e : TeamRAM.Event w) (es : List (TeamRAM.Event w)) :
    chunkBudget w m g fuel (e::es) = instructionBudget w m g fuel e.action.extra + chunkBudget w m g fuel es := rfl

/-- Per logical tick, bound the instruction's overhead, native clock and data movement. -/
def tickBudget (w m g fuel : ℕ) : ℕ :=
  instructionBudget w m g fuel 0 + (2*g+4)*w

theorem step_le_ticks (w m g fuel q : ℕ) :
    instructionBudget w m g fuel q ≤ (1+q)*tickBudget w m g fuel := by
  unfold tickBudget instructionBudget eventBudget
  ring_nf
  omega

/-- Total elementary cost follows from the same sum of `1+q` that is checked
by the real instruction clock. No separate bound on the number of probes is needed. -/
theorem chunk_le_ticks {w : ℕ} (m g fuel : ℕ) (es : List (TeamRAM.Event w)) :
    chunkBudget w m g fuel es ≤ TeamTapeHandoff.cost es * tickBudget w m g fuel := by
  induction es with
  | nil => simp [TeamTapeHandoff.cost,RAMBuckets.cost]
  | cons e es ih =>
    rw [chunkBudget_cons,show TeamTapeHandoff.cost (e::es) = 1+e.action.extra+TeamTapeHandoff.cost es from rfl,
      Nat.add_mul]
    exact Nat.add_le_add (step_le_ticks ..) ih

/-- The terminal fetch and possible deterministic range rejection. -/
def closeBudget (w : ℕ) : ℕ :=
  1050*(w+1)^2 + 1 + TeamBurstCallback.rejectCost w

/-- Fixed coefficient for the per-tick estimate of this machine, independent of
word width, processor index, register values and the choices made on the path. -/
def coefficient (m g : ℕ) := 7000 + 2*g + 12*(m*g)

private theorem tick_budget_le {w n fuel : ℕ} (m g : ℕ) (hn : 1 ≤ n) (hw : w ≤ n) (hf : fuel ≤ n^25+1) :
    tickBudget w m g fuel ≤ coefficient m g * n^25 := by
  have one : 1 ≤ n^25 := one_le_pow₀ hn
  have lin : n ≤ n^25 := Nat.le_self_pow (by decide) n
  have sq : n^2 ≤ n^25 := Nat.pow_le_pow_right hn (by decide)
  have le1 : w+1 ≤ 2*n := by omega
  have le2 : (w+1)^2 ≤ 4*n^2 := by simpa only [mul_pow, Nat.reducePow] using Nat.pow_le_pow_left le1 2
  have h₁ : 1050*(w+1)^2 ≤ 4200*n^25 := by
    calc _ ≤ 1050*(4*n^2) := Nat.mul_le_mul_left _ le2
         _ ≤ 1050*(4*n^25) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ sq)
         _ = _ := by ring
  have h₂ : 1200*(w+1) ≤ 2400*n^25 := by omega
  have h₃ : (fuel+1)*(3*(m*g)+2) ≤ (3*n^25)*(3*(m*g)+2) :=
    Nat.mul_le_mul_right _ (by omega)
  have h₄ : (2*g+4)*w ≤ (2*g+4)*n^25 := Nat.mul_le_mul_left _ (hw.trans lin)
  have h₅ : 2*(m*g)+20 ≤ (2*(m*g)+20)*n^25 := Nat.le_mul_of_pos_right _ (by omega)
  unfold tickBudget instructionBudget eventBudget coefficient
  simp only [Nat.zero_add,Nat.mul_one,Nat.zero_mul,Nat.mul_zero,Nat.add_zero]
  ring_nf at h₁ h₂ h₃ h₄ h₅ ⊢
  omega

private theorem close_le {w n : ℕ} (hn : 1 ≤ n) (hw : w ≤ n) : closeBudget w ≤ 4500*n^25 := by
  have one : 1 ≤ n^25 := one_le_pow₀ hn
  have lin : n ≤ n^25 := Nat.le_self_pow (by decide) n
  have sq : n^2 ≤ n^25 := Nat.pow_le_pow_right hn (by decide)
  have lin' : w+1 ≤ 2*n := by omega
  have sq' : (w+1)^2 ≤ 4*n^2 := by simpa only [mul_pow,Nat.reducePow] using Nat.pow_le_pow_left lin' 2
  unfold closeBudget TeamBurstCallback.rejectCost
  omega

/-- Every admitted local path, including its terminal fetch, fits a fixed multiple
of the twenty-sixth power of the input length. A private native step bound of
`n^25` may use `n^25+1` clock checks to include the final halt. -/
theorem chunk_budget_le {w n fuel : ℕ} (m g : ℕ) (es : List (TeamRAM.Event w)) (hn : 1 ≤ n)
    (hw : w ≤ n) (hf : fuel ≤ n^25+1) (logical : TeamTapeHandoff.cost es ≤ n) :
    chunkBudget w m g fuel es + closeBudget w ≤ (coefficient m g+4500)*n^26 := by
  have h := (chunk_le_ticks m g fuel es).trans (Nat.mul_le_mul logical (tick_budget_le m g hn hw hf))
  have close := (close_le hn hw).trans (Nat.mul_le_mul_left 4500 (Nat.pow_le_pow_right hn (by decide : 25 ≤ 26)))
  calc
    _ ≤ n * (coefficient m g*n^25) + 4500*n^26 := Nat.add_le_add h close
    _ = _ := by ring

/-- The width, events, native clock, and all choices may vary with the site. Only
the fixed tape architecture contributes to the threshold for the physical bound. -/
theorem eventually_chunk_budget (m g : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {w fuel : ℕ} (es : List (TeamRAM.Event w)), w ≤ n →
      fuel ≤ n^25+1 → TeamTapeHandoff.cost es ≤ n → chunkBudget w m g fuel es + closeBudget w ≤ n^27 := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (coefficient m g+4500)] with n hn hc
  intro w fuel es hw hf bound
  calc
    _ ≤ (coefficient m g+4500)*n^26 := chunk_budget_le m g es hn hw hf bound
    _ ≤ n*n^26 := Nat.mul_le_mul_right _ hc
    _ = _ := by ring

end TeamSite.Work

end BorderVNP
end Computability
end OAI
