import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic

/-!
# Geometric dovetailing of fenced multiplication attempts

Round `s` runs indices `i = 0, …, s-1` from scratch for `2^(s-1-i)` interpreter
ticks each. Index zero is reserved for schoolbook multiplication. A round accepts
its first completed answer. Generation, input copying, splitting into chunks and
tentative output can all be states of the same tick function. A rejected attempt
(e.g. a fence crossing) has no answer. The results here concern the scheduling
algorithm on interpreter ticks and its accounting interface for physical costs.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Schedule

variable {σ α : Type*}

/-- The candidate may finish, take another tick, or abort the current attempt. -/
inductive Tick (σ α : Type*) where
  | more (next : σ)
  | done (answer : α)
  | abort

/-- Run at most the specified number of interpreter transitions. -/
def tryFor (tick : σ → Tick σ α) : ℕ → σ → Option α
  | 0, _ => none
  | b + 1, st =>
    match tick st with
    | .more st' => tryFor tick b st'
    | .done x => some x
    | .abort => none

theorem tryFor_mono {tick : σ → Tick σ α} {b c : ℕ} {st : σ} {x : α}
    (hb : b ≤ c) (h : tryFor tick b st = some x) : tryFor tick c st = some x := by
  induction b generalizing c st with
  | zero => simp [tryFor] at h
  | succ b ih =>
    cases c with
    | zero => omega
    | succ c =>
      cases hstep : tick st with
      | abort => simp [tryFor, hstep] at h
      | done z => simpa [tryFor, hstep] using h
      | more st' =>
        simp only [tryFor, hstep] at h ⊢
        exact ih (Nat.le_of_succ_le_succ hb) h

/-- Index zero is the fallback. Each pair `(j+1,k)` selects template `j+1`
and a split into `2^k` chunks. -/
def parameters : ℕ → Option (ℕ × ℕ)
  | 0 => none
  | i + 1 => some ((Nat.unpair i).1 + 1, (Nat.unpair i).2)

theorem parameters_pair (j k : ℕ) :
    parameters (Nat.pair j k + 1) = some (j+1, k) := by
  simp [parameters]

/-- `slots trial i k` tries `k` candidates, starting at index `i`. -/
def slots (trial : ℕ → ℕ → Option α) (i : ℕ) : ℕ → Option α
  | 0 => none
  | k + 1 =>
    match trial i (2^k) with
    | some x => some x
    | none => slots trial (i+1) k

theorem slots_sound {P : α → Prop} {trial : ℕ → ℕ → Option α}
    (h : ∀ i b x, trial i b = some x → P x) {i k : ℕ} {x : α}
    (hx : slots trial i k = some x) : P x := by
  induction k generalizing i with
  | zero => simp [slots] at hx
  | succ k ih =>
    cases hstep : trial i (2^k) with
    | none => exact ih (by simpa [slots, hstep] using hx)
    | some y =>
      have : y = x := by simpa [slots, hstep] using hx
      exact this ▸ h i _ _ hstep

theorem slots_has_answer {trial : ℕ → ℕ → Option α} (i d a : ℕ)
    (h : (trial (i+d) (2^a)).isSome) :
    (slots trial i (d+a+1)).isSome := by
  induction d generalizing i with
  | zero =>
    simp only [Nat.zero_add, Nat.add_zero] at h ⊢
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    simp [slots, hx]
  | succ d ih =>
    have hd : (d+1)+a+1 = (d+a+1)+1 := by omega
    rw [hd, slots]
    cases trial i (2^(d+a+1)) with
    | none => exact ih (i+1) (by rwa [show (i+1)+d = i+(d+1) by omega])
    | some => rfl

/-- First answer from the first `s` rounds, or `none` if none has halted yet. -/
def through (trial : ℕ → ℕ → Option α) : ℕ → Option α
  | 0 => none
  | s + 1 =>
    match through trial s with
    | some x => some x
    | none => slots trial 0 (s+1)

theorem through_sound {P : α → Prop} {trial : ℕ → ℕ → Option α}
    (h : ∀ i b x, trial i b = some x → P x) {s : ℕ} {x : α}
    (hx : through trial s = some x) : P x := by
  induction s with
  | zero => simp [through] at hx
  | succ s ih =>
    cases hs : through trial s with
    | none => exact slots_sound h (by simpa [through, hs] using hx)
    | some y =>
      have : y = x := by simpa [through, hs] using hx
      subst y
      exact ih hs

theorem through_mono {trial : ℕ → ℕ → Option α} {s t : ℕ} {x : α}
    (hs : s ≤ t) (h : through trial s = some x) : through trial t = some x := by
  induction hs with
  | refl => exact h
  | step _ ih => simp [through, ih]

/-- By round `i + ceil(log₂ t) + 1` a candidate taking `t` ticks has had enough time,
unless an earlier candidate has already produced the answer. -/
theorem through_has_answer {tick : σ → Tick σ α} {start : ℕ → σ} {i t : ℕ} {x : α}
    (hrun : tryFor tick t (start i) = some x) :
    (through (fun j b => tryFor tick b (start j)) (i + Nat.clog 2 t + 1)).isSome := by
  let trial := fun j b => tryFor tick b (start j)
  have hslot : (slots trial 0 (i + Nat.clog 2 t + 1)).isSome := by
    apply slots_has_answer 0 i (Nat.clog 2 t)
    simp only [Nat.zero_add]
    change (tryFor tick (2 ^ Nat.clog 2 t) (start i)).isSome
    rw [tryFor_mono (Nat.le_pow_clog (by decide : 1 < 2) t) hrun]
    rfl
  change (through trial (i + Nat.clog 2 t + 1)).isSome
  rw [through]
  cases through trial (i + Nat.clog 2 t) with
  | none => exact hslot
  | some => rfl

/-- An upper bound for a full round's attempt costs, allowing a different charge
for each candidate and clock exponent, including cleanup after a timeout. -/
def slotCost (charge : ℕ → ℕ → ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => charge i k + slotCost charge (i+1) k

theorem slotCost_le {charge : ℕ → ℕ → ℕ} (C : ℕ)
    (hc : ∀ i a, charge i a ≤ C * 2^a) (i k : ℕ) :
    slotCost charge i k + C ≤ C * 2^k := by
  induction k generalizing i with
  | zero => simp [slotCost]
  | succ k ih =>
    have h := Nat.add_le_add (hc i k) (ih (i+1))
    simpa [slotCost, Nat.add_assoc, pow_succ, Nat.mul_assoc, Nat.mul_two, Nat.mul_add] using h

/-- Cumulative cost for the first `s` rounds, including per-round bookkeeping. -/
def prefixCost (cost : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | s+1 => prefixCost cost s + cost (s+1)

theorem prefixCost_le {cost : ℕ → ℕ} (C : ℕ) (h : ∀ s, cost s ≤ C * 2^s) (s : ℕ) :
    prefixCost cost s + 2 * C ≤ 2 * C * 2^s := by
  induction s with
  | zero => simp [prefixCost]
  | succ s ih =>
    have hc := h (s+1)
    simp only [prefixCost, pow_succ] at hc ⊢
    nlinarith [mul_comm C (2^s : ℕ)]

theorem ceil_pow_le (t : ℕ) : 2 ^ Nat.clog 2 t ≤ 2 * (t+1) := by
  by_cases h : 1 < t
  · have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) h
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.clog_pos (by decide : 1 < 2) h).ne'
    rw [hk] at hpred ⊢
    simp only [Nat.pred_succ] at hpred
    rw [pow_succ]
    omega
  · simp only [Nat.clog_of_right_le_one (by omega : t ≤ 1), pow_zero]
    omega

/-- A successful candidate bounds the resources of the *same* schedule for every
choice of `i`. No information about its running time or index is passed to the
round scheduler. The finite prefix here is an upper bound on the time to its first answer. -/
theorem uniform_schedule_bound {tick : σ → Tick σ α} {start : ℕ → σ}
    {cost : ℕ → ℕ} {C i t : ℕ} {x : α}
    (hcost : ∀ s, cost s ≤ C * 2^s) (hrun : tryFor tick t (start i) = some x) :
    ∃ s, (through (fun j b => tryFor tick b (start j)) s).isSome ∧
      prefixCost cost s ≤ 8 * C * 2^i * (t+1) := by
  refine ⟨i + Nat.clog 2 t + 1, through_has_answer hrun, ?_⟩
  have h := prefixCost_le C hcost (i + Nat.clog 2 t + 1)
  calc
    _ ≤ 2 * C * 2 ^ (i + Nat.clog 2 t + 1) := by omega
    _ = (4 * C * 2^i) * 2 ^ Nat.clog 2 t := by rw [pow_succ, pow_add]; ring
    _ ≤ (4 * C * 2^i) * (2*(t+1)) := Nat.mul_le_mul_left _ (ceil_pow_le t)
    _ = _ := by ring

end Schedule

end NearSquareRoot
end Computability
end OAI
