import OAI.Computability.VPVNP.UniversalCountStack

/-!
# Time and space for the witness enumerator

For a verifier using at most `B` steps per witness, the counter makes exactly
one call per binary word. The bound on the height of every stack is independent
of the number of calls. This follows by restarting the space estimate at each
call boundary, where the counters have their original widths and the auxiliary
stacks have their original contents.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalCountStack

open RAMTape TapeWord RAMTape.UnaryWord BurstRAM

variable {K Q : Type*} [DecidableEq K]

/-- Every stack in every intermediate configuration has length at most `cap`. -/
inductive SpaceRun (code : StackCode K Q) (cap : ℕ) : ℕ → Q → Stacks K → Q → Stacks K → Prop
  | nil (q : Q) (s : Stacks K) (hs : ∀ k, (s k).length ≤ cap) : SpaceRun code cap 0 q s q s
  | cons {q s q' s' n t u} (hs : ∀ k, (s k).length ≤ cap) :
      StackStep code q s q' s' → SpaceRun code cap n q' s' t u →
      SpaceRun code cap (n + 1) q s t u

theorem SpaceRun.runs {code : StackCode K Q} {cap n q s t u} (h : SpaceRun code cap n q s t u) :
    StackRuns code n q s t u := by
  induction h with
  | nil => exact .nil ..
  | cons _ step _ ih => exact .cons step ih

theorem SpaceRun.trans {code : StackCode K Q} {cap a b q s q' s' t u}
    (h : SpaceRun code cap a q s q' s') (g : SpaceRun code cap b q' s' t u) :
    SpaceRun code cap (a + b) q s t u := by
  induction h with
  | nil => simpa using g
  | cons hs step _ ih => simpa only [Nat.succ_add] using SpaceRun.cons hs step (ih g)

private theorem step_length {code : StackCode K Q} {q s q' s'}
    (h : StackStep code q s q' s') (k : K) : (s' k).length ≤ (s k).length + 1 := by
  cases h with
  | push =>
    rename_i j b _
    by_cases e : k = j <;> simp [e]
  | pop =>
    rename_i j f _
    by_cases e : k = j <;> simp [e]
    omega
  | goto => omega

theorem spaceRun_of_steps {code : StackCode K Q} {cap n q s t u}
    (h : StackRuns code n q s t u) (hs : ∀ k, (s k).length + n ≤ cap) : SpaceRun code cap n q s t u := by
  induction h with
  | nil => exact .nil _ _ (by simpa using hs)
  | cons step _ ih =>
    refine .cons (fun k => by have := hs k; omega) step (ih fun k => ?_)
    have := step_length step k
    have := hs k
    omega

/-- The low `w` bits in the same order as the finite Boolean witness. -/
def digits (w i : ℕ) : List Bool := wordBits (Fin.ofNat (2 ^ w) i)

@[simp] theorem length_digits (w i : ℕ) : (digits w i).length = w := length_wordBits _

@[simp] theorem value_digits (w i : ℕ) : value (digits w i) = i % (2 ^ w) := by
  rw [digits, value_wordBits, Fin.val_ofNat]

theorem digits_zero (w : ℕ) : digits w 0 = List.replicate w false :=
  eq_of_length_value (by simp) (by simp)

private theorem inc_digits (w i : ℕ) (b : Bool) (hi : i < 2^w) :
    (incScan b (digits w i)).1 = digits w (i + b.toNat) ∧
    ((incScan b (digits w i)).2 = true ↔ 2^w ≤ i + b.toNat) := by
  have h := incScan_value b (digits w i)
  rw [length_digits, value_digits, Nat.mod_eq_of_lt hi] at h
  have hlen := incScan_length b (digits w i)
  rw [length_digits] at hlen
  have hlt := value_lt (incScan b (digits w i)).1
  rw [hlen] at hlt
  constructor
  · apply eq_of_length_value (by simp [hlen])
    rw [value_digits, ← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · cases hc : (incScan b (digits w i)).2 <;> simp [hc] at h ⊢ <;> omega

/-- Applies the witness predicate to the low w bits of the given index in little-endian order. -/
def testAt {w : ℕ} (f : (Fin w → Bool) → Bool) (i : ℕ) : Bool :=
  f (RAMSerialization.wordBits w (Fin.ofNat (2 ^ w) i))

private def tally {w : ℕ} (f : (Fin w → Bool) → Bool) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, (testAt f j).toNat

private theorem tally_succ {w : ℕ} (f : (Fin w → Bool) → Bool) (i : ℕ) :
    tally f (i+1) = tally f i + (testAt f i).toNat := Finset.sum_range_succ ..

private theorem tally_le {w : ℕ} (f : (Fin w → Bool) → Bool) (i : ℕ) : tally f i ≤ i := by
  induction i with
  | zero => simp [tally]
  | succ i ih => rw [tally_succ]; cases testAt f i <;> simp <;> omega

private theorem tally_all {w : ℕ} (f : (Fin w → Bool) → Bool) :
    tally f (2^w) = ∑ bits, (f bits).toNat := by
  rw [tally, Finset.sum_range]
  have cast (i : Fin (2^w)) : Fin.ofNat (2^w) i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simp only [testAt, cast]
  exact (RAMSerialization.wordBits w).sum_comp (fun bits => (f bits).toNat)

variable {v : Routine (Port K) Q} {aux : Stacks K} {B A w : ℕ} {f : (Fin w → Bool) → Bool}

/-- A full run returns the numeric count in a `w + 1` bit register. The
control remains fixed across word lengths and verifier inputs. Each individual
stack stays within the stated space bound throughout the run. -/
theorem enumerate_runs (haux : ∀ k, (aux k).length ≤ A)
    (hv : ∀ (bits : Fin w → Bool) (count : List Bool), count.length = w + 1 →
      ∃ t ≤ B, v.Runs t (bank aux (List.ofFn bits) count [] [])
        (bank aux (List.ofFn bits) count [] [f bits])) :
    ∃ t ≤ 2 ^ w * (B + 8 * w + 9),
      SpaceRun (enumerate v).standalone (max A (w+1) + (B + 8*w + 9)) t
        (some (enumerate v).entry) (bank aux (digits w 0) (digits (w+1) 0) [] []) none
        (bank aux (digits w 0) (digits (w+1) (∑ bits, (f bits).toNat)) [] []) := by
  let bound := B + 8*w + 9
  let cap := max A (w+1) + bound
  let state (j : ℕ) := bank aux (digits w j) (digits (w+1) (tally f j)) [] []
  let pc (j : ℕ) := if j = 2^w then none else some (enumerate v).entry
  have hs (j : ℕ) (k : Port K) : (state j k).length ≤ max A (w+1) := by
    cases k with
    | aux k => exact (haux k).trans (le_max_left ..)
    | choice => simp [state, bank]
    | total => simp [state, bank]
    | scratch | flag => simp [state, bank]
  have loop (rem j : ℕ) (hr : j + rem = 2^w) :
      ∃ t ≤ rem * bound, SpaceRun (enumerate v).standalone cap t (pc j) (state j)
        none (state (2^w)) := by
    induction rem generalizing j with
    | zero =>
      simp only [Nat.add_zero] at hr
      subst j
      refine ⟨0, by simp, ?_⟩
      rw [show pc (2^w) = none by simp [pc]]
      exact .nil _ _ (fun k => (hs _ k).trans (Nat.le_add_right ..))
    | succ rem ih =>
      have hj : j < 2^w := by omega
      let bits := RAMSerialization.wordBits w (Fin.ofNat (2^w) j)
      obtain ⟨t, ht, verified⟩ := hv bits (digits (w+1) (tally f j)) (length_digits ..)
      have hfit : tally f j < 2^(w+1) := by
        have := tally_le f j
        rw [pow_succ]
        omega
      have hc := inc_digits w j true hj
      have ha := inc_digits (w+1) (tally f j) (testAt f j) hfit
      simp only [Bool.toNat_true] at hc
      have run := iteration_run verified
      have hb : List.ofFn bits = digits w j := rfl
      have he : f bits = testAt f j := rfl
      rw [hb, he, length_digits, length_digits, hc.1, ha.1, ← tally_succ] at run
      have hov : (incScan true (digits w j)).2 = true ↔ j+1 = 2^w := by
        rw [hc.2]
        omega
      simp only [hov] at run
      have step : StackRuns (enumerate v).standalone (t+4*(w+1)+4*w+5) (pc j) (state j)
          (pc (j+1)) (state (j+1)) := by simpa only [pc, ite_eq_right hj.ne, state] using run
      have hd : t+4*(w+1)+4*w+5 ≤ bound := by dsimp [bound]; omega
      have bounded := spaceRun_of_steps (cap := cap) step (fun k => Nat.add_le_add (hs j k) hd)
      obtain ⟨u, hu, rest⟩ := ih (j+1) (by omega)
      refine ⟨_, ?_, bounded.trans rest⟩
      exact (Nat.add_le_add hd hu).trans_eq ((Nat.add_comm ..).trans (Nat.succ_mul ..).symm)
  have h := loop (2^w) 0 (Nat.zero_add _)
  have hp : 0 < 2^w := pow_pos (by decide) _
  have hz : digits w (2^w) = digits w 0 := eq_of_length_value (by simp) (by simp)
  have t0 : tally f 0 = 0 := by simp [tally]
  simpa only [pc, ite_eq_right hp.ne, state, tally_all, hz, t0,
    bound, cap] using h

end UniversalCountStack

end VPVNP
end Computability
end OAI
