import OAI.Computability.VPVNP.RAMLocalRun

/-!
# Pathwise work of a local RAM call

The bounds hold for every supplied bit stream, including a stream that ends
during a read, and every private state. A branch reserves one bit and a
permitted read reserves one word. The instruction and probe counters bound
the sum of these charges independently of whether the call succeeds.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*}

private structure LocalCallRun.Within (t : LocalCallRun w) (fuel allowance : ℕ) : Prop where
  instructions_le : t.instructions ≤ fuel
  probes_le : t.probes ≤ allowance
  probes_le_instructions : t.probes ≤ t.instructions
  guessWork_le : t.guessWork ≤ t.instructions + w * t.probes

private theorem LocalCallRun.Within.prepend {t : LocalCallRun w} {fuel allowance : ℕ}
    (h : t.Within fuel allowance) (e : Event w) :
    (t.prepend e).Within (fuel + 1) (e.probeCharge + allowance) := by
  obtain ⟨hi, hp, hpi, hg⟩ := h
  have hcharge : e.probeCharge ≤ 1 := by cases e <;> simp [Event.probeCharge]
  have hwidth : e.guessWidth ≤ 1 + w * e.probeCharge := by
    cases e <;> simp [Event.probeCharge, Event.guessWidth]
  constructor <;> simp only [LocalCallRun.prepend, Nat.mul_add] <;> omega

private theorem runLocalCall_within (P : Program w C) (fuel : ℕ) (c : C)
    (allowance : ℕ) (bits : List Bool) :
    (runLocalCall P fuel c allowance bits).Within fuel allowance := by
  induction fuel generalizing c allowance bits with
  | zero => constructor <;> simp [runLocalCall]
  | succ f ih =>
    cases hs : P.step c with
    | localStep c' =>
      simpa [runLocalCall, hs, Event.probeCharge] using (ih c' allowance bits).prepend .tick
    | branch next =>
      cases bits with
      | nil => constructor <;> simp [runLocalCall, hs, LocalCallRun.stop]
      | cons b bs =>
        simpa [runLocalCall, hs, Event.probeCharge] using
          (ih (next b) allowance bs).prepend (.choice b)
    | read a next =>
      cases allowance with
      | zero => constructor <;> simp [runLocalCall, hs, LocalCallRun.stop]
      | succ p =>
        cases hb : takeWord w bits with
        | none => constructor <;> simp [runLocalCall, hs, hb, LocalCallRun.stop]
        | some val =>
          obtain ⟨v, bs⟩ := val
          simpa [runLocalCall, hs, hb, Event.probeCharge, Nat.one_add] using
            (ih (next v) p bs).prepend (.read a v)
    | write a v c' =>
      cases allowance with
      | zero => constructor <;> simp [runLocalCall, hs, LocalCallRun.stop]
      | succ p =>
        simpa [runLocalCall, hs, Event.probeCharge, Nat.one_add] using
          (ih c' p bits).prepend (.write a v)
    | finish s => constructor <;> simp [runLocalCall, hs, LocalCallRun.stop]
    | reject => constructor <;> simp [runLocalCall, hs, LocalCallRun.stop]

/-- Pathwise bounds on dispatches, charged probes and reserved bit slots. -/
theorem runLocalCall_bounds (P : Program w C) (fuel : ℕ) (c : C)
    (allowance : ℕ) (bits : List Bool) :
    let t := runLocalCall P fuel c allowance bits
    t.instructions ≤ fuel ∧ t.probes ≤ allowance ∧
      t.guessWork ≤ t.instructions + w * t.probes := by
  obtain ⟨hi, hp, _, hg⟩ := runLocalCall_within P fuel c allowance bits
  exact ⟨hi, hp, hg⟩

/-- Counting one unit per dispatch, per charged probe and per reserved bit. -/
theorem runLocalCall_totalWork_le (P : Program w C) (fuel : ℕ) (c : C)
    (allowance : ℕ) (bits : List Bool) :
    let t := runLocalCall P fuel c allowance bits
    t.instructions + t.probes + t.guessWork ≤ 3 * fuel + w * allowance := by
  obtain ⟨hi, hp, hpi, hg⟩ := runLocalCall_within P fuel c allowance bits
  have := Nat.mul_le_mul_left w hp
  dsimp only
  omega

/-- The startup unit leaves one fewer probe slot in each of the three
allowances. If any allowance is zero the call uses no slots at all. -/
theorem runChargedCall_bounds (P : Program w C) (fuel : ℕ) (c : C)
    (callLeft globalLeft siteLeft : ℕ) (bits : List Bool) :
    let t := runChargedCall P fuel c callLeft globalLeft siteLeft bits
    t.instructions ≤ fuel ∧ t.probes ≤ min callLeft (min globalLeft siteLeft) - 1 ∧
      t.guessWork ≤ t.instructions + w * t.probes := by
  cases h : min callLeft (min globalLeft siteLeft) with
  | zero => simp [runChargedCall, h]
  | succ p => simpa [runChargedCall, h] using runLocalCall_bounds P fuel c p bits

/-- Work of the charged interpreter on an arbitrary private bit stream. -/
theorem runChargedCall_totalWork_le (P : Program w C) (fuel : ℕ) (c : C)
    (callLeft globalLeft siteLeft : ℕ) (bits : List Bool) :
    let t := runChargedCall P fuel c callLeft globalLeft siteLeft bits
    t.instructions + t.probes + t.guessWork ≤
      3 * fuel + w * (min callLeft (min globalLeft siteLeft) - 1) := by
  cases h : min callLeft (min globalLeft siteLeft) with
  | zero => simp [runChargedCall, h]
  | succ p => simpa [runChargedCall, h] using runLocalCall_totalWork_le P fuel c p bits

private theorem Guessed.runLocalCall_probes {P : Program w C} {f c es s}
    (hg : Guessed P f c es s) {p : ℕ} (hp : countProbes es ≤ p) (tail : List Bool) :
    (runLocalCall P f c p (guessBits es ++ tail)).probes = countProbes es := by
  induction hg generalizing p with
  | done hs => simp [runLocalCall, hs, LocalCallRun.stop, countProbes]
  | step hs _ ih =>
    simpa [runLocalCall, hs, guessBits, LocalCallRun.prepend, Event.probeCharge, countProbes]
      using ih hp
  | branch hs _ ih =>
    simpa [runLocalCall, hs, guessBits, LocalCallRun.prepend, Event.probeCharge, countProbes]
      using ih hp
  | read hs _ ih =>
    rename_i es _ _
    cases p with
    | zero => simp [countProbes] at hp
    | succ p =>
      have ht : countProbes es ≤ p := by simp only [countProbes] at hp; omega
      simp only [runLocalCall, hs, guessBits, List.append_assoc]
      rw [(takeWord_eq_some_iff _ _ _).mpr rfl]
      simp [LocalCallRun.prepend, Event.probeCharge, countProbes, ih ht]
  | write hs _ ih =>
    rename_i es _ _
    cases p with
    | zero => simp [countProbes] at hp
    | succ p =>
      have ht : countProbes es ≤ p := by simp only [countProbes] at hp; omega
      simp [runLocalCall, hs, guessBits, LocalCallRun.prepend, Event.probeCharge, countProbes,
        ih ht]

/-- On success, the accumulated counter gives the report's probe count. The
site loop can advance its charge using this counter without scanning events. -/
theorem runChargedCall_probes_eq {P : Program w C} {fuel c callLeft globalLeft siteLeft bits tail}
    {r : Report w}
    (h : (runChargedCall P fuel c callLeft globalLeft siteLeft bits).output = some (r, tail)) :
    (runChargedCall P fuel c callLeft globalLeft siteLeft bits).probes = r.probes := by
  cases hm : min callLeft (min globalLeft siteLeft) with
  | zero => simp [runChargedCall, hm] at h
  | succ p =>
    simp only [runChargedCall, hm] at h ⊢
    obtain ⟨hg, hp, rfl⟩ := runLocalCall_iff.mp h
    exact hg.runLocalCall_probes hp tail

end BurstRAM

end VPVNP
end Computability
end OAI
