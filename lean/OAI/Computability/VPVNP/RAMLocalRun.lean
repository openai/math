import OAI.Computability.VPVNP.RAMWordBits
import OAI.Computability.VPVNP.RAMRecords

/-!
# Binary paths of the private call interpreter

A site processor in Lemma 10.1 follows the program's binary branches and reads
exactly one word of guesses at a permitted external read. A write has no guessed
value. The processor checks its instruction clock before dispatch, and checks
its remaining probe budget before consuming read bits or recording a write.
A successful call returns its unused bit suffix for the next call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*}

/-- Bits used by the site validator, including the guesses made at reads. -/
def guessBits : List (Event w) → List Bool
  | [] => []
  | .choice b :: es => b :: guessBits es
  | .read _ v :: es => wordBits v ++ guessBits es
  | _ :: es => guessBits es

/-- Charge one probe for each external read or write and zero for a private tick or branch. -/
def Event.probeCharge : Event w → ℕ
  | .read .. | .write .. => 1
  | _ => 0

/-- Number of guess bits reserved by the site validator for this event. A branch uses one bit
and a read uses one full word. -/
def Event.guessWidth : Event w → ℕ
  | .choice _ => 1
  | .read .. => w
  | _ => 0

/-- Metered execution on a binary stream. `guessWork` counts reserved bit slots,
including the requested slots when the stream ends during a guess. -/
structure LocalCallRun (w : ℕ) where
  /-- The successful call report and unused guess suffix, or `none` when the local execution
  fails. -/
  output : Option (Report w × List Bool)
  /-- Number of instructions charged by the local interpreter, including the terminating
  instruction when one executes. -/
  instructions : ℕ
  /-- Number of probe slots charged, including an allowed read that fails for lack of enough
  guess bits. -/
  probes : ℕ
  /-- Number of guess-bit slots requested by branches and reads, including requests whose input
  stream is too short. -/
  guessWork : ℕ

/-- One terminating instruction. -/
def LocalCallRun.stop (out : Option (Report w × List Bool)) (probes guessWork : ℕ) : LocalCallRun w :=
  ⟨out, 1, probes, guessWork⟩

/-- One executed instruction followed by the remainder of this call. -/
def LocalCallRun.prepend (e : Event w) (t : LocalCallRun w) : LocalCallRun w :=
  ⟨t.output.map (fun (r, bits) => (r.prepend e, bits)), 1 + t.instructions,
    e.probeCharge + t.probes, e.guessWidth + t.guessWork⟩

/-- Interpret a call privately. The caller supplies the remaining allowance for
probes after charging the unit for starting the call. -/
def runLocalCall (P : Program w C) : ℕ → C → ℕ → List Bool → LocalCallRun w
  | 0, _, _, _ => ⟨none, 0, 0, 0⟩
  | f + 1, c, allowance, bits =>
    match P.step c with
    | .finish s => .stop (some (⟨[], s⟩, bits)) 0 0
    | .reject => .stop none 0 0
    | .localStep c' => (runLocalCall P f c' allowance bits).prepend .tick
    | .branch next =>
      match bits with
      | [] => .stop none 0 1
      | b :: bs => (runLocalCall P f (next b) allowance bs).prepend (.choice b)
    | .read a next =>
      match allowance with
      | 0 => .stop none 0 0
      | p + 1 =>
        match takeWord w bits with
        | none => .stop none 1 w
        | some (v, bs) => (runLocalCall P f (next v) p bs).prepend (.read a v)
    | .write a v c' =>
      match allowance with
      | 0 => .stop none 0 0
      | p + 1 => (runLocalCall P f c' p bits).prepend (.write a v)

theorem runLocalCall_spec {P : Program w C} {f c p bits tail} {r : Report w}
    (h : (runLocalCall P f c p bits).output = some (r, tail)) :
    Guessed P f c r.events r.result ∧ countProbes r.events ≤ p ∧ bits = guessBits r.events ++ tail := by
  induction f generalizing c p bits tail r with
  | zero => simp [runLocalCall] at h
  | succ f ih =>
    cases hs : P.step c with
    | reject => simp [runLocalCall, hs, LocalCallRun.stop] at h
    | finish s =>
      simp only [runLocalCall, hs, LocalCallRun.stop, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.done hs, Nat.zero_le _, rfl⟩
    | localStep c' =>
      simp only [runLocalCall, hs, LocalCallRun.prepend, Option.map_eq_some_iff] at h
      obtain ⟨⟨r', t⟩, hr, he⟩ := h
      cases he
      obtain ⟨hg, hp, hb⟩ := ih hr
      exact ⟨.step hs hg, hp, hb⟩
    | branch next =>
      cases bits with
      | nil => simp [runLocalCall, hs, LocalCallRun.stop] at h
      | cons b bs =>
        simp only [runLocalCall, hs, LocalCallRun.prepend, Option.map_eq_some_iff] at h
        obtain ⟨⟨r', t⟩, hr, he⟩ := h
        cases he
        obtain ⟨hg, hp, hb⟩ := ih hr
        exact ⟨.branch hs hg, hp, congrArg (b :: ·) hb⟩
    | read a next =>
      cases p with
      | zero => simp [runLocalCall, hs, LocalCallRun.stop] at h
      | succ p =>
        cases hw : takeWord w bits with
        | none => simp [runLocalCall, hs, hw, LocalCallRun.stop] at h
        | some z =>
          obtain ⟨v, bs⟩ := z
          simp only [runLocalCall, hs, hw, LocalCallRun.prepend, Option.map_eq_some_iff] at h
          obtain ⟨⟨r', t⟩, hr, he⟩ := h
          cases he
          obtain ⟨hg, hp, hb⟩ := ih hr
          refine ⟨.read hs hg, by change 1 + countProbes r'.events ≤ p + 1; omega, ?_⟩
          change bits = (wordBits v ++ guessBits r'.events) ++ t
          rw [List.append_assoc, ← hb]
          exact (takeWord_eq_some_iff _ _ _).mp hw
    | write a v c' =>
      cases p with
      | zero => simp [runLocalCall, hs, LocalCallRun.stop] at h
      | succ p =>
        simp only [runLocalCall, hs, LocalCallRun.prepend, Option.map_eq_some_iff] at h
        obtain ⟨⟨r', t⟩, hr, he⟩ := h
        cases he
        obtain ⟨hg, hp, hb⟩ := ih hr
        exact ⟨.write hs hg, by change 1 + countProbes r'.events ≤ p + 1; omega, hb⟩

theorem Guessed.to_runLocalCall {P : Program w C} {f c es s}
    (hg : Guessed P f c es s) {p : ℕ} (hp : countProbes es ≤ p) (tail : List Bool) :
    (runLocalCall P f c p (guessBits es ++ tail)).output = some (⟨es, s⟩, tail) := by
  induction hg generalizing p with
  | done hs => simp [runLocalCall, hs, guessBits, LocalCallRun.stop]
  | step hs _ ih =>
    simp [runLocalCall, hs, guessBits, LocalCallRun.prepend, ih hp, Report.prepend]
  | branch hs _ ih =>
    simp [runLocalCall, hs, guessBits, LocalCallRun.prepend, ih hp, Report.prepend]
  | read hs _ ih =>
    rename_i es _ _
    cases p with
    | zero => simp [countProbes] at hp
    | succ p =>
      have ht : countProbes es ≤ p := by simp only [countProbes] at hp; omega
      simp only [guessBits, List.append_assoc, runLocalCall, hs]
      rw [(takeWord_eq_some_iff _ _ _).mpr rfl]
      simp [LocalCallRun.prepend, ih ht, Report.prepend]
  | write hs _ ih =>
    rename_i es _ _
    cases p with
    | zero => simp [countProbes] at hp
    | succ p =>
      have ht : countProbes es ≤ p := by simp only [countProbes] at hp; omega
      simp [runLocalCall, hs, guessBits, LocalCallRun.prepend, ih ht, Report.prepend]

/-- A successful report determines the consumed binary string exactly. This
also distinguishes branches with the same continuation or result. -/
theorem runLocalCall_iff {P : Program w C} {f c p bits tail} {r : Report w} :
    (runLocalCall P f c p bits).output = some (r, tail) ↔
      Guessed P f c r.events r.result ∧ r.probes ≤ p ∧ bits = guessBits r.events ++ tail := by
  refine ⟨runLocalCall_spec, ?_⟩
  rintro ⟨hg, hp, rfl⟩
  exact hg.to_runLocalCall hp tail

/-- With exact use of the bits, every permitted trace has one accepting
binary path through the local call simulator. -/
theorem existsUnique_callBits {P : Program w C} {f c p} {r : Report w}
    (hg : Guessed P f c r.events r.result) (hp : r.probes ≤ p) :
    ∃! bs, (runLocalCall P f c p bs).output = some (r, []) := by
  refine ⟨guessBits r.events, runLocalCall_iff.mpr ⟨hg, hp, by simp⟩, fun bs hb => ?_⟩
  simpa using (runLocalCall_iff.mp hb).2.2

/-- The three remaining allowances count the startup charge as well as the
probes. A zero allowance rejects before the program sees its first instruction. -/
def runChargedCall (P : Program w C) (f : ℕ) (c : C) (callLeft globalLeft siteLeft : ℕ)
    (bits : List Bool) : LocalCallRun w :=
  match min callLeft (min globalLeft siteLeft) with
  | 0 => ⟨none, 0, 0, 0⟩
  | p + 1 => runLocalCall P f c p bits

theorem runChargedCall_iff {P : Program w C} {f c callLeft globalLeft siteLeft bits tail}
    {r : Report w} :
    (runChargedCall P f c callLeft globalLeft siteLeft bits).output = some (r, tail) ↔
      Guessed P f c r.events r.result ∧ 1 + r.probes ≤ callLeft ∧
      1 + r.probes ≤ globalLeft ∧ 1 + r.probes ≤ siteLeft ∧ bits = guessBits r.events ++ tail := by
  have hcap : ∀ x : ℕ, x ≤ min callLeft (min globalLeft siteLeft) ↔
      x ≤ callLeft ∧ x ≤ globalLeft ∧ x ≤ siteLeft := fun x => by simp only [le_min_iff]
  cases hm : min callLeft (min globalLeft siteLeft) with
  | zero =>
    simp only [runChargedCall, hm, reduceCtorEq, false_iff]
    rintro ⟨_, hc, hg, hs, _⟩
    have := (hcap _).mpr ⟨hc, hg, hs⟩
    omega
  | succ p =>
    simp only [runChargedCall, hm, runLocalCall_iff]
    have hc : r.probes ≤ p ↔ 1 + r.probes ≤ callLeft ∧ 1 + r.probes ≤ globalLeft ∧
        1 + r.probes ≤ siteLeft := by rw [← hcap, hm]; omega
    tauto

end BurstRAM

end VPVNP
end Computability
end OAI
