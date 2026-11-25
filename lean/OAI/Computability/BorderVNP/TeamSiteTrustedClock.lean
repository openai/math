import OAI.Computability.BorderVNP.TeamSiteProcessor
import OAI.Computability.BorderVNP.TeamLink

/-! # Measuring the private call deadline on the real processor input

This fixed program measures its own complete input once, prior to decoding the site.
A separate unary bank retains one mark for every allowed native private-tape transition.
The ordinary signed processor clock still bounds the whole computation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TrustedClock

open VPVNP RAMTape UniversalMachine StackCompiler Filter
open private prepared startup_runs from OAI.Computability.BorderVNP.TeamClockedProgram

variable {K Q : Type} [DecidableEq K]

/-- Canonical bank after measuring the raw, prefix-bearing physical input. -/
def installed (input : K) (raw : Word) : Stacks (TeamClocked.Port K) :=
  Function.update (Function.update (labeledInput (.user input) raw) (.tally .length)
    (List.replicate raw.length true)) (.tally .fuel) (List.replicate (raw.length^25) true)

/-- The original raw input, every ordinary site stack, and both private counters at entry. -/
theorem installed_fields (input : K) (raw : Word) :
    (installed input raw) ∘ TeamClocked.Port.user = labeledInput input raw ∧
      installed input raw (.tally .length) = List.replicate raw.length true ∧
      installed input raw (.tally .fuel) = List.replicate (raw.length^25) true ∧
      ∀ p, installed input raw (.reader p) = [] := by
  constructor
  · funext p
    simp [installed,labeledInput]
  · simp [installed,labeledInput]

/-- Measure the actual raw input and then execute the fixed site table. The latter
may access the separate trusted template at each genuine private call boundary. -/
def code (input : K) (body : StackCode (TeamClocked.Port K) Q) (start : Q) :
    StackCode (TeamClocked.Port K) ((TeamClocked.startup input 25).State ⊕ Q)
  | .inl q => ((TeamClocked.startup input 25).body.code q).rename id (Option.elim · (.inr start) Sum.inl)
  | .inr q => (body q).rename id Sum.inr

/-- The measuring prefix makes no signed or nondeterministic choices. -/
def negative (input : K) (neg : Q → Bool) : (TeamClocked.startup input 25).State ⊕ Q → Bool :=
  Sum.elim (fun _ => false) neg

/-- Exact physical startup from an otherwise empty stack bank, reaching the entry of
the actual site body with the preserved input and its length-dependent unary template. -/
theorem prepare (input : K) (body : StackCode (TeamClocked.Port K) Q) (start : Q) (raw : Word) :
    StackRuns (code input body start) (TeamClocked.prepSteps 25 raw.length)
      (.inl (TeamClocked.startup input 25).body.entry) (labeledInput (.user input) raw)
      (.inr start) (installed input raw) := by
  let label (z : Option (TeamClocked.startup input 25).State) :
      (TeamClocked.startup input 25).State ⊕ Q := z.elim (.inr start) Sum.inl
  have row (q) (hc : ((TeamClocked.startup input 25).body.standalone q).returns = false) :
      code input body start (label q) = ((TeamClocked.startup input 25).body.standalone q).rename id label := by
    cases q with
    | none => contradiction
    | some q => rfl
  let base := labeledInput (TeamClocked.Port.user input) raw
  have eqs (s : Stacks (TeamClocked.Port K)) : installStacks id base s = s := by
    funext i; exact installStacks_at Function.injective_id base s i
  simpa only [eqs,label,Option.elim_some,Option.elim_none,installed,prepared] using
    (startup_runs input 25 raw).lift id Function.injective_id label base row

/-- The measuring prefix and its deterministic native startup consume exactly their
charged steps. After that prefix, all signed paths are paths of the selected site body. -/
theorem paths_after (input : K) (body : StackCode (TeamClocked.Port K) Q) (neg : Q → Bool)
    (start : Q) (raw : Word) (fuel : ℕ) :
    TeamStack.paths (code input body start) (negative input neg) (fuel+TeamClocked.prepSteps 25 raw.length)
      (.inl (TeamClocked.startup input 25).body.entry) (labeledInput (.user input) raw) =
      TeamStack.paths body neg fuel start (installed input raw) := by
  let bank := installed input raw
  have h := TeamGuard.paths_lift (target := code input body start) (src := body) (neg := neg)
    (neg' := negative input neg) id Function.injective_id Sum.inr bank (fun _ => rfl)
    (fun _ => rfl) fuel start bank
  have eq : installStacks id bank bank = bank := by funext p; exact installStacks_at Function.injective_id bank bank p
  rw [eq] at h
  exact (TeamGuard.runs_paths (prepare input body start raw) (negative input neg) fuel).trans h

/-- The trusted preparation leaves at least `n^35` steps to the ordinary site body
inside its independently measured `n^36` processor clock. -/
theorem eventually_prep_room :
    ∀ᶠ n : ℕ in atTop, n^35 + TeamClocked.prepSteps 25 n ≤ n^36 := by
  let c := (26*25+113)*2^26
  filter_upwards [eventually_ge_atTop (c+8)] with n hn
  have one : 1 ≤ n := by omega
  have hp := SiteFuel.work_le n 0 0 25 (by decide) (Nat.zero_le _) (Nat.zero_le _)
  have hmul : (n+1)^26 ≤ (2*n)^26 := Nat.pow_le_pow_left (by omega) _
  rw [mul_pow] at hmul
  have work : (SiteFuel.program 25).work (SiteFuel.initial n 0 0) ≤ c*n^26 :=
    hp.trans ((Nat.mul_le_mul_left _ hmul).trans_eq (Nat.mul_assoc ..).symm)
  have n35 : n^26 ≤ n^35 := Nat.pow_le_pow_right one (by decide)
  have lin : n ≤ n^35 := Nat.le_self_pow (by decide) _
  have pos : 1 ≤ n^35 := Nat.one_le_pow _ _ one
  change n^35+(5*n+2+(SiteFuel.program 25).work (SiteFuel.initial n 0 0)) ≤ n^36
  rw [show n^36 = n*n^35 by ring]
  calc
    _ ≤ (c+8)*n^35 := by
      have hwork := work.trans (Nat.mul_le_mul_left c n35)
      rw [Nat.add_mul]; omega
    _ ≤ n*n^35 := Nat.mul_le_mul_right _ hn

variable [Fintype K] [Fintype Q]

/-- A single physical universal program with an independent clock for all site work.
Neither the program code nor its private transition allowance is supplied as advice. -/
noncomputable def machine (input : K) (body : StackCode (TeamClocked.Port K) Q) (neg : Q → Bool) (start : Q) : Program :=
  TeamClocked.machine (.user input) 36 (code input body start) (negative input neg)
    (.inl (TeamClocked.startup input 25).body.entry)

/-- The actual signed coefficient of every sufficiently long word carrying this code
is precisely the body running on the physical input and its true private clock bank. -/
theorem eventually_value (input : K) (body : StackCode (TeamClocked.Port K) Q) (neg : Q → Bool) (start : Q) :
    ∀ᶠ n : ℕ in atTop, ∀ payload : Word,
      let raw := programPrefix (machine input body neg start) ++ payload
      raw.length = n → signedCount raw.get =
        TeamStack.paths body neg (n^36-TeamClocked.prepSteps 25 n) start (installed input raw) := by
  filter_upwards [TeamClocked.eventually_prefix_value (.user input) 36 (by decide) (by decide)
    (code input body start) (negative input neg) (.inl (TeamClocked.startup input 25).body.entry),
    eventually_prep_room] with n eval room
  intro payload raw hn
  have run := eval payload hn
  have endRun := paths_after input body neg start raw (n^36-TeamClocked.prepSteps 25 n)
  rw [hn, Nat.sub_add_cancel (by omega)] at endRun
  exact run.trans endRun

end TeamSite.TrustedClock

end BorderVNP
end Computability
end OAI
