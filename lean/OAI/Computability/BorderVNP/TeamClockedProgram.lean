import OAI.Computability.BorderVNP.TeamGuard
import OAI.Computability.VPVNP.RAMTapeSiteFuel
import OAI.Computability.VPVNP.RAMTapeInputRoutines
import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.StructuredStackClock

/-! # The signed local processor clock on every physical input

The program measures the length of its own literal input, builds a unary clock, and then
executes the signed stack validator. It rejects if the clock expires. Even malformed inputs
cannot evade this clock. The input length and the fuel are computed inside the machine.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamClocked

open VPVNP.RAMTape VPVNP.UniversalMachine StackCompiler Filter

/-- Separate original validator stacks, unary arithmetic stacks, and input-reader scratch. -/
inductive Port (K : Type) where
  | user (p : K)
  | tally (p : SiteFuel.Port)
  | reader (p : InputPort)
  deriving DecidableEq, Fintype

variable {K Q : Type} [DecidableEq K]

private def readerPort (input : K) : InputPort → Port K
  | .input => .user input
  | .size => .tally .length
  | p => .reader p

omit [DecidableEq K] in
private theorem reader_inj (input : K) : Function.Injective (readerPort input) := by
  rintro (_ | _ | _ | _ | _ | _ | _ | _ | _ | _) (_ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;> simp [readerPort]

private def guardPort : (K ⊕ Unit) → Port K
  | .inl p => .user p
  | .inr _ => .tally .fuel

omit [DecidableEq K] in
private theorem guard_inj : Function.Injective (guardPort (K := K)) := by
  rintro (p | ⟨⟩) (r | ⟨⟩) <;> simp [guardPort]

/-- Fixed length measurement and unary power routine preceding the validator. -/
def startup (input : K) (u : ℕ) : FiniteRoutine (Port K) :=
  ((FiniteRoutine.ofRoutine InputReader.lengthRoutine).onPorts (readerPort input)).followedBy
    ((FiniteRoutine.ofRoutine (SiteFuel.program u).code).onPorts Port.tally)

/-- Exact number of stack instructions used to construct the clock from the input. -/
def prepSteps (u n : ℕ) : ℕ := 5*n + 2 + (SiteFuel.program u).work (SiteFuel.initial n 0 0)

private def prepared (input : K) (u : ℕ) (raw : Word) : Stacks (Port K) :=
  Function.update (Function.update (labeledInput (Port.user input) raw) (.tally .length)
    (List.replicate raw.length true)) (.tally .fuel) (List.replicate (raw.length^u) true)

private theorem startup_runs (input : K) (u : ℕ) (raw : Word) :
    (startup input u).Runs (prepSteps u raw.length) (labeledInput (Port.user input) raw) (prepared input u raw) := by
  let s := labeledInput (Port.user input) raw
  let mid := Function.update s (.tally .length) (List.replicate raw.length true)
  let small := labeledInput InputPort.input raw
  have pre := InputReader.lengthRoutine_runs small (by simp [small, labeledInput])
  have hpre : ((FiniteRoutine.ofRoutine InputReader.lengthRoutine).onPorts (readerPort input)).Runs
      (5*raw.length+2) s mid := by
    apply FiniteRoutine.runs_onPorts_framed _ (reader_inj input) (h := pre)
    · intro k; cases k <;> simp [readerPort, s, small, labeledInput]
    · intro k; cases k <;> simp [readerPort, mid, s, small, labeledInput]
    · intro p hp
      exact Function.update_of_ne (Ne.symm (hp .size)) ..
  have pow := SiteFuel.runs raw.length 0 0 u
  have hpow : ((FiniteRoutine.ofRoutine (SiteFuel.program u).code).onPorts Port.tally).Runs
      ((SiteFuel.program u).work (SiteFuel.initial raw.length 0 0)) mid (prepared input u raw) := by
    apply FiniteRoutine.runs_onPorts_framed _ (fun _ _ => Port.tally.inj) (h := pow)
    · intro k; cases k <;> simp [mid, s, labeledInput, Tally.encode, SiteFuel.initial]
    · intro k; cases k <;> simp [prepared, labeledInput, Tally.encode, SiteFuel.initial, SiteFuel.result, SiteFuel.powered]
    · intro p hp
      exact Function.update_of_ne (Ne.symm (hp .fuel)) ..
  exact hpre.followedBy hpow

/-- The measured-clock control starts in its deterministic prefix and then follows the
original branching validator, consuming one guard bit per original instruction. -/
def code (input : K) (u : ℕ) (src : StackCode K Q) (start : Q) :
    StackCode (Port K) ((startup input u).State ⊕ TeamGuard.Phase Q)
  | .inl q => ((startup input u).body.code q).rename id
      (Option.elim · (.inr (.check start)) Sum.inl)
  | .inr q => (TeamGuard.code src q).rename guardPort Sum.inr

/-- The sign is read only at the validator's own accepting instruction. -/
def negative (input : K) (u : ℕ) (neg : Q → Bool) : (startup input u).State ⊕ TeamGuard.Phase Q → Bool :=
  Sum.elim (fun _ => false) (TeamGuard.negative neg)

private theorem startup_linked (input : K) (u : ℕ) (src : StackCode K Q) (start : Q) (raw : Word) :
    StackRuns (code input u src start) (prepSteps u raw.length) (.inl (startup input u).body.entry)
      (labeledInput (Port.user input) raw) (.inr (.check start)) (prepared input u raw) := by
  let label (z : Option (startup input u).State) : (startup input u).State ⊕ TeamGuard.Phase Q := z.elim (.inr (.check start)) Sum.inl
  have row (q) (hc : ((startup input u).body.standalone q).returns = false) :
      code input u src start (label q) = ((startup input u).body.standalone q).rename id label := by
    cases q with
    | none => contradiction
    | some q => rfl
  let base := labeledInput (Port.user input) raw
  have eqs (s : Stacks (Port K)) : installStacks id base s = s := by
    funext i; exact installStacks_at Function.injective_id base s i
  simpa only [eqs, label, Option.elim_some, Option.elim_none] using (startup_runs input u raw).lift id Function.injective_id label base row

/-- The fixed input-measuring machine halts on every string. Its path value is the original
validator's signed count at exactly `raw.length^u` steps, even when the latter times out. -/
theorem stack_run (input : K) (u : ℕ) (src : StackCode K Q) (neg : Q → Bool) (start : Q) (raw : Word) :
    let T := 2 * raw.length^u + 2 + prepSteps u raw.length
    let P := code input u src start
    let q := Sum.inl (startup input u).body.entry
    let s := labeledInput (Port.user input) raw
    StopsWithin P T q s ∧ TeamStack.paths P (negative input u neg) T q s =
      TeamStack.paths src neg (raw.length^u) start (labeledInput input raw) := by
  intro T P q s
  let sz := raw.length^u
  let data := labeledInput input raw
  let base := prepared input u raw
  have hbase : installStacks guardPort base (TeamGuard.bank data sz) = base := by
    apply installStacks_eq guard_inj
    rintro (p | ⟨⟩) <;> simp [base, data, sz, prepared, guardPort, TeamGuard.bank, labeledInput]
  have ⟨hs, hv⟩ := TeamGuard.executes src neg start data sz
  have hst := (stopsWithin_lift (target := P) guardPort guard_inj Sum.inr base (fun _ => rfl)
    (2*sz+2) (.check start) (TeamGuard.bank data sz)).mpr hs
  have hval := TeamGuard.paths_lift (target := P) (neg := TeamGuard.negative neg) (neg' := negative input u neg)
    guardPort guard_inj Sum.inr base (fun _ => rfl) (fun _ => rfl) (2*sz+2) (.check start) (TeamGuard.bank data sz)
  rw [hbase] at hst hval
  have prep := startup_linked input u src start raw
  exact ⟨(prep.stopsWithin_iff (2*sz+2)).mpr hst,
    (TeamGuard.runs_paths prep (negative input u neg) (2*sz+2)).trans (hval.trans hv)⟩

/-- The complete startup, timeout checks, and quadratic two-tape compilation fit the
actual `n^100` coefficient clock. The length threshold may depend on the fixed stack bank. -/
theorem eventually_tape_clock (ports u : ℕ) (hu : 1 ≤ u) (hexp : 2*(u+2)+1 ≤ 100) :
    ∀ᶠ n : ℕ in atTop, let T := 2*n^u + 2 + prepSteps u n
      T * (6*(n+ports+T)+4) ≤ n^100 := by
  let c := (26*u+113)*2^(u+1)
  filter_upwards [eventually_ge_atTop (max 28 (max ports (c+11)))] with n hn
  have hn28 := (le_max_left ..).trans hn
  have hports := (le_max_left ..).trans ((le_max_right ..).trans hn)
  have hc := (le_max_right ..).trans ((le_max_right ..).trans hn)
  have hn1 : 1 ≤ n := by omega
  let B := n^(u+1)
  have hBn : n ≤ B := Nat.le_self_pow (Nat.succ_ne_zero _) _
  have hBu : n^u ≤ B := Nat.pow_le_pow_right hn1 (Nat.le_succ u)
  have hp := SiteFuel.work_le n 0 0 u hu (Nat.zero_le _) (Nat.zero_le _)
  have hm : (n+1)^(u+1) ≤ (2*n)^(u+1) := Nat.pow_le_pow_left (by omega) _
  rw [mul_pow] at hm
  have hh := hp.trans (Nat.mul_le_mul_left (26*u+113) hm)
  rw [← Nat.mul_assoc] at hh
  change _ ≤ c*B at hh
  let T := 2*n^u+2+prepSteps u n
  have hT : T ≤ n^(u+2) := calc
    _ ≤ (c+11)*B := by dsimp only [T, prepSteps]; rw [Nat.add_mul]; omega
    _ ≤ n*B := Nat.mul_le_mul_right _ hc
    _ = _ := (Nat.pow_succ' ..).symm
  have hBig : n ≤ n^(u+2) := Nat.le_self_pow (Nat.succ_ne_zero _) _
  change T * (6*(n+ports+T)+4) ≤ _
  calc
    _ ≤ n^(u+2)*(28*n^(u+2)) := Nat.mul_le_mul hT (by omega)
    _ = 28*n^(2*(u+2)) := by rw [Nat.mul_comm 2 (u+2), pow_mul]; ring
    _ ≤ n*n^(2*(u+2)) := Nat.mul_le_mul_right _ hn28
    _ = n^(2*(u+2)+1) := (Nat.pow_succ' ..).symm
    _ ≤ n^100 := Nat.pow_le_pow_right hn1 hexp

variable [Fintype K] [Fintype Q]

/-- Literal signed universal program that measures its own input and clocks the validator. -/
noncomputable def machine (input : K) (u : ℕ) (src : StackCode K Q) (neg : Q → Bool) (start : Q) : Program :=
  TeamStack.machine (labeledCode (Port.user input) (code input u src start)) (negative input u neg)
    (.inl (startup input u).body.entry)

/-- Every sufficiently long input carrying this single program, including malformed
validator payloads, returns exactly the `n^u`-step signed source computation. -/
theorem eventually_prefix_value (input : K) (u : ℕ) (hu : 1 ≤ u) (hexp : 2*(u+2)+1 ≤ 100)
    (src : StackCode K Q) (neg : Q → Bool) (start : Q) :
    ∀ᶠ n : ℕ in atTop, ∀ payload : Word,
      let raw := programPrefix (machine input u src neg start) ++ payload
      raw.length = n → signedCount raw.get = TeamStack.paths src neg (n^u) start (labeledInput input raw) := by
  filter_upwards [eventually_tape_clock (Fintype.card (Port K)+1) u hu hexp] with n clock
  intro payload raw hlen
  let T := 2*raw.length^u+2+prepSteps u raw.length
  have ⟨hs, hv⟩ := stack_run input u src neg start raw
  have h := TeamGuard.prefix_named (Port.user input) (code input u src start) (negative input u neg)
    (.inl (startup input u).body.entry) payload T hs
  change T * (6 * (raw.length + (Fintype.card (Port K)+1) + T) + 4) ≤ raw.length^100 → _ at h
  exact (h (by simpa only [T, hlen] using clock)).trans (by rw [← hlen]; exact hv)

end TeamClocked

end BorderVNP
end Computability
end OAI
