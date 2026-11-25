import OAI.Computability.BorderVNP.FiniteOutputStack
import OAI.Computability.BorderVNP.FiniteOutputWriter

/-! # Running a fixed field-valued stack validator on its own literal prefix

The universal processor writes the whole field code at each accepting leaf.
That fixed extra cost is reserved once on a path, after the simulated stack
instructions. The named validator still enforces its prescribed fuel bound
on every input, including malformed metadata and padding.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldStack

open VPVNP.RAMTape VPVNP.UniversalMachine StackCompiler Filter

variable {k : ℕ} {Q F : Type*} [Fintype Q] [Field F] [Fintype F]

/-- An accepting state in the ready phase supplies its value to the finite-field writer. -/
def phaseWeight (w : Q → F) : Phase k Q → F
  | .ready q => w q
  | _ => 0

/-- Literal tape table for the elementary field-valued stack interpreter. -/
noncomputable abbrev machine (code : StackCode (Fin k) Q) (w : Q → F) (start : Q) : Program :=
  FieldTape.machine (.ready start) (rows code) (phaseWeight w)

private noncomputable abbrev physical (code : StackCode (Fin k) Q) (w : Q → F) (start : Q)
    (ticks : ℕ) (q : Q) (s : Stacks (Fin k)) : F :=
  FieldTape.value (.ready start) (rows code) (phaseWeight w) ticks (.ready q)
    (tapeList (packed s)) (tapeList [])

private theorem physical_step (code : StackCode (Fin k) Q) (w : Q → F) (start : Q)
    {t B ticks : ℕ} {q s r s'} (step : StackStep code q s r s') (size : (packed s).length+t+1 ≤ B)
    (clock : (t+1)*(6*B+4)+Fintype.card F ≤ ticks)
    (ih : ∀ left, (packed s').length+t ≤ B → t*(6*B+4)+Fintype.card F ≤ left →
      physical code w start left r s' = paths code w t r s') :
    physical code w start ticks q s = paths code w t r s' := by
  obtain ⟨d, hd, run⟩ := step_run code step
  have grow := step_size code step
  have bound : d ≤ 6*B+4 := by omega
  rw [Nat.succ_mul] at clock
  have he : ticks - d + d = ticks := by omega
  have hr := FieldTape.runs_value run (.ready start) (phaseWeight w) (ticks-d)
  rw [he] at hr
  exact hr.trans (ih _ (by omega) (by omega))

/-- Under the physical clock including the field-code trailer, every accepting stack
path has its prescribed field weight in the literal program. -/
theorem physical_eq (code : StackCode (Fin k) Q) (w : Q → F) (start : Q)
    (t : ℕ) (q : Q) (s : Stacks (Fin k)) (B ticks : ℕ)
    (stops : StopsWithin code t q s) (size : (packed s).length+t ≤ B)
    (clock : t*(6*B+4)+Fintype.card F ≤ ticks) :
    FieldTape.value (.ready start) (rows code) (phaseWeight w) ticks (.ready q)
      (tapeList (packed s)) (tapeList []) = paths code w t q s := by
  induction t generalizing q s ticks with
  | zero => exact stops.elim
  | succ t ih =>
    cases h : code q with
    | push i b r =>
      simp only [StopsWithin, h] at stops
      simp only [paths, h]
      exact physical_step code w start (.push h) (by omega) clock (fun _ => ih _ _ _ stops)
    | pop i f =>
      simp only [StopsWithin, h] at stops
      simp only [paths, h]
      exact physical_step code w start (.pop h) (by omega) clock (fun _ => ih _ _ _ stops)
    | goto r =>
      simp only [StopsWithin, h] at stops
      simp only [paths, h]
      exact physical_step code w start (.goto h) (by omega) clock (fun _ => ih _ _ _ stops)
    | choose low high =>
      simp only [StopsWithin, h] at stops
      rw [Nat.succ_mul] at clock
      obtain ⟨ticks,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ticks ≠ 0)
      rw [FieldTape.value_step _ _ _ _ _ _ _ (by omega)]
      simp only [rows, h, FieldTape.after, update_stay, paths]
      exact congrArg₂ (· + ·) (ih low s ticks stops.1 (by omega) (by omega))
        (ih high s ticks stops.2 (by omega) (by omega))
    | halt b =>
      rw [Nat.succ_mul] at clock
      obtain ⟨ticks,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ticks ≠ 0)
      rw [FieldTape.value_step _ _ _ _ _ _ _ (by omega)]
      simp only [rows, h, FieldTape.after, phaseWeight, paths]

/-- The one-hot output is evaluated on a machine that includes its own transition table
in the word it reads. -/
theorem prefix_value (code : StackCode (Fin (k+1)) Q) (w : Q → F) (start : Q)
    (payload : Word) (T : ℕ) :
    let raw := programPrefix (machine code w start) ++ payload
    StopsWithin code T start (inputStacks raw) →
    T * (6*(raw.length+(k+1)+T)+4)+Fintype.card F ≤ raw.length^100 →
      FPath.U F raw.get = paths code w T start (inputStacks raw) := by
  intro raw stops clock
  rw [FieldTape.initial_value]
  have ht : tapeList (packed (inputStacks (k := k) raw)) = Turing.Tape.mk₁ (raw.map fun b => if b then 2 else 1) := by
    rw [packed_input]
    exact congrArg (fun r => Turing.Tape.mk' (Turing.ListBlank.mk []) r)
      (show Turing.ListBlank.mk (raw.map bit ++ List.replicate (k+1) 0) = Turing.ListBlank.mk (raw.map bit) from
        Quotient.sound (Or.inr ⟨k+1,rfl⟩))
  change FieldTape.value (.ready start) (rows code) (phaseWeight w) (raw.length^100) (.ready start)
    (Turing.Tape.mk₁ (raw.map fun b => if b then 2 else 1)) (tapeList []) = _
  rw [← ht]
  exact physical_eq code w start T start (inputStacks raw) (raw.length+(k+1)+T)
    (raw.length^100) stops (by simp [packed_input]) clock

variable {K S : Type} [Fintype K] [DecidableEq K] [Fintype S]

/-- The named-port validator embeds into the elementary tape interpreter with the same
input word, path weights and accepting multiplicities. -/
theorem prefix_named (input : K) (code : StackCode K S) (w : S → F) (start : S)
    (payload : Word) (T : ℕ) :
    let raw := programPrefix (machine (labeledCode input code) w start) ++ payload
    StopsWithin code T start (labeledInput input raw) →
    T*(6*(raw.length+(Fintype.card K+1)+T)+4)+Fintype.card F ≤ raw.length^100 →
      FPath.U F raw.get = paths code w T start (labeledInput input raw) := by
  intro raw stops clock
  have h := (stopsWithin_lift (target := labeledCode input code) (labeledPort input)
    (labeledPort_injective input) id (inputStacks raw) (fun _ => rfl) T start _).2 stops
  have hp := paths_lift (target := labeledCode input code) (w := w) (w' := w) (labeledPort input)
    (labeledPort_injective input) id (inputStacks raw) (fun _ => rfl) (fun _ => rfl) T start (labeledInput input raw)
  rw [installedInput] at h hp
  exact (prefix_value (labeledCode input code) w start payload T h clock).trans hp

/-- The fixed program that installs the length-dependent source fuel before the interpreter. -/
noncomputable def clockedMachine (input : K) (u : ℕ) (src : StackCode K S) (w : S → F) (start : S) : Program :=
  machine (labeledCode (TeamClocked.Port.user input) (TeamClocked.code input u src start))
    (clockWeight input u w) (.inl (TeamClocked.startup input u).body.entry)

/-- All sufficiently long physical inputs carrying this one prefix return the field-valued
source path sum with exactly the advertised source clock. The threshold is independent of
the number of processors, links and all payload values. -/
theorem eventually_prefix_value (input : K) (u : ℕ) (hu : 1 ≤ u) (hexp : 2*(u+2)+1 ≤ 100)
    (src : StackCode K S) (w : S → F) (start : S) :
    ∀ᶠ n : ℕ in atTop, ∀ payload : Word,
      let raw := programPrefix (clockedMachine input u src w start) ++ payload
      raw.length = n → FPath.U F raw.get = paths src w (n^u) start (labeledInput input raw) := by
  let ports := Fintype.card (TeamClocked.Port K)+1
  filter_upwards [TeamClocked.eventually_tape_clock (ports+Fintype.card F) u hu hexp] with n hclock
  intro payload raw hlen
  let T := 2*raw.length^u+2+TeamClocked.prepSteps u raw.length
  have ⟨hs,_⟩ := TeamClocked.stack_run input u src (fun _ => false) start raw
  have hv := clock_value input u src w start raw
  have h := prefix_named (TeamClocked.Port.user input) (TeamClocked.code input u src start)
    (clockWeight input u w) (.inl (TeamClocked.startup input u).body.entry) payload T hs
  change T*(6*(raw.length+ports+T)+4)+Fintype.card F ≤ raw.length^100 → _ at h
  rw [← hlen] at hclock ⊢
  change T*(6*(raw.length+(ports+Fintype.card F)+T)+4) ≤ raw.length^100 at hclock
  have ht : 1 ≤ T := by dsimp [T]; omega
  have hcard := Nat.mul_le_mul_right (Fintype.card F) ht
  rw [one_mul] at hcard
  exact (h (le_trans (by nlinarith only [hcard]) hclock)).trans hv

end FieldStack

end BorderVNP
end Computability
end OAI
