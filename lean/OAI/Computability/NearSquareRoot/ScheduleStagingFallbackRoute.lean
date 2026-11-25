import OAI.Computability.NearSquareRoot.ScheduleStagingFallbackLayout
import OAI.Computability.NearSquareRoot.ShortWordSpace

/-!
# Exact physical routing of a positive candidate into the shared fallback bank

The candidate uses the standard literal input and output ports. All added
tapes start blank, stay parked, and contribute no head excursion. A halting
shared trace reflects to the corresponding halting local trace at exactly
the same step count.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingFallbackRoute

open IntegerMultiplication TM CommonAlphabet.Pipeline
open ChunkControl (Driver)

variable {A Q I J : Type} (r : Route I J)

def routed (blank : A) (x : Config A Q I) : Config A Q J :=
  ⟨x.pc,r.put x.tape (fun _ => Tape.loaded blank [])⟩

private theorem config_eq (blank : A) (x : Config A Q I) :
    routed r blank x = CommonTapes.config r.index (fun _ => Tape.loaded blank []) x :=
  congrArg (Config.mk x.pc) (r.put_eq _ _)

@[simp] theorem tape_at (blank : A) (x : Config A Q I) (i : I) :
    (routed r blank x).tape (r.index i) = x.tape i := by
  simp [routed,r.put_eq]

theorem tape_off (blank : A) (x : Config A Q I) (j : J) (h : ¬∃ i, r.index i = j) :
    (routed r blank x).tape j = Tape.loaded blank [] := by
  simp [routed,r.put_eq,CommonTapes.extend_off _ _ _ _ h]

/-- Embedding an ordinary two-operand input onto an initially empty bank
gives exactly the ordinary input configuration at the routed port. -/
theorem initial_routed (start : Q) (inp : I) (bit : Bool → A) (sep blank : A) (x y : List Bool) :
    routed r blank (initialConfig start inp bit sep blank x y) =
      initialConfig start (r.index inp) bit sep blank x y := by
  classical
  apply congrArg (Config.mk start)
  funext j
  change (routed r blank (initialConfig start inp bit sep blank x y)).tape j =
    (initialConfig start (r.index inp) bit sep blank x y).tape j
  by_cases h : ∃ i, r.index i = j
  · obtain ⟨i,rfl⟩ := h
    rw [tape_at]
    simp [initialConfig]
  · rw [tape_off _ _ _ _ h]
    simp [initialConfig,show j ≠ r.index inp from fun e => h ⟨inp,e.symm⟩]

theorem advance_routed (blank : A) (m : Rule A Q I) (x : Config A Q I) :
    advance (r.rule m) (routed r blank x) = (advance m x).map (routed r blank) := by
  rw [r.rule_eq,config_eq,CommonTapes.advance_config]
  cases advance m x with
  | none => rfl
  | some y => exact congrArg some (config_eq r blank y).symm

theorem trace (blank : A) (m : Rule A Q I) {x y t} (h : Trace (advance m) x t y) :
    Trace (advance (r.rule m)) (routed r blank x) t (routed r blank y) := by
  rw [r.rule_eq,config_eq,config_eq]
  exact CommonTapes.trace _ _ _ h

theorem reflect_trace (blank : A) (m : Rule A Q I) {x w t}
    (run : Trace (advance (r.rule m)) (routed r blank x) t w) :
    ∃ z, Trace (advance m) x t z ∧ w = routed r blank z := by
  rw [r.rule_eq,config_eq] at run
  obtain ⟨z,hz,he⟩ := CommonTapes.reflectTrace _ m _ run
  exact ⟨z,hz,he.symm.trans (config_eq r blank z).symm⟩

/-- A head bound on arbitrary local prefixes also covers arbitrary shared
prefixes, including cutoffs reached before the candidate halts. -/
theorem prefix_within (blank : A) (m : Rule A Q I) {R : ℕ} {x : Config A Q I}
    (bound : ∀ {k z}, Trace (advance m) x k z → ∀ i,
      -(R : ℤ) ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ R)
    {t w} (run : Trace (advance (r.rule m)) (routed r blank x) t w) (j : J) :
    -(R : ℤ) ≤ (w.tape j).pos ∧ (w.tape j).pos ≤ R := by
  obtain ⟨z,hz,rfl⟩ := reflect_trace r blank m run
  by_cases h : ∃ i, r.index i = j
  · obtain ⟨i,rfl⟩ := h
    simpa using bound hz i
  · rw [tape_off r blank z j h]
    change -(R : ℤ) ≤ 0 ∧ 0 ≤ (R : ℤ)
    omega

theorem reflect_halt (blank : A) (m : Rule A Q I) {x w t}
    (run : Trace (advance (r.rule m)) (routed r blank x) t w) (stop : advance (r.rule m) w = none) :
    ∃ z, Trace (advance m) x t z ∧ advance m z = none ∧ w = routed r blank z := by
  obtain ⟨z,hz,rfl⟩ := reflect_trace r blank m run
  rw [advance_routed,Option.map_eq_none_iff] at stop
  exact ⟨z,hz,stop,rfl⟩

theorem run_fenced (blank : A) (m : Rule A Q I) {R : ℕ} {x y t}
    (run : FencedRun m (fun _ => -(R : ℤ)) (fun _ => R) x t y) :
    FencedRun (r.rule m) (fun _ => -(R : ℤ)) (fun _ => R)
      (routed r blank x) t (routed r blank y) := by
  classical
  refine ⟨trace r blank m run.1,fun k hk z hf j => ?_⟩
  obtain ⟨v,hv,_⟩ := trace_split run.1 hk
  rw [trace_endpoint_unique hf (trace r blank m hv)]
  by_cases h : ∃ i, r.index i = j
  · obtain ⟨i,rfl⟩ := h
    rw [tape_at]
    exact run.2 k hk v hv i
  · rw [tape_off r blank v j h]
    change -(R : ℤ) ≤ 0 ∧ 0 ≤ (R : ℤ)
    omega

theorem whole_output (blank : A) (z : List A) (out : I) (x : Config A Q I) :
    whole blank z ((routed r blank x).tape (r.index out)) ↔ whole blank z (x.tape out) := by
  rw [tape_at]

section Positive

open StagingFallback

variable (d : Driver) (I : Type)

local notation "bank" => positiveRoute d I
local notation "B" => StagingProtection.blank d
local notation "b" => StagingProtection.bit d
local notation "sep" => StagingSerialize.put d Code.Ltr.sep

theorem positive_initial (q : Q) (x y : List Bool) :
    routed bank B (initialConfig q (.inl false) b sep B x y) =
    initialConfig q (inp d I) b sep B x y :=
  initial_routed bank q (.inl false) b sep B x y

/-- A shared positive halt has the actual local endpoint on every positive
port, while all schoolbook-only tapes still contain precisely the blank tape. -/
theorem positive_halt (m : Rule (StagingProtection.Cell d) Q (Local d I)) (q : Q)
    (x y : List Bool) {t w}
    (run : Trace (advance ((positiveRoute d I).rule m)) (initialConfig q (inp d I) b sep B x y) t w)
    (stop : advance ((positiveRoute d I).rule m) w = none) :
    ∃ z, Trace (advance m) (initialConfig q (.inl false) b sep B x y) t z ∧
      advance m z = none ∧ w = routed bank B z ∧ w.pc = z.pc ∧
      (∀ j, w.tape (.inl j) = z.tape j) ∧ (∀ j, w.tape (.inr j) = Tape.loaded B []) := by
  rw [← positive_initial d I q] at run
  obtain ⟨z,hz,halt,rfl⟩ := reflect_halt bank B m run stop
  exact ⟨z,hz,halt,rfl,rfl,fun _ => rfl,fun _ => rfl⟩

theorem positive_prefix (m : Rule (StagingProtection.Cell d) Q (Local d I)) (q : Q)
    (x y : List Bool) {R : ℕ}
    (bound : ∀ {k v}, Trace (advance m) (initialConfig q (.inl false) b sep B x y) k v →
      ∀ i, -(R : ℤ) ≤ (v.tape i).pos ∧ (v.tape i).pos ≤ R)
    {t w} (run : Trace (advance ((positiveRoute d I).rule m))
      (initialConfig q (inp d I) b sep B x y) t w) (j : Axes d I) :
    -(R : ℤ) ≤ (w.tape j).pos ∧ (w.tape j).pos ≤ R := by
  rw [← positive_initial d I q] at run
  exact prefix_within bank B m bound run j

/-- The chosen positive candidate has exactly the same time, radius, and
literal output on the shared positive and fallback machine bank. -/
theorem positive_run (m : Rule (StagingProtection.Cell d) Q (Local d I)) (q : Q)
    (x y z : List Bool) {R t : ℕ} {v}
    (run : FencedRun m (fun _ => -(R : ℤ)) (fun _ => R)
      (initialConfig q (.inl false) b sep B x y) t v)
    (stop : advance m v = none) (word : whole B (z.map b) (v.tape (.inr none))) :
    FencedRun ((positiveRoute d I).rule m) (fun _ => -(R : ℤ)) (fun _ => R)
      (initialConfig q (inp d I) b sep B x y) t (routed bank B v) ∧
    advance ((positiveRoute d I).rule m) (routed bank B v) = none ∧
    whole B (z.map b) ((routed bank B v).tape (out d I)) := by
  rw [← positive_initial d I q]
  refine ⟨run_fenced bank B m run, ?_,word⟩
  rw [advance_routed,stop]
  rfl

end Positive
end StagingFallbackRoute

end NearSquareRoot
end Computability
end OAI
