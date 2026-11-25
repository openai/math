import OAI.Computability.NearSquareRoot.ScheduleStagingStartupRoute

/-! # Oversize split exponents on the complete physical startup machine

An oversized threshold is detected on the separator. Rejection becomes a
stationary self-loop before width generation or any candidate computation.
Thus every time cutoff sees the same linear strip, with no halting endpoint.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingStartup

open IntegerMultiplication TM Code Bits CommonAlphabet CommonAlphabet.Pipeline
open ChunkControl (Driver)
open private TapeSequence.first_step from OAI.Computability.NearSquareRoot.InterchangeSplitCompose
open StagingProtection (Cell Tapes)

variable {I Q : Type} [DecidableEq I] (d : Driver) [DecidableEq (StagingControl.Letter d)]

private def serialConfig (k C : ℕ) (x : Config (Cell d) (StagingSerialize.Phase k) Bool) :
    Config (Cell d) (PC k (StagingWidth.Phase C) ⊕ Q) (Axis d I) :=
  TapeSequence.relabel Sum.inl (TapeSequence.relabel Sum.inl (TapeSequence.relabel Sum.inl
    (mapper (inputRoute (inputReg d)) (fun _ => blankTape d) x)))

omit [DecidableEq (StagingControl.Letter d)] in
private theorem serial_initial (k C : ℕ) (x y : Word) :
    serialConfig (I:=I) (Q:=Q) d k C (StagingSerialize.initial d k x y) =
      initialMachine d k C x y := by
  change Config.mk _ _ = Config.mk _ _
  rw [Config.mk.injEq]
  exact ⟨rfl,begin_serial (P:=StagingWidth.Phase C) d k x y⟩

private theorem serial_prefix {k C : ℕ} (post : Rule (Cell d) Q (Tapes d I)) (q : Q)
    {x y : Config (Cell d) (StagingSerialize.Phase k) Bool} {t : ℕ}
    (hist : Trace (advance (serial d k)) x t y) :
    Trace (advance (machine d k C post q)) (serialConfig d k C x) t (serialConfig d k C y) := by
  apply TapeSequence.first_trace
  apply TapeSequence.first_trace
  apply TapeSequence.first_trace
  exact mapped_trace (inputRoute (inputReg d)) (fun _ => blankTape d) (serial d k) hist

/-- At the exact first rejecting time the assembled machine enters a fixed
configuration on which its next physical transition is the identity. -/
theorem reject_loop (k C : ℕ) (post : Rule (Cell d) Q (Tapes d I)) (q : Q) (x y : Word)
    (tooLarge : x.length < 2^k) :
    ∃ z, Trace (advance (machine d k C post q)) (initialMachine d k C x y) (x.length+1) z ∧
      advance (machine d k C post q) z = some z := by
  obtain ⟨hist,_⟩ := StagingSerialize.reject d k x y tooLarge
  have tr := serial_prefix (C:=C) d post q (serial_trace d k hist)
  rw [serial_initial] at tr
  refine ⟨_,tr,?_⟩
  have h : advance (serial d k) (StagingSerialize.rejected d k x y) = some (StagingSerialize.rejected d k x y) := by
    rw [serial,StagingReject.step]
    rfl
  apply TapeSequence.first_step
  apply TapeSequence.first_step
  apply TapeSequence.first_step
  rw [mapped_step,h]
  rfl

private theorem frozen {V : Type} {f : V → Option V} {a b : V} {j : ℕ}
    (h : Trace f a j b) (loop : f a = some a) : b = a := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    rw [loop] at h
    cases h
    exact ih loop

theorem oversize_ne_halt (k C : ℕ) (post : Rule (Cell d) Q (Tapes d I)) (q : Q)
    (x y : Word) (tooLarge : x.length < 2^k) {t z}
    (hist : Trace (advance (machine d k C post q)) (initialMachine d k C x y) t z) :
    advance (machine d k C post q) z ≠ none := by
  obtain ⟨v,tr,loop⟩ := reject_loop d k C post q x y tooLarge
  intro stop
  have passed := Uniform.before_halt hist stop tr
  obtain ⟨u,pre,tail⟩ := trace_split hist passed
  have end_eq := trace_endpoint_unique pre tr
  subst u
  rw [frozen tail loop,loop] at stop
  cases stop

/-- All heads stay within the first-operand length plus the delimiter at
every trial cutoff, independently of the digit routine and its tape count. -/
theorem oversize_prefix (k C : ℕ) (post : Rule (Cell d) Q (Tapes d I)) (q : Q)
    (x y : Word) (tooLarge : x.length < 2^k) {t z}
    (hist : Trace (advance (machine d k C post q)) (initialMachine d k C x y) t z) (i : Axis d I) :
    -((x.length+1 : ℕ):ℤ) ≤ (z.tape i).pos ∧ (z.tape i).pos ≤ (x.length+1 : ℕ) := by
  have origin : ((initialMachine (Q:=Q) d k C x y).tape i).pos = 0 := rfl
  by_cases h : t ≤ x.length+1
  · obtain ⟨lo,hi⟩ := head_excursion hist i
    rw [origin] at lo hi
    omega
  · obtain ⟨v,tr,loop⟩ := reject_loop d k C post q x y tooLarge
    obtain ⟨u,pre,tail⟩ := trace_split hist (k:=x.length+1) (by omega)
    have end_eq := trace_endpoint_unique pre tr
    subst u
    rw [frozen tail loop]
    obtain ⟨lo,hi⟩ := head_excursion tr i
    rw [origin] at lo hi
    omega

end StagingStartup

end NearSquareRoot
end Computability
end OAI
