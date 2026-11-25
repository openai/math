import OAI.Computability.NearSquareRoot.ScheduleMachine
import OAI.Computability.NearSquareRoot.ScheduleCharges

/-!
# Correctness, time, and space of the physical round loop

A restartable executor operates on the whole tape family and returns the current
slot's result. A failed slot restores its entry layout. The outer control checks
this return, updates the two persistent counters and starts the next attempt.
The proof combines exact physical traces and common absolute head intervals
through successive attempts and rounds.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ScheduleMachine

open IntegerMultiplication

private def bounded {A Q I : Type} (m : TM.Rule A Q I) (lo hi : I → ℤ)
    (x z : TM.Config A Q I) (bound : ℕ) : Prop :=
  ∃ t ≤ bound, FencedRun m lo hi x t z

private theorem bounded_trans {A Q I : Type} {m : TM.Rule A Q I} {lo hi : I → ℤ}
    {x y z : TM.Config A Q I} {u v : ℕ}
    (left : bounded m lo hi x y u) (right : bounded m lo hi y z v) :
    bounded m lo hi x z (u+v) := by
  obtain ⟨t,ht,hs⟩ := left
  obtain ⟨k,hk,hz⟩ := right
  exact ⟨_,Nat.add_le_add ht hk,hs.trans hz⟩

private def delivered {A Q I α : Type} (m : TM.Rule A Q I) (lo hi : I → ℤ)
    (P : α → TM.Config A Q I → Prop) (x pending : TM.Config A Q I) (bound : ℕ) :
    Option α → Prop
  | some y => ∃ z, bounded m lo hi x z bound ∧ TM.advance m z = none ∧ P y z
  | none => bounded m lo hi x pending bound

private def first {α : Type} (left right : Option α) : Option α :=
  match left with | some t => some t | none => right

private theorem delivered_join {A Q I α : Type} {m : TM.Rule A Q I} {lo hi : I → ℤ}
    {P : α → TM.Config A Q I → Prop} {x y z : TM.Config A Q I}
    {u v : ℕ} {left right : Option α} (h : delivered m lo hi P x y u left)
    (g : delivered m lo hi P y z v right) :
    delivered m lo hi P x z (u+v) (first left right) := by
  cases left with
  | some a =>
    obtain ⟨b,⟨k,hk,hrun⟩,hhalt,hp⟩ := h
    exact ⟨b,⟨k,by omega,hrun⟩,hhalt,hp⟩
  | none =>
    cases right with
    | none => exact bounded_trans h g
    | some a =>
      obtain ⟨c,pre,halt,hp⟩ := g
      exact ⟨c,bounded_trans h pre,halt,hp⟩

variable {A Q I α : Type} [Finite A]
variable (blank mark : A) (start : Q) (trial : TM.Rule A Q (Index I)) (accept : Q → Bool)
    (work : I → TM.Tape A)
local notation "M" => rule blank mark start trial accept
local notation "slotAt" => slot blank mark start work

/-- The executor's result includes its actual partial-machine trace, in the joint
fence and charged through copying/cleanup. A rejected attempt restores the exact
physical tape contents and head positions. -/
def AttemptReturns (lo hi : Index I → ℤ) (P : α → TM.Config A (PC Q) (Index I) → Prop)
    (answer : ℕ → ℕ → Option α) (charge : ℕ → ℕ → ℕ) (i a : ℕ) : Prop :=
  ∃ (t : ℕ) (z : TM.Config A Q (Index I)), t ≤ charge i a ∧
    FencedRun trial lo hi ⟨start, counters blank mark i a work⟩ t z ∧
    TM.advance trial z = none ∧
    match answer i (2^a) with
    | some v => accept z.pc = true ∧ P v (enter z)
    | none => accept z.pc = false ∧ z.tape = counters blank mark i a work

variable {blank mark start trial accept work}
variable {lo hi : Index I → ℤ} {P : α → TM.Config A (PC Q) (Index I) → Prop}
    {answer : ℕ → ℕ → Option α} {charge : ℕ → ℕ → ℕ}

private theorem slot_run (hne : blank ≠ mark) {i a : ℕ}
    (fits : ∀ j, lo j + (i+3 : ℕ) ≤ (counters blank mark i a work j).pos ∧
      (counters blank mark i a work j).pos ≤ hi j - (i+3 : ℕ))
    (attempt : AttemptReturns blank mark start trial accept work lo hi P answer charge i a) :
    delivered M lo hi P (slotAt i a) (slotAt (next i a).1 (next i a).2)
      (charge i a + (i+3)) (answer i (2^a)) := by
  obtain ⟨t,z,ht,hrun,halt,result⟩ := attempt
  have first := run_fenced blank mark start trial accept hrun
  cases ho : answer i (2^a) with
  | some v =>
    rw [ho] at result
    exact ⟨enter z,⟨t,by omega,first⟩,finish_accept blank mark start trial accept halt result.1,
      result.2⟩
  | none =>
    rw [ho] at result
    obtain ⟨k,hk,last⟩ := retry blank mark start trial accept hne work i a result.2 halt result.1
    have hfit := fencedRun_of_call_clock last (i+3) hk (by
      intro j; simpa [enter,result.2] using fits j)
    exact ⟨t+k,Nat.add_le_add ht hk,first.trans hfit⟩

/-- At the end of a round the unsuccessful branch is the zero index of the next round. -/
private def rangeStart (blank mark : A) (start : Q) (work : I → TM.Tape A) (i : ℕ) :
    ℕ → TM.Config A (PC Q) (Index I)
  | 0 => slot blank mark start work 0 i
  | a+1 => slot blank mark start work i a

private theorem slot_range (hne : blank ≠ mark) (s : ℕ)
    (fits : ∀ i a, i+a ≤ s → ∀ j, lo j + (i+3 : ℕ) ≤ (counters blank mark i a work j).pos ∧
      (counters blank mark i a work j).pos ≤ hi j - (i+3 : ℕ))
    (attempts : ∀ i a, i+a < s →
      AttemptReturns blank mark start trial accept work lo hi P answer charge i a)
    (i k : ℕ) (h : i+k ≤ s) :
    delivered M lo hi P (rangeStart blank mark start work i k) (slotAt 0 (i+k))
      (Schedule.slotCost (fun i a => charge i a + (i+3)) i k) (Schedule.slots answer i k) := by
  induction k generalizing i with
  | zero =>
    simp only [rangeStart,Nat.add_zero,Schedule.slotCost,Schedule.slots,delivered]
    refine ⟨0,le_rfl,.nil _,?_⟩
    intro t ht z hz j
    obtain rfl : t = 0 := by omega
    have := trace_endpoint_unique hz (.nil _)
    subst z
    obtain ⟨hl,hr⟩ := fits 0 i (by omega) j
    change lo j ≤ (counters blank mark 0 i work j).pos ∧ (counters blank mark 0 i work j).pos ≤ hi j
    omega
  | succ k ih =>
    have pre := slot_run hne (fits i k (by omega)) (attempts i k (by omega))
    have post := ih (i+1) (by omega)
    have he : slotAt (next i k).1 (next i k).2 = rangeStart blank mark start work (i+1) k := by
      cases k <;> rfl
    rw [he] at pre
    have all := delivered_join pre post
    rw [show (i+1)+k=i+(k+1) by omega] at all
    exact all

/-- The first answer of all rounds up to `s` is obtained by a genuine halting
trace of the fixed scheduler. The full prefix fits the common fence, and all
slot costs, counter movement and return checks are charged. -/
theorem through_run (hne : blank ≠ mark) (s : ℕ)
    (fits : ∀ i a, i+a ≤ s → ∀ j, lo j + (i+3 : ℕ) ≤ (counters blank mark i a work j).pos ∧
      (counters blank mark i a work j).pos ≤ hi j - (i+3 : ℕ))
    (attempts : ∀ i a, i+a < s →
      AttemptReturns blank mark start trial accept work lo hi P answer charge i a)
    {v : α} (ok : Schedule.through answer s = some v) :
    ∃ z t, t ≤ Schedule.prefixCost (fun r =>
        Schedule.slotCost (fun i a => charge i a + (i+3)) 0 r) s ∧
      FencedRun M lo hi (slotAt 0 0) t z ∧ TM.advance M z = none ∧ P v z := by
  have pre (r : ℕ) (hr : r ≤ s) :
      delivered M lo hi P (slotAt 0 0) (slotAt 0 r)
        (Schedule.prefixCost (fun u => Schedule.slotCost (fun i a => charge i a+(i+3)) 0 u) r)
        (Schedule.through answer r) := by
    induction r with
    | zero =>
      refine ⟨0,le_rfl,.nil _,?_⟩
      intro k hk z hz j
      obtain rfl : k = 0 := by omega
      have := trace_endpoint_unique hz (.nil _)
      subst z
      obtain ⟨hl,hh⟩ := fits 0 0 (by omega) j
      change lo j ≤ (counters blank mark 0 0 work j).pos ∧ (counters blank mark 0 0 work j).pos ≤ hi j
      omega
    | succ r ih =>
      have previous := ih (by omega)
      have current := slot_range hne s fits attempts 0 (r+1) (by omega)
      simp only [Nat.zero_add] at current
      exact delivered_join previous current
  have h := pre s le_rfl
  rw [ok] at h
  obtain ⟨z,⟨t,ht,run⟩,halt,correct⟩ := h
  exact ⟨z,t,ht,run,halt,correct⟩

end ScheduleMachine

end NearSquareRoot
end Computability
end OAI
