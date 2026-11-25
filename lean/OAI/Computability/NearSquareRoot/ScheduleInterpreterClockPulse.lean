import OAI.Computability.NearSquareRoot.ScheduleClock
import OAI.Computability.NearSquareRoot.VisitedCells

/-!
# Ticks issued by the binary budget clock

A visit to the ready state marks one interpreter step. We count the outgoing
transition from that state. The intermediate write phase in the stack-to-tape
simulation issues no tick.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ScheduleClock

open IntegerMultiplication

abbrev ClockConfiguration := TM.Config (Option Bool) (SM.PC Bool State Bool) Bool

def physicalPulse : SM.PC Bool State Bool → Bool
  | .inl .ready => true
  | _ => false

/-- The natural number records issued pulses externally to the physical clock. -/
def countedStep (z : ClockConfiguration × ℕ) : Option (ClockConfiguration × ℕ) :=
  (TM.advance PhysicalRule z.1).map fun c => (c, z.2 + (physicalPulse z.1.pc).toNat)

private def remaining (x : SM.Config Bool State Bool) : ℕ :=
  let w := 2 ^ (x.stack true).length
  let v := value (x.stack false)
  match x.pc with
  | .initialize | .rewind => w*(v+1)
  | .ready => w*v + 1
  | .borrow => w*v
  | .writeZero => w*(2*v+1)
  | .expired => 0

private theorem remaining_step {x y : SM.Config Bool State Bool} (h : Step x = some y) :
    remaining y + (physicalPulse (.inl x.pc)).toNat = remaining x := by
  obtain ⟨q,f⟩ := x
  cases q <;> cases h₁ : f false <;> cases h₂ : f true <;>
    simp [Step, SM.advance, SM.tops, rule, h₁, h₂] at h <;>
    first
    | (subst y
       simp [remaining, physicalPulse, SM.perform, pair, SM.Action.perform, h₁, h₂, value, pow_succ]
       done)
    | (subst y
       simp [remaining, physicalPulse, SM.perform, pair, SM.Action.perform, h₁, h₂, value, pow_succ]
       ring)
    | skip
  case borrow.cons.nil b bs =>
    cases b <;> simp at h <;> subst y <;>
      simp [remaining, physicalPulse, SM.perform, pair, SM.Action.perform, h₁, h₂, value, pow_succ]
  case borrow.cons.cons b bs c cs =>
    cases b <;> simp at h <;> subst y <;>
      simp [remaining, physicalPulse, SM.perform, pair, SM.Action.perform, h₁, h₂, value, pow_succ]
    ring

private theorem counted_simulate {x y : SM.Config Bool State Bool} {n : ℕ}
    (hx : Trace Step x n y) (T : Bool → TM.Tape (Option Bool)) (he : SM.faithful x.stack T)
    (a : ℕ) :
    ∃ T' b, SM.faithful y.stack T' ∧ b + remaining y = a + remaining x ∧
      Trace countedStep (⟨.inl x.pc,T⟩,a) (2*n) (⟨.inl y.pc,T'⟩,b) := by
  induction hx generalizing T a with
  | nil => exact ⟨T, a, he, rfl, by simp only [Nat.mul_zero]; exact .nil _⟩
  | @cons x u z n h _ ih =>
    have hrem := remaining_step h
    cases hy : rule x.pc (SM.tops x) with
    | none => simp [Step, SM.advance, hy] at h
    | some y =>
      simp only [SM.advance, hy, Option.map_some, Option.some.injEq] at h
      subst u
      have ht : (fun i => (T i).view 0) = SM.tops x := by funext i; rw [he]; simp [SM.tops]
      let T₁ : Bool → TM.Tape (Option Bool) := fun i => (T i).apply ((y.2 i).first ((T i).view 0))
      let T₂ : Bool → TM.Tape (Option Bool) := fun i => (T₁ i).apply ((y.2 i).second ((T₁ i).view 0))
      have h₁ : TM.advance PhysicalRule ⟨.inl x.pc, T⟩ = some ⟨.inr y, T₁⟩ := by
        simp [TM.advance, PhysicalRule, SM.toTM, ht, hy, T₁]
      have h₂ : TM.advance PhysicalRule ⟨.inr y, T₁⟩ = some ⟨.inl y.1, T₂⟩ := rfl
      let a' := a + (physicalPulse (.inl x.pc)).toNat
      obtain ⟨T', b, he', hb, hh⟩ := ih T₂
        (fun i => (y.2 i).represent_perform (T i) (x.stack i) (he i)) a'
      refine ⟨T',b,he', ?_, ?_⟩
      · dsimp [a'] at hb
        omega
      · rw [show 2*(1+n) = 1+(1+2*n) by omega]
        exact Trace.cons (y := (⟨.inr y,T₁⟩,a')) (by simp [countedStep, h₁, a'])
          (Trace.cons (by simp only [countedStep, h₂, Option.map_some, physicalPulse,
                           Bool.toNat_false, Nat.add_zero]; rfl) hh)

/-- Every strict prefix of a budget has a physical witness with the exact pulse count. -/
theorem physical_prefix_pulses (e : List Bool) (v : ℕ) (hv : v < 2^e.length)
    (T : Bool → TM.Tape (Option Bool)) (hf : SM.faithful (cfg .initialize [] e).stack T) :
    ∃ t b' T', Trace countedStep (⟨.inl .initialize,T⟩,0) t (⟨.inl .ready,T'⟩,v) ∧
      SM.faithful (cfg .ready b' []).stack T' ∧ b'.length = e.length ∧
      value b' + v + 1 = 2^e.length ∧ t ≤ 2*(e.length + 1 + 6*v) ∧
      VisitsAtMost PhysicalRule ⟨.inl .initialize,T⟩ t (2*(e.length+3)) := by
  have hval := initial_value e.length
  obtain ⟨t,b',ht,hlen,hv',htime⟩ := ticks v (List.replicate e.length true) (by omega)
  have trace := (initialize_run e).trans ht
  obtain ⟨T',b,hf',hb,hm⟩ := counted_simulate trace T hf 0
  simp [remaining, cfg, pair, value] at hb
  have eb : b = v := by omega
  subst b
  refine ⟨_,b',T',hm,hf',by simpa using hlen,by omega,?_,physical_space trace T hf⟩
  simp [List.count_replicate] at htime
  omega

/-- Forgetting the pulse observer preserves the actual physical transition sequence. -/
theorem counted_trace_forget {x y : ClockConfiguration × ℕ} {n}
    (h : Trace countedStep x n y) : Trace (TM.advance PhysicalRule) x.1 n y.1 := by
  induction h with
  | nil => exact .nil _
  | @cons x z y n hx _ ih =>
    apply Trace.cons (y := z.1) _ ih
    cases h' : TM.advance PhysicalRule x.1 with
    | none => simp [countedStep, h'] at hx
    | some d =>
      simp only [countedStep, h', Option.map_some, Option.some.injEq] at hx
      subst z
      rfl

/-- Exactly the prescribed number of ready-state transitions occurs by expiration. -/
private theorem expiration_and_restore (e : List Bool) (T : Bool → TM.Tape (Option Bool))
    (hf : SM.faithful (cfg .initialize [] e).stack T) :
    ∃ t T', Trace countedStep (⟨.inl .initialize,T⟩,0) t (⟨.inl .expired,T'⟩,2^e.length) ∧
      (e = List.replicate e.length true → T' = T) ∧
      TM.advance PhysicalRule ⟨.inl .expired,T'⟩ = none ∧
      t ≤ 2*(e.length + 1 + 6*2^e.length) ∧
      VisitsAtMost PhysicalRule ⟨.inl .initialize,T⟩ t (2*(e.length+3)) := by
  let b := List.replicate e.length true
  have hval : value b + 1 = 2^e.length := initial_value _
  obtain ⟨t,b',ht,hlen,hv,htime⟩ := ticks (value b) b (le_refl _)
  have hval' : value b' = 0 := by omega
  have hlen' : b'.length = e.length := by simpa [b] using hlen
  rw [(zero_value b' hval').trans (congrArg (List.replicate · false) hlen')] at ht htime
  have hc := ((initialize_run e).trans ht).trans (timeout e.length)
  obtain ⟨T',c,hf',hb,hm⟩ := counted_simulate hc T hf 0
  simp [remaining, cfg, pair, value] at hb
  subst c
  have restored (markers : e = List.replicate e.length true) : T' = T := by
    obtain ⟨U,hu,hbottom,unobserved⟩ := simulateWithBottom hc T hf
    have ee := trace_endpoint_unique (counted_trace_forget hm) unobserved
    have eTU : T' = U := congrArg TM.Config.tape ee
    rw [eTU]
    funext i
    apply tape_eq_of_stack_restored (hu i) (hf i) (hbottom i)
    cases i with
    | false => rfl
    | true => exact markers.symm
  refine ⟨_,T',hm,restored,SM.simulate_halt (m := rule) (x := cfg .expired [] (List.replicate e.length true)) rfl hf',?_,physical_space hc T hf⟩
  simp [List.count_replicate,b] at htime
  dsimp [b] at hval ⊢
  omega

/-- Exactly the prescribed number of ready-state transitions occurs by expiration. -/
theorem physical_expiration_pulses (e : List Bool) (T : Bool → TM.Tape (Option Bool))
    (hf : SM.faithful (cfg .initialize [] e).stack T) :
    ∃ t T', Trace countedStep (⟨.inl .initialize,T⟩,0) t (⟨.inl .expired,T'⟩,2^e.length) ∧
      TM.advance PhysicalRule ⟨.inl .expired,T'⟩ = none ∧
      t ≤ 2*(e.length + 1 + 6*2^e.length) ∧
      VisitsAtMost PhysicalRule ⟨.inl .initialize,T⟩ t (2*(e.length+3)) := by
  obtain ⟨t,T',run,_,rest⟩ := expiration_and_restore e T hf
  exact ⟨t,T',run,rest⟩

/-- With standard unary markers an exhausted clock leaves both complete tapes and
their heads exactly as they were initially. They can be reused in the next attempt. -/
theorem physical_expiration_restored (a : ℕ) (T : Bool → TM.Tape (Option Bool))
    (hf : SM.faithful (cfg .initialize [] (List.replicate a true)).stack T) :
    ∃ t, Trace countedStep (⟨.inl .initialize,T⟩,0) t (⟨.inl .expired,T⟩,2^a) ∧
      TM.advance PhysicalRule ⟨.inl .expired,T⟩ = none ∧
      t ≤ 2*(a+1+6*2^a) ∧ VisitsAtMost PhysicalRule ⟨.inl .initialize,T⟩ t (2*(a+3)) := by
  obtain ⟨t,T',run,restore,halt,time,space⟩ := expiration_and_restore _ T hf
  have eq := restore (by simp)
  subst T'
  exact ⟨t,by simpa using run,halt,by simpa using time,by simpa using space⟩

end ScheduleClock

end NearSquareRoot
end Computability
end OAI
