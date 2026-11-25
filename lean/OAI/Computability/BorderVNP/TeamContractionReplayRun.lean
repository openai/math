import OAI.Computability.BorderVNP.TeamPrivateFragment

/-! # Exact terminal witnesses for a deterministic replay table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.Replay

open VPVNP.RAMTape

variable {K Q : Type*} [DecidableEq K]

private theorem step_unique {C : StackCode K Q} {q s q₁ s₁ q₂ s₂}
    (h₁ : StackStep C q s q₁ s₁) (h₂ : StackStep C q s q₂ s₂) : q₁ = q₂ ∧ s₁ = s₂ := by
  cases h₁ <;> cases h₂ <;> simp_all

/-- Two replay runs from the same tape contents to actual halting instructions have
identical elapsed time, terminal control (including the unread choice suffix), and stacks. -/
theorem terminal_unique {C : StackCode K Q} {q s q₁ s₁ q₂ s₂ m n a b}
    (r₁ : StackRuns C m q s q₁ s₁) (r₂ : StackRuns C n q s q₂ s₂)
    (h₁ : C q₁ = .halt a) (h₂ : C q₂ = .halt b) : m = n ∧ q₁ = q₂ ∧ s₁ = s₂ := by
  induction r₁ generalizing n with
  | nil =>
    cases r₂ with
    | nil => exact ⟨rfl,rfl,rfl⟩
    | cons step _ => cases step <;> simp_all
  | cons step _ ih =>
    cases r₂ with
    | nil => cases step <;> simp_all
    | cons other tail =>
      obtain ⟨rfl,rfl⟩ := step_unique step other
      obtain ⟨he,hl,hs⟩ := ih tail h₁
      exact ⟨congrArg Nat.succ he,hl,hs⟩

/-- Read an accepting terminal label of a deterministic table within its physical clock.
An unresolved choice has no deterministic witness. -/
def observe (C : StackCode K Q) (label : Q → Option Bool) : ℕ → Q → Stacks K → Option Bool
  | 0, _, _ => none
  | n+1, q, s => match C q with
    | .push k b next => observe C label n next (Function.update s k (b :: s k))
    | .pop k f => observe C label n (f (s k).head?) (Function.update s k (s k).tail)
    | .goto next => observe C label n next s
    | .choose .. => none
    | .halt a => if a then label q else none

private theorem observe_runs {C : StackCode K Q} {m q s q' s'} (r : StackRuns C m q s q' s')
    (label : Q → Option Bool) (t : ℕ) : observe C label (t+m) q s = observe C label t q' s' := by
  induction r with
  | nil => rfl
  | cons step _ ih => cases step <;> simp_all [observe]

/-- A nonzero observation requires an actual deterministic run to an accepting halt.
The halt itself consumes one clock tick. -/
theorem observe_iff (C : StackCode K Q) (label : Q → Option Bool) (t : ℕ) (q : Q) (s : Stacks K) (z : Bool) :
    observe C label t q s = some z ↔
      ∃ k < t, ∃ u out, StackRuns C k q s u out ∧ C u = .halt true ∧ label u = some z := by
  constructor
  · induction t generalizing q s with
    | zero => simp [observe]
    | succ t ih =>
      intro h
      have extend {u next} (step : StackStep C q s u next) (val : observe C label t u next = some z) :
          ∃ k < t+1, ∃ v out, StackRuns C k q s v out ∧ C v = .halt true ∧ label v = some z := by
        obtain ⟨k,hk,v,out,run,halt,hlabel⟩ := ih u next val
        exact ⟨k+1,by omega,v,out,.cons step run,halt,hlabel⟩
      cases hc : C q with
      | push i b u => exact extend (.push hc) (by simpa [observe,hc] using h)
      | pop i f => exact extend (.pop hc) (by simpa [observe,hc] using h)
      | goto u => exact extend (.goto hc) (by simpa [observe,hc] using h)
      | choose low high => simp [observe,hc] at h
      | halt a =>
        cases a
        · simp [observe,hc] at h
        · exact ⟨0,Nat.zero_lt_succ _,q,s,.nil ..,hc,by simpa [observe,hc] using h⟩
  · rintro ⟨k,hk,u,out,run,halt,hlabel⟩
    have he : t = (t-(k+1)+1)+k := by omega
    rw [he,observe_runs run,observe,halt]
    exact hlabel

end TeamContraction.Replay

end BorderVNP
end Computability
end OAI
