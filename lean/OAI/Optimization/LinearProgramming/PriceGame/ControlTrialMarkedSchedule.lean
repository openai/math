import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialMarked
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialSchedule

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open TrialExecution

variable {N : ℕ} {A I P C R : Type}

theorem ScheduleTrace.emits {v : (j : ℕ) → (Fin j → A) → A → Prop}
    {action : ∀ j xs, Computation N {y // v j xs y}} {j tr out}
    (h : ScheduleTrace v action j tr out) : Emits (runSchedule v action j) tr out := by
  induction h with
  | nil => exact .pure _
  | snoc _ single ih =>
    rw [runSchedule]
    exact ih.bind (single.map (f := snocSchedule v _))

def MarkedRefinesStep (pcOK : PC I P R C → Prop) (frameOK : Frame I P C → Prop)
    (ops : Kernel I P R C PackedQuery) (calls fuel rem : ℕ) (input : I)
    (rows : List C) (tr : List (PackedQuery × Bool)) (c : C) : Prop :=
  let prep := ops.prepare input rows
  let frame : Frame I P C := ⟨fuel,rem,input,rows,prep⟩
  ∃ left middle returned, tr = left++middle ∧
    pcOK (.schedule fuel (rem+1) input rows) ∧ frameOK frame ∧
    (∀ tape, pcOK (.feedback frame returned tape)) ∧
    MarkedEvaluates pcOK frameOK ops calls (.node fuel (ops.childInput input prep)) left returned ∧
    Scan (ops.finish input rows prep returned) [] middle c

theorem ScheduleTrace.prependMarked {v : (j : ℕ) → (Fin j → A) → A → Prop}
    {act : ∀ j xs, Computation N {y // v j xs y}}
    (pcOK : PC I P R C → Prop) (frameOK : Frame I P C → Prop)
    (ops : Kernel I P R C PackedQuery) (calls fuel : ℕ) (input : I) (encode : A → C)
    (href : ∀ j rem, j+rem+1 = calls → ∀ (xs : Schedule v j) (pre : List (PackedQuery × Bool)),
      Emits (runSchedule v act j) pre xs → ∀ c tr, Emits (act j xs.val) tr c →
        MarkedRefinesStep pcOK frameOK ops calls fuel rem input (List.ofFn (fun i => encode (xs.val i))) tr (encode c.val))
    {j tr xs} (s : ScheduleTrace v act j tr xs) :
    ∀ {rem tail result}, j+rem = calls →
      MarkedEvaluates pcOK frameOK ops calls (.rounds fuel rem input (List.ofFn fun i => encode (xs.val i))) tail result →
      MarkedEvaluates pcOK frameOK ops calls (.rounds fuel (j+rem) input []) (tr++tail) result := by
  induction s with
  | nil =>
    intro rem tail result eq rest
    simpa using rest
  | @snoc n tr pre xs x old last ih =>
    intro rem tail result eq rest
    obtain ⟨left,middle,returned,rfl,hs,hf,hscan,child,fb⟩ := href n rem (by omega) xs pre old.emits x tr last
    have packed : List.ofFn (fun i => encode ((snocSchedule v xs x).val i)) =
        (List.ofFn fun i => encode (xs.val i)) ++ [encode x.val] := by
      rw [List.ofFn_succ', List.concat_eq_append]
      simp [snocSchedule]
    rw [packed] at rest
    have total := ih (by omega : n+(rem+1)=calls) (MarkedEvaluates.call hs hf hscan child fb rest)
    simpa only [Nat.succ_add,Nat.add_succ,List.append_assoc] using total

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
