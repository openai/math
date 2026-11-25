import OAI.Computability.MultitapeWeakETH.Machine

/-! # Freezing complete machine configurations at the physical deadline -/

namespace OAI.Computability.MultitapeWeakETH

open IntegerMultiplication

inductive Phase (M : Machine)
  | running (cfg : Config M)
  | halted (cfg : Config M)

def freezeStep (M : Machine) (choice : M.Choice) : Phase M → Phase M
  | .halted cfg => .halted cfg
  | .running cfg =>
    match TM.advance (M.rule choice) cfg with
    | none => .halted cfg
    | some next => .running next

def frozenRun (M : Machine) (coins : ℕ → M.Choice) (init : Config M) : ℕ → Phase M
  | 0 => .running init
  | t+1 => freezeStep M (coins t) (frozenRun M coins init t)

/-- A controller that has not yet observed a halt follows precisely the
unfrozen sequence of tape transitions. -/
theorem frozen_running_iff (M : Machine) (coins : ℕ → M.Choice) (init : Config M)
    (t : ℕ) (cfg : Config M) :
    frozenRun M coins init t = .running cfg ↔ run M coins init t = some cfg := by
  induction t generalizing cfg with
  | zero => simp [frozenRun,run]
  | succ t ih =>
    cases h : frozenRun M coins init t with
    | running p =>
      have hp := (ih p).mp h
      cases e : TM.advance (M.rule (coins t)) p <;> simp [run,frozenRun,h,freezeStep,hp,e]
    | halted p =>
      have hp : run M coins init t = none := by
        cases e : run M coins init t with
        | none => rfl
        | some v => have contra := (ih v).mpr e; simp [h] at contra
      simp [run,frozenRun,h,freezeStep,hp]

/-- The frozen configuration first observes the halt test at some u
strictly before its number of tests. All later steps preserve that exact
configuration, including tape contents and head positions. -/
theorem frozen_halted_iff (M : Machine) (coins : ℕ → M.Choice) (init : Config M)
    (t : ℕ) (cfg : Config M) :
    frozenRun M coins init t = .halted cfg ↔ ∃ u < t, run M coins init u = some cfg ∧
      TM.advance (M.rule (coins u)) cfg = none := by
  induction t with
  | zero => simp [frozenRun]
  | succ t ih =>
    have split : (∃ u < t+1, run M coins init u = some cfg ∧ TM.advance (M.rule (coins u)) cfg = none) ↔
        frozenRun M coins init t = .halted cfg ∨
        (frozenRun M coins init t = .running cfg ∧ TM.advance (M.rule (coins t)) cfg = none) := by
      rw [ih,frozen_running_iff]
      constructor
      · rintro ⟨u,hu,h⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu) with lt | rfl
        · exact Or.inl ⟨u,lt,h⟩
        · exact Or.inr h
      · rintro (⟨u,lt,h⟩ | h)
        · exact ⟨u,by omega,h⟩
        · exact ⟨t,by omega,h⟩
    rw [split]
    cases h : frozenRun M coins init t with
    | halted p => simp [frozenRun,h,freezeStep]
    | running p =>
      cases e : TM.advance (M.rule (coins t)) p with
      | none =>
        simp only [frozenRun,h,freezeStep,e,Phase.halted.injEq,reduceCtorEq,false_or,Phase.running.injEq]
        exact ⟨fun eq => ⟨eq,eq ▸ e⟩,And.left⟩
      | some next =>
        simp only [frozenRun,h,freezeStep,e,reduceCtorEq,false_or,Phase.running.injEq,false_iff,not_and]
        rintro rfl
        simp [e]

/-- Testing through T, including time zero, takes T+1 halt tests. The
machine pays for at most T moves. The final test supplies the output state. -/
theorem timely_frozen_iff (M : Machine) {n T : ℕ} (seed : Fin (T+1) → M.Choice)
    (x y out : Word n) :
    timely M T seed x y out ↔ ∃ cfg, frozenRun M
      (fun j => seed ⟨min j T,Nat.lt_succ_of_le (min_le_right ..)⟩) (initial M x y) (T+1) =
        .halted cfg ∧ M.accepts cfg.pc = true ∧ writes M cfg out := by
  simp only [frozen_halted_iff]
  constructor
  · rintro ⟨t,ht,cfg,runAt,stop,good⟩
    exact ⟨cfg,⟨t,Nat.lt_succ_of_le ht,runAt,by simpa only [min_eq_left ht] using stop⟩,good⟩
  · rintro ⟨cfg,⟨t,ht,runAt,stop⟩,good⟩
    have le := Nat.le_of_lt_succ ht
    exact ⟨t,le,cfg,runAt,by simpa only [min_eq_left le] using stop,good⟩

end OAI.Computability.MultitapeWeakETH
