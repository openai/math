import OAI.Computability.VPVNP.StructuredStackTotal
import OAI.Computability.VPVNP.RAMTapeSpace

/-! # A space invariant on every branch of a returning stack routine

The caller checks its own invariant at a normal return. At each active
instruction the callee checks the current bank and both successors of a
binary choice. This gives a simultaneous clock and peak-space contract.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Routine

variable {K Q R : Type*} [DecidableEq K]

/-- Every branch from the given local control checks the stack invariant at each active
instruction and reaches a halt or a return within the fuel budget. At a return the
continuation receives the remaining fuel and stack bank. -/
def SafeFrom (r : Routine K Q) (safe : Stacks K → Prop) (cont : ℕ → Stacks K → Prop) :
    ℕ → Option Q → Stacks K → Prop
  | t, none, s => cont t s
  | 0, some _, _ => False
  | t+1, some q, s => safe s ∧
    match r.code q with
    | .push k b next => r.SafeFrom safe cont t next (Function.update s k (b :: s k))
    | .pop k next => r.SafeFrom safe cont t (next (s k).head?) (Function.update s k (s k).tail)
    | .goto next => r.SafeFrom safe cont t next s
    | .choose a b => r.SafeFrom safe cont t a s ∧ r.SafeFrom safe cont t b s
    | .halt _ => True

/-- The all-branches stack invariant and fuel bound for a routine started at its entry label. -/
abbrev Safe (r : Routine K Q) (safe : Stacks K → Prop) (cont : ℕ → Stacks K → Prop)
    (t : ℕ) (s : Stacks K) := r.SafeFrom safe cont t (some r.entry) s

@[simp] theorem safeFrom_none (r : Routine K Q) (safe : Stacks K → Prop)
    (c : ℕ → Stacks K → Prop) (t : ℕ) (s : Stacks K) : r.SafeFrom safe c t none s ↔ c t s := by
  cases t <;> rfl

theorem safeFrom_install (outer : Routine K R) (inner : Routine K Q)
    (label : Q → R) (resume : Option R) (h : ∀ q, outer.code (label q) = inner.install label resume q)
    (safe : Stacks K → Prop) (c : ℕ → Stacks K → Prop) (t : ℕ) (q : Option Q) (s : Stacks K) :
    outer.SafeFrom safe c t (q.elim resume (some ∘ label)) s ↔
      inner.SafeFrom safe (fun n st => outer.SafeFrom safe c n resume st) t q s := by
  induction t generalizing q s with
  | zero => cases q <;> rfl
  | succ t ih =>
    cases q with
    | none => rfl
    | some q =>
      simp only [Option.elim_some, Function.comp_apply, SafeFrom, h, install]
      cases inner.code q <;> simp only [StackOp.rename, id_eq, Function.comp_apply, ih]

theorem safe_followedBy (a : Routine K Q) (b : Routine K R) (safe : Stacks K → Prop)
    (c : ℕ → Stacks K → Prop) (t : ℕ) (s : Stacks K) :
    (a.followedBy b).Safe safe c t s ↔ a.Safe safe (b.Safe safe c) t s := by
  have second (n : ℕ) (st : Stacks K) :
      (a.followedBy b).SafeFrom safe c n (some (.inr b.entry)) st ↔ b.Safe safe c n st := by
    simpa only [Option.elim_some, Function.comp_apply, safeFrom_none] using
      safeFrom_install (a.followedBy b) b Sum.inr none (fun _ => rfl) safe c n (some b.entry) st
  change (a.followedBy b).SafeFrom safe c t (some (.inl a.entry)) s ↔
    a.SafeFrom safe (fun n st => b.Safe safe c n st) t (some a.entry) s
  simpa only [Option.elim_some, Function.comp_apply, second] using
    safeFrom_install (a.followedBy b) a Sum.inl (some (.inr b.entry)) (fun _ => rfl)
      safe c t (some a.entry) s

theorem SafeFrom.allStops {r : Routine K Q} {safe c d t q s}
    (h : r.SafeFrom safe c t q s) (hd : ∀ n u, c n u → d n u) : r.AllStopsFrom d t q s := by
  induction t generalizing q s with
  | zero => cases q <;> simp_all [SafeFrom, AllStopsFrom]
  | succ t ih =>
    cases q with
    | none => exact hd _ _ ((safeFrom_none ..).mp h)
    | some q =>
      simp only [SafeFrom] at h
      simp only [AllStopsFrom]
      cases he : r.code q <;> rw [he] at h <;> simp only at h ⊢
      all_goals first | exact ih h.2 | exact ⟨ih h.2.1, ih h.2.2⟩

theorem SafeFrom.stopsWithin {r : Routine K Q} {safe c t q s} (outcome : Bool)
    (h : r.SafeFrom safe c t q s) (hc : ∀ n u, c n u → 0 < n) :
    StopsWithin (r.close outcome) t q s :=
  (stopsWithin_close_iff ..).mpr (h.allStops hc)

/-- Every reachable bank satisfies the invariant, including a normal return
when the caller's continuation enforces it there. -/
theorem SafeFrom.reach {r : Routine K Q} {safe c t q s} (outcome : Bool)
    (h : r.SafeFrom safe c t q s) (hc : ∀ n u, c n u → safe u) {v u}
    (path : StackCompiler.Reach (r.close outcome) q s v u) : safe u := by
  have certificate : ∃ n, r.SafeFrom safe c n v u := by
    induction path with
    | initial => exact ⟨t, h⟩
    | @step a x b y _ hs ih =>
      obtain ⟨n, hn⟩ := ih
      cases a with
      | none => cases hs <;> contradiction
      | some a =>
        cases n with
        | zero => exact False.elim hn
        | succ n =>
          refine ⟨n, ?_⟩
          cases hs with
          | push he | pop he | goto he =>
            change r.code a = _ at he
            rw [SafeFrom, he] at hn
            exact hn.2
    | @low a x l b _ he ih | @high a x l b _ he ih =>
      obtain ⟨n, hn⟩ := ih
      cases a with
      | none => contradiction
      | some a =>
        cases n with
        | zero => exact False.elim hn
        | succ n =>
          change r.code a = _ at he
          rw [SafeFrom, he] at hn
          first | exact ⟨n, hn.2.1⟩ | exact ⟨n, hn.2.2⟩
  obtain ⟨n, hn⟩ := certificate
  cases v with
  | none => exact hc n u ((safeFrom_none ..).mp hn)
  | some v => cases n with
    | zero => exact False.elim hn
    | succ n => exact hn.1

end RAMTape.Routine

end VPVNP
end Computability
end OAI
