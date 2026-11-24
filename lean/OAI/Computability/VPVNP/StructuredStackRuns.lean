import OAI.Computability.VPVNP.StructuredStackLink

/-!
# Exact deterministic runs of stack routines

Sequencing adds the costs of its components. A dispatch on the top symbol
consumes one instruction in addition to the run of the selected branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Routine

variable {K Q R M : Type*} [DecidableEq K]

theorem Runs.followedBy {a : Routine K Q} {b : Routine K R} {n m : ℕ} {s u out : Stacks K}
    (ha : a.Runs n s u) (hb : b.Runs m u out) : (a.followedBy b).Runs (n + m) s out :=
  (ha.link (a.followedBy b) Sum.inl (some (.inr b.entry)) (fun _ => rfl)).trans
    (hb.link (a.followedBy b) Sum.inr none (fun _ => rfl))

theorem runs_ret (s : Stacks K) : (ret : Routine K Unit).Runs 1 s s :=
  .cons (.goto rfl) (.nil ..)

theorem runs_push (k : K) (b : Bool) (s : Stacks K) :
    (push k b).Runs 1 s (Function.update s k (b :: s k)) :=
  .cons (.push rfl) (.nil ..)

variable (k : K) (missing : Routine K M) (low : Routine K Q) (high : Routine K R)
    {s out : Stacks K} {t : ℕ}

theorem runs_popCase_empty (hs : s k = []) (hm : missing.Runs t s out) :
    (popCase k missing low high).Runs (t + 1) s out := by
  let r := popCase k missing low high
  have h := hm.link r (Sum.inr ∘ Sum.inl) none (fun _ => rfl)
  have hup : Function.update s k [] = s := by rw [← hs, Function.update_eq_self]
  have he : StackStep r.standalone (some r.entry) s (some (.inr (.inl missing.entry))) s := by
    simpa only [hs, List.head?_nil, List.tail_nil, hup] using
      (StackStep.pop (code := r.standalone) (s := s) (q := some r.entry)
        (show r.standalone (some r.entry) = .pop k _ from rfl))
  exact .cons he h

theorem runs_popCase_false {tail : List Bool} (hs : s k = false :: tail)
    (hl : low.Runs t (Function.update s k tail) out) :
    (popCase k missing low high).Runs (t + 1) s out := by
  let r := popCase k missing low high
  have h := hl.link r (Sum.inr ∘ Sum.inr ∘ Sum.inl) none (fun _ => rfl)
  have he : StackStep r.standalone (some r.entry) s (some (.inr (.inr (.inl low.entry))))
      (Function.update s k tail) := by
    simpa only [hs, List.head?_cons, List.tail_cons] using
      (StackStep.pop (code := r.standalone) (s := s) (q := some r.entry)
        (show r.standalone (some r.entry) = .pop k _ from rfl))
  exact .cons he h

theorem runs_popCase_true {tail : List Bool} (hs : s k = true :: tail)
    (hh : high.Runs t (Function.update s k tail) out) :
    (popCase k missing low high).Runs (t + 1) s out := by
  let r := popCase k missing low high
  have h := hh.link r (Sum.inr ∘ Sum.inr ∘ Sum.inr) none (fun _ => rfl)
  have he : StackStep r.standalone (some r.entry) s (some (.inr (.inr (.inr high.entry))))
      (Function.update s k tail) := by
    simpa only [hs, List.head?_cons, List.tail_cons] using
      (StackStep.pop (code := r.standalone) (s := s) (q := some r.entry)
        (show r.standalone (some r.entry) = .pop k _ from rfl))
  exact .cons he h

end RAMTape.Routine

end VPVNP
end Computability
end OAI
