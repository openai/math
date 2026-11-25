import OAI.Optimization.LinearProgramming.PriceGame.ControlData
import OAI.Optimization.LinearProgramming.PriceGame.ControlPrefix
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionSchedule

/-! Finite traces of all queries and answers. No hidden-oracle assumption is needed
to compile a trace, including the traces through an adaptive schedule. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

universe u v

variable {N : ℕ} {α : Type u} {β : Type v}

/-- Traces keep the price rows and designations in the first-order wire representation. -/
inductive Emits : Computation N α → List (PackedQuery × Bool) → α → Prop where
  | pure (a : α) : Emits (.pure a) [] a
  | ask {q : Query N} {k : Bool → Computation N α} {tr a} (b : Bool)
      (rest : Emits (k b) tr a) : Emits (.ask q k) ((packQuery q,b)::tr) a

theorem Emits.bind_inv {p : Computation N α} {f : α → Computation N β} {tr b}
    (e : Emits (p.bind f) tr b) :
    ∃ pre a post, tr = pre++post ∧ Emits p pre a ∧ Emits (f a) post b := by
  induction p generalizing tr with
  | pure a => exact ⟨[],a,tr,rfl,.pure a,e⟩
  | ask q next ih =>
    rw [Computation.bind_ask] at e
    cases e with
    | ask reply rest =>
      obtain ⟨pre,a,post,rfl,left,right⟩ := ih reply rest
      exact ⟨(packQuery q,reply)::pre,a,post,rfl,.ask reply left,right⟩

theorem Emits.map_inv {p : Computation N α} {f : α → β} {tr b} (e : Emits (p.map f) tr b) :
    ∃ a, Emits p tr a ∧ f a = b := by
  obtain ⟨pre,a,post,rfl,left,right⟩ := Emits.bind_inv e
  cases right
  exact ⟨a,by simpa using left,rfl⟩

theorem Emits.bind {p : Computation N α} {f : α → Computation N β} {tr a post b}
    (e : Emits p tr a) (rest : Emits (f a) post b) : Emits (p.bind f) (tr++post) b := by
  induction e with
  | pure => exact rest
  | ask reply before ih => exact .ask reply (ih rest)

theorem Emits.map {p : Computation N α} {f : α → β} {tr a} (e : Emits p tr a) :
    Emits (p.map f) tr (f a) := by
  simpa only [Computation.map, List.append_nil] using e.bind (f := fun a => .pure (f a)) (.pure (f a))

theorem Emits.observe_tape {p : Computation N α} {tr a} (e : Emits p tr a) (tail : List Bool) :
    observe p (tr.map Prod.snd ++ tail) = .inl (a,tail) := by
  induction e with
  | pure => rfl
  | ask b _ ih => exact ih

theorem emits_run (p : Computation N α) (reply : List (Query N × Bool) → Query N → Bool)
    (history : List (Query N × Bool)) : ∃ tr, Emits p tr (p.run reply history) := by
  induction p generalizing history with
  | pure a => exact ⟨[], .pure _⟩
  | ask q next ih =>
    obtain ⟨tr,h⟩ := ih (reply history q) ((q,reply history q)::history)
    exact ⟨(packQuery q,reply history q)::tr,.ask _ h⟩

/-- A full schedule trace is a chronological snoc sequence of traces of actual calls,
including the prefix-dependent proof attached to every returned call. -/
inductive ScheduleTrace (P : (j : ℕ) → (Fin j → α) → α → Prop)
    (step : ∀ j xs, Computation N {y // P j xs y}) :
    (n : ℕ) → List (PackedQuery × Bool) → TrialExecution.Schedule P n → Prop where
  | nil : ScheduleTrace P step 0 [] ⟨Fin.elim0, fun i => i.elim0⟩
  | snoc {n tr preTr} {xs : TrialExecution.Schedule P n} {x : {y // P n xs.val y}}
      (old : ScheduleTrace P step n preTr xs) (last : Emits (step n xs.val) tr x) :
      ScheduleTrace P step (n+1) (preTr++tr) (TrialExecution.snocSchedule P xs x)

theorem scheduleTrace_of_emits (P : (j : ℕ) → (Fin j → α) → α → Prop)
    (step : ∀ j xs, Computation N {y // P j xs y}) (n : ℕ)
    {tr out} (e : Emits (TrialExecution.runSchedule P step n) tr out) :
    ScheduleTrace P step n tr out := by
  induction n generalizing tr with
  | zero => cases e; exact .nil
  | succ n ih =>
    rw [TrialExecution.runSchedule] at e
    obtain ⟨left,xs,right,rfl,first,second⟩ := e.bind_inv
    obtain ⟨x,hx,rfl⟩ := second.map_inv
    exact .snoc (ih first) hx

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
