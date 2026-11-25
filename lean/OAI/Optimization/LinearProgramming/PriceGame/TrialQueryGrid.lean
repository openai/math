import OAI.Optimization.LinearProgramming.PriceGame.ComputationIO
import OAI.Optimization.LinearProgramming.PriceGame.StatesFeedback
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionSchedule

/-! Branchwise invariants for intermediate outputs and query encodings in recursive trials. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

universe u v

namespace Computation

variable {N R : ℕ} {α : Type u} {β : Type v} {anchor : Fin N}

/-- A branch-independent specification of every query and every possible return.
The invariant includes branches with inconsistent replies. -/
def Guarded (Q : Query N → Prop) (P : α → Prop) : Computation N α → Prop
  | .pure a => P a
  | .ask q next => Q q ∧ ∀ b, Guarded Q P (next b)

theorem guarded_bind {Q : Query N → Prop} {P : α → Prop} {S : β → Prop}
    {p : Computation N α} {f : α → Computation N β}
    (hp : p.Guarded Q P) (hf : ∀ a, P a → (f a).Guarded Q S) : (p.bind f).Guarded Q S := by
  induction p with
  | pure a => exact hf _ hp
  | ask q next ih => exact ⟨hp.1, fun b => ih b (hp.2 b)⟩

theorem guarded_map {Q : Query N → Prop} {P : α → Prop} {S : β → Prop}
    {p : Computation N α} {f : α → β}
    (hp : p.Guarded Q P) (hf : ∀ a, P a → S (f a)) : (p.map f).Guarded Q S :=
  guarded_bind hp (fun a ha => show Guarded Q S (.pure (f a)) from hf a ha)

theorem guarded_mono {Q Q' : Query N → Prop} {P P' : α → Prop} {p : Computation N α}
    (hp : p.Guarded Q P) (hq : ∀ q, Q q → Q' q) (hr : ∀ a, P a → P' a) : p.Guarded Q' P' := by
  induction p with
  | pure a => exact hr _ hp
  | ask q next ih => exact ⟨hq _ hp.1, fun b => ih b (hp.2 b)⟩

theorem Guarded.allQueries {Q : Query N → Prop} {P : α → Prop} {p : Computation N α}
    (hp : p.Guarded Q P) : p.AllQueries Q := by
  induction p with
  | pure => exact True.intro
  | ask q next ih => exact ⟨hp.1, fun b => ih b (hp.2 b)⟩

theorem guarded_true_of_allQueries {Q : Query N → Prop} {p : Computation N α}
    (hp : p.AllQueries Q) : p.Guarded Q (fun _ => True) := by
  induction p with
  | pure => exact True.intro
  | ask q next ih => exact ⟨hp.1, fun b => ih b (hp.2 b)⟩

theorem Guarded.run {Q : Query N → Prop} {P : α → Prop} {p : Computation N α}
    (hp : p.Guarded Q P) (reply : List (Query N × Bool) → Query N → Bool)
    (history : List (Query N × Bool)) : P (p.run reply history) := by
  induction p generalizing history with
  | pure => exact hp
  | ask q next ih => exact ih _ (hp.2 _) _

theorem guarded_iterate (step : α → Computation N α) (Q : Query N → Prop) (I : ℕ → α → Prop)
    (n t : ℕ) (a : α) (ha : I t a)
    (hstep : ∀ j, t ≤ j → j < t+n → ∀ x, I j x → (step x).Guarded Q (I (j+1))) :
    (iterate step n a).Guarded Q (I (t+n)) := by
  induction n generalizing t a with
  | zero => simpa only [iterate, Nat.add_zero, Guarded] using ha
  | succ n ih =>
    rw [iterate]
    apply guarded_bind (hstep t le_rfl (by omega) a ha)
    intro x hx
    have hr := ih (t+1) x hx (fun j hj hl => hstep j (by omega) (by omega))
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using hr

end Computation

namespace TrialExecution

variable {N : ℕ} {α : Type u}

/-- A whole-prefix invariant can mention the accumulated weights or earlier
receipts. It is required only on prefixes obtained by the actual schedule. -/
theorem runSchedule_guarded_prefix (P : (j : ℕ) → (Fin j → α) → α → Prop)
    (step : ∀ j xs, Computation N {y // P j xs y}) (n : ℕ) (Q : Query N → Prop)
    (I : (j : ℕ) → Schedule P j → Prop)
    (base : I 0 ⟨Fin.elim0, fun i => i.elim0⟩)
    (hstep : ∀ j < n, ∀ xs : Schedule P j, I j xs →
      (step j xs.val).Guarded Q (fun x => I (j+1) (snocSchedule P xs x))) :
    (runSchedule P step n).Guarded Q (I n) := by
  induction n with
  | zero => exact base
  | succ n ih =>
    rw [runSchedule]
    apply Computation.guarded_bind (ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj)))
    intro xs hx
    exact Computation.guarded_map (hstep n (Nat.lt_succ_self _) xs hx) (fun _ hp => hp)

theorem runSchedule_guarded_of_valid_prefix (P : (j : ℕ) → (Fin j → α) → α → Prop)
    (step : ∀ j xs, Computation N {y // P j xs y}) (n : ℕ) (Q : Query N → Prop)
    (I : ℕ → α → Prop)
    (hstep : ∀ j < n, ∀ xs : Schedule P j, (∀ i : Fin j, I i.val (xs.val i)) →
      (step j xs.val).Guarded Q (fun x => I j x.val)) :
    (runSchedule P step n).Guarded Q (fun xs => ∀ i : Fin n, I i.val (xs.val i)) := by
  apply runSchedule_guarded_prefix P step n Q (fun j xs => ∀ i : Fin j, I i.val (xs.val i))
    (fun i => i.elim0)
  intro j hj xs hx
  apply Computation.guarded_mono (hstep j hj xs hx) (fun _ h => h)
  intro x hxi i
  cases i using Fin.lastCases with
  | cast a => simpa [snocSchedule] using hx a
  | last => simpa [snocSchedule] using hxi

/-- Each step only needs its invariant on prefixes that already passed verification.
The fresh output may depend on the actual prefix in both its value and its subtype. -/
theorem runSchedule_guarded (P : (j : ℕ) → (Fin j → α) → α → Prop)
    (step : ∀ j xs, Computation N {y // P j xs y}) (n : ℕ) (Q : Query N → Prop)
    (I : ℕ → α → Prop)
    (hstep : ∀ j < n, ∀ xs : Fin j → α, (∀ i : Fin j, I i.val (xs i)) →
      (step j xs).Guarded Q (fun x => I j x.val)) :
    (runSchedule P step n).Guarded Q (fun xs => ∀ i : Fin n, I i.val (xs.val i)) := by
  exact runSchedule_guarded_of_valid_prefix P step n Q I (fun j hj xs => hstep j hj xs.val)

end TrialExecution

namespace States

variable {N : ℕ} {J : Type}

theorem Path.pricesSatisfy_mono {I J : Type u} (p : Path I J) {P S : ℚ → Prop}
    (hp : p.pricesSatisfy P) (hs : ∀ a, P a → S a) : p.pricesSatisfy S := by
  induction p with
  | root => exact True.intro
  | extend _ _ _ ih => exact ⟨ih hp.1, fun j => hs _ (hp.2 j)⟩

/-- Mapping through a median keeps any scalar predicate satisfied by its three inputs,
even when the predicate is not closed under arithmetic. -/
theorem parentPrices_satisfy (P : ℚ → Prop) (y : J → ℚ) (x : J × Bool → ℚ)
    (hy : ∀ j, P (y j)) (hx : ∀ j, P (x j)) (i : J) : P (parentPrices y x i) := by
  simp only [parentPrices, median₃, max_def, min_def]
  split_ifs <;> first | exact hy _ | exact hx _

theorem feedbackAt_allQueries (P : ℚ → Prop) (p : Path (Fin N) J) (y : J → ℚ)
    (x : J × Bool → ℚ) (i : J) (bases : p.pricesSatisfy P)
    (hy : ∀ j, P (y j)) (hx : ∀ j, P (x j)) :
    (Computation.ofTree (feedbackAt p y x i)).AllQueries (fun q => ∀ j, P (q.prices j)) := by
  simp only [feedbackAt]
  split_ifs
  · exact True.intro
  · exact True.intro
  · exact ⟨rootQuery_pricesSatisfy P p bases _ (parentPrices_satisfy P y x hy hx) i, fun _ => True.intro⟩

/-- Under arbitrary root oracle replies all coordinates of every query belong to the
given predicate, for instance the grid of allowed rationals of bounded magnitude. -/
theorem feedbackAll_guarded {l : ℕ} (P : ℚ → Prop) (p : Path (Fin N) (Mass.Vertex N l))
    (y : Mass.Vertex N l → ℚ) (x : Mass.Vertex N (l+1) → ℚ)
    (bases : p.pricesSatisfy P) (hy : ∀ j, P (y j)) (hx : ∀ j, P (x j)) :
    (feedbackAll p y x).Guarded (fun q => ∀ j, P (q.prices j)) (fun _ => True) := by
  apply Computation.guarded_true_of_allQueries
  apply Computation.allQueries_map
  exact Computation.allQueries_traverse _ _ (fun i _ => feedbackAt_allQueries P p y x i bases hy hx)

end States
end PriceGame
end LinearProgramming
end Optimization
end OAI
