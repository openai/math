import OAI.Optimization.LinearProgramming.PriceGame.TrialQueryTraces

/-! Extending a finite execution prefix of an adaptive schedule without changing
any completed value, designation, or reply. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

universe u

open TrialExecution
variable {N : ℕ} {α : Type u}

/-- Snoc a specific output of the actual next adaptive call. -/
theorem runSchedule_snoc_emits (P : (j : ℕ) → (Fin j → α) → α → Prop)
    (step : ∀ j xs, Computation N {x // P j xs x}) {m : ℕ} {xs : Schedule P m}
    {pre ev : List (PackedQuery × Bool)} {c : {x // P m xs.val x}}
    (first : Emits (runSchedule P step m) pre xs) (next : Emits (step m xs.val) ev c) :
    Emits (runSchedule P step (m+1)) (pre ++ ev) (snocSchedule P xs c) := by
  rw [runSchedule]
  exact first.bind (next.map (f := snocSchedule P xs))

/-- Every emitted prefix extends to a complete execution. The newly needed replies
can all be false; previously observed replies are copied verbatim. -/
theorem runSchedule_extend_emits (P : (j : ℕ) → (Fin j → α) → α → Prop)
    (step : ∀ j xs, Computation N {x // P j xs x}) {m n : ℕ} (h : m ≤ n)
    {tr : List (PackedQuery × Bool)} {xs : Schedule P m} (em : Emits (runSchedule P step m) tr xs) :
    ∃ tail, ∃ ys : Schedule P n, Emits (runSchedule P step n) (tr ++ tail) ys ∧
      ∀ i : Fin m, ys.val (Fin.castLE h i) = xs.val i := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨[],xs,by simpa using em,fun _ => rfl⟩
  | succ n hn ih =>
    obtain ⟨tail,ys,hy,hpres⟩ := ih
    let c := (step n ys.val).run (fun _ _ => false) []
    obtain ⟨ev,hnxt⟩ := emits_run (step n ys.val) (fun _ _ => false) []
    refine ⟨tail ++ ev, snocSchedule P ys c, ?_, ?_⟩
    · simpa only [List.append_assoc] using runSchedule_snoc_emits P step hy hnxt
    · intro i
      change (Fin.snoc ys.val c.val : Fin (n+1) → α) (Fin.castSucc (Fin.castLE hn i)) = _
      rw [Fin.snoc_castSucc]
      exact hpres i

/-- The extension can be required to pass through a particular observed next
value and its entire query/reply segment. -/
theorem runSchedule_extend_through_emits (P : (j : ℕ) → (Fin j → α) → α → Prop)
    (step : ∀ j xs, Computation N {x // P j xs x}) {m n : ℕ} (h : m+1 ≤ n)
    {xs : Schedule P m} {pre ev : List (PackedQuery × Bool)} {c : {x // P m xs.val x}}
    (first : Emits (runSchedule P step m) pre xs) (next : Emits (step m xs.val) ev c) :
    ∃ tail, ∃ ys : Schedule P n, Emits (runSchedule P step n) (pre ++ ev ++ tail) ys ∧
      (∀ i : Fin m, ys.val (Fin.castLE ((Nat.le_succ _).trans h) i) = xs.val i) ∧
      ys.val (Fin.castLE h (Fin.last m)) = c.val := by
  obtain ⟨tail,ys,hy,keep⟩ := runSchedule_extend_emits P step h (runSchedule_snoc_emits P step first next)
  refine ⟨tail,ys,hy,?_,?_⟩
  · intro i
    have hi : Fin.castLE h i.castSucc = Fin.castLE ((Nat.le_succ _).trans h) i := by
      apply Fin.ext
      simp
    simpa only [snocSchedule, Fin.snoc_castSucc, hi] using keep i.castSucc
  · simpa only [snocSchedule, Fin.snoc_last] using keep (Fin.last m)

/-- Specialization at a designated index in the complete schedule. The prefix
passed to this call is exactly the one that yielded the chosen output. -/
theorem runSchedule_extend_at_emits (P : (j : ℕ) → (Fin j → α) → α → Prop)
    (step : ∀ j xs, Computation N {x // P j xs x}) {n : ℕ} (j : Fin n)
    {xs : Schedule P j.val} {pre ev : List (PackedQuery × Bool)} {c : {x // P j.val xs.val x}}
    (first : Emits (runSchedule P step j.val) pre xs) (next : Emits (step j.val xs.val) ev c) :
    ∃ tail, ∃ ys : Schedule P n, Emits (runSchedule P step n) (pre ++ ev ++ tail) ys ∧
      «prefix» ys.val j = xs.val ∧ ys.val j = c.val := by
  obtain ⟨tail,ys,hy,hpre,hc⟩ := runSchedule_extend_through_emits P step j.isLt first next
  exact ⟨tail,ys,hy,funext hpre,hc⟩

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
