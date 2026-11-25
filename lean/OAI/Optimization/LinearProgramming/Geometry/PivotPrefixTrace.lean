import OAI.Optimization.LinearProgramming.Geometry.Pivot

/-! Append the literal answered and interrupted transcripts of successive pivot stages. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

namespace MinorQuery.Run

variable {κ α β : Type*}

private def After (k : α → MinorQuery κ β) (res : Sum κ α) (rest : List (κ × ℚ)) (out : Sum κ β) : Prop :=
  match res with
  | .inl key => rest = [] ∧ out = Sum.inl key
  | .inr val => Run (k val) rest out

private theorem appendAux {p : MinorQuery κ α} (k : α → MinorQuery κ β)
    {first : List (κ × ℚ)} {res : Sum κ α} (h : Run p first res)
    (rest : List (κ × ℚ)) (out : Sum κ β)
    (next : After k res rest out) : Run (p.bind k) (first++rest) out := by
  induction h with
  | done val => exact next
  | restart key cont =>
    rcases next with ⟨rfl,rfl⟩
    exact Run.restart _ _
  | answer key cont v tail ih => exact Run.answer _ _ v (ih next)

theorem bind_answer {p : MinorQuery κ α} {k : α → MinorQuery κ β} {xs ys a out}
    (h : Run p xs (.inr a)) (next : Run (k a) ys out) : Run (p.bind k) (xs++ys) out :=
  appendAux k h ys out next

theorem bind_restart {p : MinorQuery κ α} (k : α → MinorQuery κ β) {xs key}
    (h : Run p xs (.inl key)) : Run (p.bind k) xs (.inl key) := by
  simpa only [List.append_nil] using appendAux k h [] (.inl key) ⟨rfl,rfl⟩

end MinorQuery.Run

variable {m n a : ℕ} {D : Matrix (Fin m) (Fin n) ℚ} {price : Fin n → ℚ}

/-- Append the transcript of one completed pivot step to the completed prefix. -/
theorem prefixRun_succ {ha : a+1 ≤ m} {rows : Fin a → PivotRow n} {row : PivotRow n} {xs ys}
    (hp : MinorQuery.Run (pivotPrefix D price a (by omega)) xs (.inr (some rows)))
    (hr : MinorQuery.Run (pivotStep (D.submatrix (Fin.castLE ha) id) (fun j => (rows j).pivot) price) ys (.inr (some row))) :
    MinorQuery.Run (pivotPrefix D price (a+1) ha) (xs++ys) (.inr (some (Fin.lastCases row rows))) := by
  rw [pivotPrefix]
  apply hp.bind_answer
  rw [← List.append_nil ys]
  apply hr.bind_answer
  exact .done _

/-- At a restarting minor, no subsequent row requests a value. -/
theorem prefixRun_succ_restart {ha : a+1 ≤ m} {rows : Fin a → PivotRow n} {key xs ys}
    (hp : MinorQuery.Run (pivotPrefix D price a (by omega)) xs (.inr (some rows)))
    (hr : MinorQuery.Run (pivotStep (D.submatrix (Fin.castLE ha) id) (fun j => (rows j).pivot) price) ys (.inl key)) :
    MinorQuery.Run (pivotPrefix D price (a+1) ha) (xs++ys) (.inl key) := by
  rw [pivotPrefix]
  exact hp.bind_answer (hr.bind_restart _)

/-- Aborting within a prefix also aborts the complete geometric query at precisely that key. -/
theorem prefixRun_restart_extend {b : ℕ} (hab : a ≤ b) (hb : b ≤ m) {xs key}
    (h : MinorQuery.Run (pivotPrefix D price a (hab.trans hb)) xs (.inl key)) :
    MinorQuery.Run (pivotPrefix D price b hb) xs (.inl key) := by
  induction hab with
  | refl => exact h
  | @step b hle ih =>
    rw [pivotPrefix]
    exact (ih (Nat.le_trans (Nat.le_succ b) hb) h).bind_restart _

end Geometry
end LinearProgramming
end Optimization
end OAI
