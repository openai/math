import OAI.Optimization.LinearProgramming.Lattice.OracleRows

/-! A costed sign-query program for normalizing a rational matrix image. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

universe u v

/-- A decision tree gains information about the hidden real vector only through integer-form
sign queries. The result type may contain explicitly computed rational data. -/
inductive SignQueries (p : ℕ) (α : Type u) : Type u
  | done (value : α)
  | ask (row : Fin p → ℤ) (next : Bool → SignQueries p α)

namespace SignQueries

/-- Interpret the tree with the provided sign oracle. -/
def run {p : ℕ} {α : Type u} (oracle : (Fin p → ℤ) → Bool) : SignQueries p α → α
  | .done x => x
  | .ask a next => run oracle (next (oracle a))

/-- The number of sign queries actually made along this oracle's execution. -/
def cost {p : ℕ} {α : Type u} (oracle : (Fin p → ℤ) → Bool) : SignQueries p α → ℕ
  | .done _ => 0
  | .ask a next => cost oracle (next (oracle a)) + 1

/-- Sequential composition of query programs. -/
def bind {p : ℕ} {α : Type u} {β : Type v} (t : SignQueries p α) (next : α → SignQueries p β) :
    SignQueries p β :=
  match t with
  | .done x => next x
  | .ask a child => .ask a fun b ↦ (child b).bind next

@[simp] theorem run_bind {p : ℕ} {α : Type u} {β : Type v} (oracle : (Fin p → ℤ) → Bool)
    (t : SignQueries p α) (next : α → SignQueries p β) :
    run oracle (t.bind next) = run oracle (next (run oracle t)) := by
  induction t with
  | done x => rfl
  | ask a child ih => exact ih (oracle a)

@[simp] theorem cost_bind {p : ℕ} {α : Type u} {β : Type v} (oracle : (Fin p → ℤ) → Bool)
    (t : SignQueries p α) (next : α → SignQueries p β) :
    cost oracle (t.bind next) = cost oracle t + cost oracle (next (run oracle t)) := by
  induction t with
  | done x => simp [bind, cost, run]
  | ask a child ih => simp [bind, cost, run, ih]; omega

/-- Run each member of the finite family once in index order. -/
def sequence {p : ℕ} {α : Type u} : (n : ℕ) → (Fin n → SignQueries p α) → SignQueries p (Fin n → α)
  | 0, _ => .done Fin.elim0
  | n + 1, f => (f 0).bind fun head ↦ (sequence n fun i ↦ f i.succ).bind fun tail ↦ .done (Fin.cons head tail)

@[simp] theorem run_sequence {p n : ℕ} {α : Type u} (oracle : (Fin p → ℤ) → Bool)
    (f : Fin n → SignQueries p α) : run oracle (sequence n f) = fun i ↦ run oracle (f i) := by
  induction n with
  | zero => exact funext fun i ↦ i.elim0
  | succ n ih =>
    simp only [sequence, run_bind, run, ih]
    exact funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i

@[simp] theorem cost_sequence {p n : ℕ} {α : Type u} (oracle : (Fin p → ℤ) → Bool)
    (f : Fin n → SignQueries p α) : cost oracle (sequence n f) = ∑ i, cost oracle (f i) := by
  induction n with
  | zero => simp [sequence, cost]
  | succ n ih => simp [sequence, ih, cost, Fin.sum_univ_succ]

end SignQueries

/-- Greatest absolute coordinate by integer sign queries, oriented to be nonnegative. -/
def maxRowQ {p : ℕ} : List (Fin p → ℤ) → SignQueries p (Fin p → ℤ)
  | [] => .done 0
  | a :: rows => (maxRowQ rows).bind fun prev ↦ .ask a fun nonnegative ↦
    let oriented := if nonnegative then a else -a
    .ask (oriented - prev) fun larger ↦ .done (if larger then oriented else prev)

@[simp] theorem maxRowQ_run {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (rows : List (Fin p → ℤ)) :
    SignQueries.run oracle (maxRowQ rows) = (maxAbsRow oracle rows).row := by
  induction rows with
  | nil => rfl
  | cons a rows ih => simp [maxRowQ, SignQueries.run, maxAbsRow, ih]

@[simp] theorem maxRowQ_cost {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (rows : List (Fin p → ℤ)) :
    SignQueries.cost oracle (maxRowQ rows) = 2 * rows.length := by
  induction rows with
  | nil => rfl
  | cons a rows ih => simp [maxRowQ, SignQueries.cost, ih]; omega

/-- Bisection on a ratio of integer forms with a positive denominator. -/
def dyadicSearchQ {p : ℕ} (a b : Fin p → ℤ) : ℕ → SignQueries p ℤ
  | 0 => .done 0
  | k + 1 => (dyadicSearchQ a b k).bind fun prev ↦ .ask (dyadicQuery a b k prev) fun nonnegative ↦
    .done (2 * prev + if nonnegative then 1 else -1)

@[simp] theorem dyadicSearchQ_run {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ) (k : ℕ) :
    SignQueries.run oracle (dyadicSearchQ a b k) = (dyadicSearch oracle a b k).numerator := by
  induction k with
  | zero => rfl
  | succ k ih => simp [dyadicSearchQ, SignQueries.run, dyadicSearch, ih]

@[simp] theorem dyadicSearchQ_cost {p : ℕ} (oracle : (Fin p → ℤ) → Bool) (a b : Fin p → ℤ) (k : ℕ) :
    SignQueries.cost oracle (dyadicSearchQ a b k) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [dyadicSearchQ, SignQueries.cost, ih]

/-- Return `none` exactly on zero matrix images. Otherwise produce a dyadic rational vector. -/
def probeRowsQ {n p : ℕ} (P : Fin n → Fin p → ℚ) (k : ℕ) : SignQueries p (Option (Fin n → ℚ)) :=
  let rows := integralRows P
  (maxRowQ (List.ofFn rows)).bind fun d ↦ .ask (-d) fun zero ↦
    if zero then .done none else
      (SignQueries.sequence n fun i ↦ (dyadicSearchQ (rows i) d k).bind fun j ↦
        .done ((j : ℚ) / (2 : ℚ) ^ k)).bind fun ys ↦ .done (some ys)

theorem probeRowsQ_run {n p : ℕ} (oracle : (Fin p → ℤ) → Bool) (P : Fin n → Fin p → ℚ) (k : ℕ) :
    SignQueries.run oracle (probeRowsQ P k) =
      if oracle (-(maxAbsRow oracle (List.ofFn (integralRows P))).row) then none else
        some (normalizedRowApprox oracle P k) := by
  simp only [probeRowsQ, SignQueries.run_bind, maxRowQ_run, SignQueries.run]
  split <;> rename_i h
  · rfl
  · simp [SignQueries.run, normalizedRowApprox, h]

/-- A full `n`-row call has at most `2n+1+nk` queries, independently of the oracle's accuracy. -/
theorem probeRowsQ_cost {n p : ℕ} (oracle : (Fin p → ℤ) → Bool) (P : Fin n → Fin p → ℚ) (k : ℕ) :
    SignQueries.cost oracle (probeRowsQ P k) ≤ 2 * n + 1 + n * k := by
  simp only [probeRowsQ, SignQueries.cost_bind, maxRowQ_cost, List.length_ofFn,
    maxRowQ_run, SignQueries.cost]
  split <;> simp [SignQueries.cost]
  omega

theorem probeRowsQ_none_iff {n p : ℕ} (oracle : (Fin p → ℤ) → Bool) (v : Fin p → ℝ)
    (hOracle : ∀ c, oracle c = true ↔ 0 ≤ formValue c v) (P : Fin n → Fin p → ℚ) (k : ℕ) :
    SignQueries.run oracle (probeRowsQ P k) = none ↔ ∀ i, (∑ j, (P i j : ℝ) * v j) = 0 := by
  let rows := integralRows P
  let d := (maxAbsRow oracle (List.ofFn rows)).row
  have hzero : SignQueries.run oracle (probeRowsQ P k) = none ↔ oracle (-d) = true := by
    rw [probeRowsQ_run]; change (if oracle (-d) then _ else _) = _ ↔ _
    cases oracle (-d) <;> simp
  rw [hzero, hOracle]
  have hn : formValue (-d) v = -‖fun i ↦ formValue (rows i) v‖ := by
    rw [← maxAbsRow_value oracle v hOracle rows]; simp [d, formValue, Finset.sum_neg_distrib]
  rw [hn, neg_nonneg, norm_le_zero_iff]
  have hD : (matrixDenominator P : ℝ) ≠ 0 := by exact_mod_cast (matrixDenominator_pos P).ne'
  simp [funext_iff, rows, integralRows_value, hD]

theorem probeRowsQ_some {n p : ℕ} (oracle : (Fin p → ℤ) → Bool) (P : Fin n → Fin p → ℚ) (k : ℕ)
    {ys : Fin n → ℚ} (h : SignQueries.run oracle (probeRowsQ P k) = some ys) :
    ys = normalizedRowApprox oracle P k := by
  rw [probeRowsQ_run] at h
  split at h <;> simp_all

end Lattice
end LinearProgramming
end Optimization
end OAI
