import OAI.Optimization.LinearProgramming.PriceGame.Computation
import Mathlib.Data.Fin.Tuple.Basic

/-! Running an adaptive sequence of finite computations, retaining the transcript of returned values. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

universe u

variable {N : ℕ} {α : Type u}

/-- Values produced strictly before step `j` of the schedule. -/
def «prefix» {n : ℕ} (xs : Fin n → α) (j : Fin n) (i : Fin j.val) : α :=
  xs ⟨i.val, i.isLt.trans j.isLt⟩

@[simp] theorem prefix_snoc_castSucc {n : ℕ} (xs : Fin n → α) (x : α) (j : Fin n) :
    «prefix» (Fin.snoc xs x : Fin (n + 1) → α) j.castSucc = «prefix» xs j := by
  funext i
  exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => α) x xs (⟨i.val, i.isLt.trans j.isLt⟩ : Fin n)

@[simp] theorem prefix_snoc_last {n : ℕ} (xs : Fin n → α) (x : α) :
    «prefix» (Fin.snoc xs x : Fin (n + 1) → α) (Fin.last n) = xs := by
  funext i
  exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => α) x xs i

/-- Each element carries the guarantee of its own computation on the prefix it saw. -/
abbrev Schedule (P : (j : ℕ) → (Fin j → α) → α → Prop) (n : ℕ) :=
  {xs : Fin n → α // ∀ j : Fin n, P j («prefix» xs j) (xs j)}

def snocSchedule (P : (j : ℕ) → (Fin j → α) → α → Prop) {n : ℕ}
    (xs : Schedule P n) (x : {y // P n xs.val y}) : Schedule P (n + 1) :=
  ⟨Fin.snoc xs.val x.val, fun j => by
    cases j using Fin.lastCases with
    | cast i => simpa using xs.property i
    | last => simpa using x.property⟩

/-- At each step run the given computation on the entire prefix of previous results.
The descending structural recursion builds the prefix, followed by the next effect. -/
def runSchedule (P : (j : ℕ) → (Fin j → α) → α → Prop)
    (step : ∀ j xs, Computation N {y // P j xs y}) :
    (n : ℕ) → Computation N (Schedule P n)
  | 0 => .pure ⟨Fin.elim0, fun j => j.elim0⟩
  | n + 1 => (runSchedule P step n).bind fun xs =>
      (step n xs.val).map (snocSchedule P xs)

theorem runSchedule_height_le (P : (j : ℕ) → (Fin j → α) → α → Prop)
    (step : ∀ j xs, Computation N {y // P j xs y}) (n K : ℕ)
    (hstep : ∀ j < n, ∀ xs, (step j xs).height ≤ K) :
    (runSchedule P step n).height ≤ n * K := by
  induction n with
  | zero => simp [runSchedule, Computation.height]
  | succ n ih =>
    rw [runSchedule]
    calc
      _ ≤ (runSchedule P step n).height + K := Computation.height_bind_le _ _ K fun xs => by
        rw [Computation.height_map]
        exact hstep n (Nat.lt_succ_self n) xs.val
      _ ≤ n * K + K := Nat.add_le_add_right (ih fun j hj => hstep j (Nat.lt_succ_of_lt hj)) K
      _ = (n + 1) * K := (Nat.succ_mul n K).symm

private theorem reaches_step_congr {R : ℕ} {anchor : Fin N} (hidden : Hidden N R anchor)
    (P : (j : ℕ) → (Fin j → α) → α → Prop)
    (step : ∀ j xs, Computation N {y // P j xs y}) {j : ℕ} {xs ys : Fin j → α}
    {x y : α} {hx : P j xs x} {hy : P j ys y} (h1 : xs = ys) (h2 : x = y)
    (hr : Computation.Reaches hidden (step j xs) ⟨x, hx⟩) :
    Computation.Reaches hidden (step j ys) ⟨y, hy⟩ := by
  subst ys
  subst y
  exact hr

/-- A transcript is reachable precisely when every call can return its recorded value
on the prefix actually supplied to that call. Unforced oracle replies may vary by occurrence. -/
theorem runSchedule_reaches_iff {R : ℕ} {anchor : Fin N} (hidden : Hidden N R anchor)
    (P : (j : ℕ) → (Fin j → α) → α → Prop)
    (step : ∀ j xs, Computation N {y // P j xs y}) :
    ∀ (n : ℕ) (xs : Schedule P n), Computation.Reaches hidden (runSchedule P step n) xs ↔
      ∀ j : Fin n, Computation.Reaches hidden (step j («prefix» xs.val j))
        ⟨xs.val j, xs.property j⟩ := by
  intro n
  induction n with
  | zero =>
    intro xs
    constructor
    · intro _ j; exact j.elim0
    · intro _
      apply (Computation.reaches_pure_iff hidden _ _).mpr
      apply Subtype.ext
      funext j
      exact j.elim0
  | succ n ih =>
    intro xs
    rw [runSchedule, Computation.reaches_bind_iff]
    constructor
    · rintro ⟨ys, hy, hz⟩
      obtain ⟨x, hx, rfl⟩ := (Computation.reaches_map_iff hidden _ _ _).mp hz
      intro j
      cases j using Fin.lastCases with
      | cast j =>
        exact reaches_step_congr hidden P step (prefix_snoc_castSucc ys.val x.val j).symm
          (Fin.snoc_castSucc (α := fun _ : Fin (n+1) => α) x.val ys.val j).symm ((ih ys).mp hy j)
      | last =>
        exact reaches_step_congr hidden P step (prefix_snoc_last ys.val x.val).symm
          (Fin.snoc_last (α := fun _ : Fin (n+1) => α) x.val ys.val).symm hx
    · intro h
      let ys : Schedule P n := ⟨fun j => xs.val j.castSucc, fun j => xs.property j.castSucc⟩
      let x : {y // P n ys.val y} := ⟨xs.val (Fin.last n), xs.property (Fin.last n)⟩
      refine ⟨ys, (ih ys).mpr (fun j => h j.castSucc), ?_⟩
      apply (Computation.reaches_map_iff hidden _ _ _).mpr
      refine ⟨x, h (Fin.last n), ?_⟩
      apply Subtype.ext
      funext j
      cases j using Fin.lastCases with
      | cast j => simp [snocSchedule, ys]
      | last => simp [snocSchedule, x]

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
