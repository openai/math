import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Most-significant-bit transshipment schedules for Appendix B. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment

variable {m : ℕ}

/-- The expert vertices whose next digit contributes one unit, in fixed index order. -/
def oddExperts (qty : Fin m → ℕ) : List (Fin m) :=
  (List.finRange m).filter fun i => qty i % 2 == 1

theorem count_oddExperts (qty : Fin m → ℕ) (i : Fin m) :
    (oddExperts qty).count i = qty i % 2 := by
  have hb := Nat.mod_lt (qty i) (by decide : 0 < 2)
  by_cases h : qty i % 2 = 1
  · simp [oddExperts, h, List.count_filter]
  · have h0 : qty i % 2 = 0 := by omega
    have hn : i ∉ oddExperts qty := by simp [oddExperts, h]
    simp [List.count_eq_zero_of_not_mem hn, h0]

/-- `none` requests a doubling; `some i` augments the supply or demand of expert `i`. -/
def schedule : ℕ → (Fin m → ℕ) → List (Option (Fin m))
  | 0, _ => []
  | k + 1, qty => schedule k (fun i => qty i / 2) ++ none :: (oddExperts qty).map some

/-- Exactly one doubling per binary place. -/
theorem count_doublings (k : ℕ) (qty : Fin m → ℕ) : (schedule k qty).count none = k := by
  induction k generalizing qty with
  | zero => rfl
  | succ k ih => simp [schedule, ih, List.count_eq_zero_of_not_mem]

/-- Bounds the total number of unit path augmentations separately from the doublings. -/
theorem schedule_cost (k : ℕ) (qty : Fin m → ℕ) :
    ((schedule k qty).filterMap id).length ≤ m * k := by
  induction k generalizing qty with
  | zero => simp [schedule]
  | succ k ih =>
    have hn : (oddExperts qty).length ≤ m :=
      (List.length_filter_le _ _).trans_eq List.length_finRange
    simp only [schedule, List.filterMap_append, List.filterMap_cons, id_eq, List.length_append,
      List.filterMap_map, Function.comp_def, List.filterMap_some, Nat.mul_succ]
    exact Nat.add_le_add (ih _) hn

variable {S : Type*}

/-- Interpret an explicit schedule on any state representation. -/
def operation (double : S → S) (unit : S → Fin m → S) (s : S) : Option (Fin m) → S
  | none => double s
  | some i => unit s i

def raiseAt (q : Fin m → ℕ) (i j : Fin m) : ℕ := q j + if j = i then 1 else 0

private theorem fold_units (double : S → S) (unit : S → Fin m → S) (P : S → (Fin m → ℕ) → Prop)
    (hu : ∀ s q, P s q → ∀ i, P (unit s i) (raiseAt q i))
    (s : S) (q : Fin m → ℕ) (hs : P s q) (l : List (Fin m)) :
    P ((l.map some).foldl (operation double unit) s) (fun j => q j + l.count j) := by
  induction l generalizing q s with
  | nil => simpa using hs
  | cons i l ih =>
    have h := ih _ _ (hu s q hs i)
    suffices (fun j => raiseAt q i j + l.count j) = (fun j => q j + (i :: l).count j) by
      simpa [List.foldl_cons, operation, ← this] using h
    funext j
    by_cases hij : i = j <;> simp [raiseAt, hij, Ne.symm,
      Nat.add_left_comm, Nat.add_comm]

/-- Applying the schedule reaches the exact encoded balances. This statement applies in particular
when the state invariant includes integral feasibility and a residual optimality certificate. -/
theorem run_schedule (double : S → S) (unit : S → Fin m → S) (P : S → (Fin m → ℕ) → Prop)
    (initial : S) (h0 : P initial (fun _ => 0))
    (hd : ∀ s q, P s q → P (double s) (fun j => 2 * q j))
    (hu : ∀ s q, P s q → ∀ i, P (unit s i) (raiseAt q i))
    (k : ℕ) (qty : Fin m → ℕ) (hk : ∀ i, qty i < 2 ^ k) :
    P ((schedule k qty).foldl (operation double unit) initial) qty := by
  induction k generalizing qty with
  | zero =>
    have hz : qty = fun _ => 0 := funext fun i => by simpa using hk i
    simpa [schedule, hz] using h0
  | succ k ih =>
    let half (i : Fin m) := qty i / 2
    have hhalf (i : Fin m) : half i < 2 ^ k := by
      have := hk i
      rw [pow_succ] at this
      exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr this
    have h := hd _ _ (ih half hhalf)
    have h' := fold_units double unit P hu _ _ h (oddExperts qty)
    have recover : (fun j => 2 * half j + (oddExperts qty).count j) = qty := by
      funext j
      rw [count_oddExperts]
      dsimp [half]
      omega
    rw [recover] at h'
    exact (by simpa [schedule, List.foldl_append, operation, half] using h')

end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
