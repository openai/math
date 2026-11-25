import OAI.Optimization.LinearProgramming.PriceGame.Experts
import Mathlib.Tactic
import Mathlib.Data.List.FinRange

/-! Deterministic enumeration of all paper skeletons. It uses only public dimensions. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

open States.Mass

namespace Skeleton

def vertices (N : ℕ) : (k : ℕ) → List (Vertex N k)
  | 0 => List.finRange N
  | k + 1 => (vertices N k).flatMap fun i => [(i, false), (i, true)]

@[simp] theorem mem_vertices (N k : ℕ) (i : Vertex N k) : i ∈ vertices N k := by
  induction k with
  | zero => exact List.mem_finRange i
  | succ k ih =>
    obtain ⟨j, b⟩ := i
    apply List.mem_flatMap.mpr
    refine ⟨j, ih j, ?_⟩
    change (j, b) ∈ ([(j, false), (j, true)] : List (Vertex N k × Bool))
    cases b <;> simp

private theorem length_flatMap_const {α β : Type*} (xs : List α) (f : α → List β)
    {n : ℕ} (h : ∀ a ∈ xs, (f a).length = n) :
    (xs.flatMap f).length = xs.length * n := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.flatMap_cons, List.length_append, h a (by simp), ih (fun a ha => h a (by simp [ha]))]
    simp [Nat.succ_mul, Nat.add_comm]

private theorem length_flatMap_le {α β : Type*} (xs : List α) (f : α → List β)
    {n : ℕ} (h : ∀ a ∈ xs, (f a).length ≤ n) :
    (xs.flatMap f).length ≤ xs.length * n := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, one_mul]
    have hp := ih (fun b hb => h b (by simp [hb]))
    grind

@[simp] theorem length_vertices (N k : ℕ) : (vertices N k).length = N * 2 ^ k := by
  induction k with
  | zero => simpa only [vertices, pow_zero, Nat.mul_one] using! (List.length_finRange (n := N))
  | succ k ih =>
    change ((vertices N k).flatMap fun i => ([(i, false), (i, true)] : List (Vertex N k × Bool))).length = _
    rw [length_flatMap_const _ _ (n := 2) (by intros; rfl), ih, pow_succ, Nat.mul_assoc]

/-- Ordered tuples with repetitions and fixed arity, enumerated without hidden data. -/
def tuples {α : Type*} (xs : List α) : (k : ℕ) → List (Fin k → α)
  | 0 => [Fin.elim0]
  | k + 1 => xs.flatMap fun a => (tuples xs k).map fun as => Fin.cons a as

theorem mem_tuples {α : Type*} (xs : List α) (k : ℕ) (f : Fin k → α)
    (hf : ∀ i, f i ∈ xs) : f ∈ tuples xs k := by
  induction k with
  | zero =>
    simpa [tuples] using (funext (fun i : Fin 0 => i.elim0) : f = Fin.elim0)
  | succ k ih =>
    apply List.mem_flatMap.mpr
    refine ⟨f 0, hf 0, List.mem_map.mpr ⟨Fin.tail f, ih _ (fun i => hf i.succ), ?_⟩⟩
    exact Fin.cons_self_tail f

@[simp] theorem length_tuples {α : Type*} (xs : List α) (k : ℕ) :
    (tuples xs k).length = xs.length ^ k := by
  induction k with
  | zero => simp [tuples]
  | succ k ih =>
    rw [tuples, length_flatMap_const _ _ (n:=xs.length ^ k) (by simp [ih]), pow_succ, Nat.mul_comm]

def pivots (N k : ℕ) : List (Pivot N k) :=
  none :: (List.finRange k).flatMap fun j : Fin k =>
    (vertices N j).map fun i => some ⟨j, i⟩

@[simp] theorem mem_pivots (N k : ℕ) (p : Pivot N k) : p ∈ pivots N k := by
  cases p with
  | none => simp [pivots]
  | some a =>
    obtain ⟨j, i⟩ := a
    simp only [pivots, List.mem_cons, Option.some_ne_none, false_or, List.mem_flatMap]
    exact ⟨j, List.mem_finRange j, List.mem_map.mpr ⟨i, mem_vertices _ _ _, rfl⟩⟩

theorem length_pivots_le (N k : ℕ) : (pivots N k).length ≤ 1 + k * (N * 2 ^ k) := by
  unfold pivots
  rw [List.length_cons]
  have h := length_flatMap_le (List.finRange k)
    (fun j : Fin k => (vertices N j).map fun i => (some ⟨j, i⟩ : Pivot N k)) (n := N * 2 ^ k) (by
      intro j _
      rw [List.length_map, length_vertices]
      exact Nat.mul_le_mul_left N (Nat.pow_le_pow_right (by decide) j.isLt.le))
  rw [List.length_finRange] at h
  omega

/-- Enumerate skeletons independently of the hidden signs and costs. -/
def enumerate (N : ℕ) : List (Skeleton N) :=
  (List.finRange (depth N)).flatMap fun k : Fin (depth N) =>
    ([false, true] : List Bool).flatMap fun sign =>
      (tuples (vertices N k) 64).flatMap fun tuple =>
        (pivots N k).map fun pivot => ⟨k, sign, tuple, pivot⟩

@[simp] theorem mem_enumerate {N : ℕ} (s : Skeleton N) : s ∈ enumerate N := by
  obtain ⟨k, sign, tuple, pivot⟩ := s
  apply List.mem_flatMap.mpr
  refine ⟨k, List.mem_finRange k, List.mem_flatMap.mpr ⟨sign, ?_, List.mem_flatMap.mpr ⟨tuple, ?_, ?_⟩⟩⟩
  · cases sign <;> simp
  · exact mem_tuples _ _ _ (fun i => mem_vertices _ _ _)
  · exact List.mem_map.mpr ⟨pivot, mem_pivots _ _ _, rfl⟩

/-- The fixed exponent 64 appears in the bound on the number of skeletons, not in a loop
depending on the costs. -/
theorem length_enumerate_le (N : ℕ) (hN : 0 < N) :
    (enumerate N).length ≤ depth N * (2 * ((2*N^2)^64 * (1 + depth N * (2*N^2)))) := by
  let v := 2*N^2
  let D := depth N
  have hv (k : Fin D) : N * 2^k.val ≤ v := by
    have hc := card_vertices_le N k hN k.isLt.le
    simpa [v, card_vertices, Nat.mul_comm (2^k.val) N] using hc
  have hp (k : Fin D) : (pivots N k.val).length ≤ 1 + D*v :=
    (length_pivots_le _ _).trans (Nat.add_le_add_left (Nat.mul_le_mul k.isLt.le (hv k)) 1)
  let perSign (k : Fin D) (s : Bool) : List (Skeleton N) :=
    (tuples (vertices N k) 64).flatMap fun as =>
      (pivots N k).map fun p => ⟨k, s, as, p⟩
  have hsign (k : Fin D) (s : Bool) : (perSign k s).length ≤ v^64 * (1+D*v) := by
    calc
      _ ≤ (tuples (vertices N k) 64).length * (1+D*v) :=
        length_flatMap_le _ _ fun _ _ => by simpa using hp k
      _ ≤ _ := by
        rw [length_tuples, length_vertices]
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (hv k) _)
  have htwo (k : Fin D) : (([false,true] : List Bool).flatMap (perSign k)).length ≤
      2 * (v^64 * (1+D*v)) :=
    length_flatMap_le _ _ (fun sign _ => hsign k sign)
  have hall := length_flatMap_le (List.finRange D)
    (fun k : Fin D => ([false,true] : List Bool).flatMap (perSign k)) (fun k _ => htwo k)
  simpa only [List.length_finRange, enumerate, perSign, D, v] using! hall

end Skeleton
end PriceGame
end LinearProgramming
end Optimization
end OAI
