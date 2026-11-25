import OAI.Computability.NearSquareRoot.SynchronizedPrimitive
import Mathlib.Tactic

/-! # Bounded primitive-layer words for a short transform -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedPair
open scoped Matrix

variable {A : Type} [DecidableEq A]

theorem ShortLayer.adjoint {M : Matrix A A ℂ} (h : ShortLayer M) : ShortLayer Mᴴ := by
  cases h with
  | permutation e =>
    suffices h : (fun i j => if i = e j then (1 : ℂ) else 0 : Matrix A A ℂ)ᴴ =
        (fun i j => if i = e.symm j then 1 else 0) by rw [h]; apply ShortLayer.permutation
    ext i j
    change star (if j = e i then (1 : ℂ) else 0) = _
    simp only [Equiv.eq_symm_apply]
    split_ifs <;> simp_all [eq_comm]
  | phase d hd =>
    rw [Matrix.diagonal_conjTranspose]
    exact .phase _ (fun i => by simpa using hd i)
  | pairs e f hf hfa =>
    rw [Matrix.conjTranspose_submatrix, Matrix.blockDiagonal_conjTranspose]
    exact .pairs e _ hfa (fun i => by simpa using hf i)

variable [Fintype A]

/-- The bound is on the actual length of a matrix factorization. -/
def HasShortWord (M : Matrix A A ℂ) (n : ℕ) : Prop :=
  ∃ w : List (Matrix A A ℂ), w.prod = M ∧ (∀ x ∈ w, ShortLayer x) ∧ w.length ≤ n

namespace HasShortWord

theorem singleton {M : Matrix A A ℂ} (h : ShortLayer M) : HasShortWord M 1 :=
  ⟨[M], by simp, by simpa using h, by simp⟩

theorem empty : HasShortWord (1 : Matrix A A ℂ) 0 :=
  ⟨[], rfl, by simp, by simp⟩

theorem mono {M : Matrix A A ℂ} {m n : ℕ} (h : HasShortWord M m) (hmn : m ≤ n) :
    HasShortWord M n := by
  obtain ⟨w, hw, hp, hn⟩ := h
  exact ⟨w, hw, hp, hn.trans hmn⟩

theorem append {M N : Matrix A A ℂ} {m n : ℕ} (h : HasShortWord M m) (g : HasShortWord N n) :
    HasShortWord (M * N) (m + n) := by
  obtain ⟨u, hu, hpu, hnu⟩ := h
  obtain ⟨v, hv, hpv, hnv⟩ := g
  refine ⟨u ++ v, by simp [hu, hv], fun x hx => ?_, by simpa using Nat.add_le_add hnu hnv⟩
  exact (List.mem_append.mp hx).elim (hpu x) (hpv x)

theorem power {M : Matrix A A ℂ} {n : ℕ} (h : HasShortWord M n) (j : ℕ) :
    HasShortWord (M^j) (j*n) := by
  induction j with
  | zero => simpa using (empty (A := A))
  | succ j ih => simpa [pow_succ, Nat.succ_mul] using ih.append h

private theorem adjoint_prod (w : List (Matrix A A ℂ)) :
    (w.reverse.map Matrix.conjTranspose).prod = w.prodᴴ := by
  induction w with
  | nil => simp
  | cons x w ih => simp only [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, Matrix.conjTranspose_mul, ih]

theorem adjoint {M : Matrix A A ℂ} {n : ℕ} (h : HasShortWord M n) :
    HasShortWord Mᴴ n := by
  obtain ⟨w, rfl, hp, hn⟩ := h
  refine ⟨w.reverse.map Matrix.conjTranspose, adjoint_prod _, ?_, by simpa using hn⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact (hp y (by simpa using hy)).adjoint

end HasShortWord
end ShortFourier

end NearSquareRoot
end Computability
end OAI
