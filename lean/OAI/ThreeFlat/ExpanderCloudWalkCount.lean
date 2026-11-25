import Mathlib.LinearAlgebra.Matrix.Symmetric

namespace OAI
/-! # Counting walks in regular multigraphs

The entries of powers of the arc matrix count walks. Reversal preserves the
length, and the total number of walks beginning at any vertex is the degree
raised to the length. Both identities extend to weighted sums of lengths.
-/

namespace ThreeFlat

open Finset

variable {V I : Type*} [Fintype V] [DecidableEq V]

theorem nat_walk_rowsum (B : Matrix V V ℕ) (b : ℕ)
    (h : ∀ u, ∑ v, B u v = b) (k : ℕ) (u : V) :
    ∑ v, (B ^ k) u v = b ^ k := by
  induction k with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, pow_succ, ← ih]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => by rw [← Finset.mul_sum, h a]

theorem nat_walk_symm (B : Matrix V V ℕ) (hsym : ∀ u v, B u v = B v u)
    (k : ℕ) (u v : V) : (B ^ k) u v = (B ^ k) v u := by
  have h : B.IsSymm := Matrix.IsSymm.ext fun i j => hsym j i
  exact (h.pow k).apply v u

theorem nat_walk_weighted_rowsum (B : Matrix V V ℕ) (b : ℕ)
    (h : ∀ u, ∑ v, B u v = b) (s : Finset I) (w length : I → ℕ) (u : V) :
    (∑ v, ∑ i ∈ s, w i * (B ^ length i) u v) = ∑ i ∈ s, w i * b ^ length i := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum, nat_walk_rowsum B b h]

theorem nat_walk_weighted_symm (B : Matrix V V ℕ) (hsym : ∀ u v, B u v = B v u)
    (s : Finset I) (w length : I → ℕ) (u v : V) :
    (∑ i ∈ s, w i * (B ^ length i) u v) = ∑ i ∈ s, w i * (B ^ length i) v u :=
  Finset.sum_congr rfl fun i _ => congrArg (w i * ·) (nat_walk_symm B hsym (length i) u v)

end ThreeFlat

end OAI
