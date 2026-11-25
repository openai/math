import OAI.Computability.BorderVNP.CubeMeanFactors
import OAI.Computability.BorderVNP.CubeMeanLoads

/-! # Incident-row arithmetic for the public cube-label scan

Each record carries the original integer width. The public cache contains the conditional bin
means scaled by the square of the alphabet size. Recomputing an incident subtotal before and
after one pin gives an exact update using natural subtraction without underflow.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.MeanChoice

open Balancing Finset
open scoped BigOperators

/-- One publicly oriented cable or one delivered block of data. -/
inductive Traffic (C : Type*) where
  | cable (src dst : C) (width : ℕ)
  | delivery (recv : C) (width : ℕ)
  deriving DecidableEq

variable {C I : Type*} [DecidableEq C] {z : ℕ}

/-- Number of unit bits in a public record. -/
def Traffic.width : Traffic C → ℕ
  | .cable _ _ w | .delivery _ w => w

/-- Exactly the records whose conditioned contribution can change at this pin. -/
def touches (c : C) : Traffic C → Prop
  | .cable a b _ => a = c ∨ b = c
  | .delivery a _ => a = c

instance (c : C) (r : Traffic C) : Decidable (touches c r) := by
  cases r <;> unfold touches <;> infer_instance

/-- Width times the common-denominator numerator of this row's conditioned bin hit. -/
def rowNat (s : Finset C) (x : C → Fin (z+1)) : Bins z → Traffic C → ℕ
  | .inl (u,v), .cable a b w => w*factor s x a u*factor s x b v
  | .inr u, .delivery a w => w*(z+1)*factor s x a u
  | _, _ => 0

/-- Each nonnegative bin contribution is at most the width times the common denominator. -/
theorem rowNat_le (s : Finset C) (x : C → Fin (z+1)) (j : Bins z) (r : Traffic C) :
    rowNat s x j r ≤ r.width*(z+1)^2 := by
  rcases j with ⟨u,v⟩ | u
  · cases r with
    | cable a b w =>
      simpa only [rowNat,Traffic.width,pow_two,Nat.mul_assoc] using
        Nat.mul_le_mul (Nat.mul_le_mul_left w (factor_le s x a u)) (factor_le s x b v)
    | delivery a w => exact Nat.zero_le _
  · cases r with
    | cable a b w => exact Nat.zero_le _
    | delivery a w =>
      simpa only [rowNat,Traffic.width,pow_two,Nat.mul_assoc] using
        Nat.mul_le_mul_left (w*(z+1)) (factor_le s x a u)

/-- Only incident rows change, even if some other endpoint had been fixed earlier. -/
theorem rowNat_unaffected (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1))
    (j : Bins z) (r : Traffic C) (hn : ¬touches c r) :
    rowNat (insert c s) (Function.update x c v) j r = rowNat s x j r := by
  cases r with
  | cable a b w =>
    change ¬(a = c ∨ b = c) at hn
    rcases j with ⟨u,t⟩|u
    · simp only [rowNat,factor_unaffected s x c a v u (fun h => hn (.inl h)),
        factor_unaffected s x c b v t (fun h => hn (.inr h))]
    · rfl
  | delivery a w =>
    rcases j with j|u
    · rcases j with ⟨u,t⟩; rfl
    · simp only [rowNat,factor_unaffected s x c a v u hn]

variable [Fintype I]

/-- The common scaled mean of a bin, summed over all descriptors. -/
def cache (rows : I → Traffic C) (s : Finset C) (x : C → Fin (z+1)) (j : Bins z) : ℕ :=
  ∑ i, rowNat s x j (rows i)

/-- The subtotal obtained from the publicly indexed incident rows. -/
def incidentSum (rows : I → Traffic C) (c : C) (s : Finset C) (x : C → Fin (z+1)) (j : Bins z) : ℕ :=
  ∑ i ∈ univ.filter (fun i => touches c (rows i)), rowNat s x j (rows i)

private def restSum (rows : I → Traffic C) (c : C) (s : Finset C) (x : C → Fin (z+1)) (j : Bins z) : ℕ :=
  ∑ i ∈ univ.filter (fun i => ¬touches c (rows i)), rowNat s x j (rows i)

private theorem splitSum (rows : I → Traffic C) (c : C) (s : Finset C) (x : C → Fin (z+1)) (j : Bins z) :
    incidentSum rows c s x j + restSum rows c s x j = cache rows s x j :=
  Finset.sum_filter_add_sum_filter_not _ _ _

private theorem restSum_unaffected (rows : I → Traffic C) (c : C) (s : Finset C) (x : C → Fin (z+1))
    (v : Fin (z+1)) (j : Bins z) :
    restSum rows c (insert c s) (Function.update x c v) j = restSum rows c s x j :=
  sum_congr rfl fun _ hi => rowNat_unaffected _ _ _ _ _ _ (mem_filter.mp hi).2

/-- A commit updates an existing cache by replacing only the incident subtotal. -/
def commit (rows : I → Traffic C) (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1))
    (old : Bins z → ℕ) (j : Bins z) : ℕ :=
  old j - incidentSum rows c s x j + incidentSum rows c (insert c s) (Function.update x c v) j

/-- Committing a pin returns its exact new cache. -/
theorem commit_cache (rows : I → Traffic C) (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1)) :
    commit rows s x c v (cache rows s x) = cache rows (insert c s) (Function.update x c v) := by
  funext j
  have h := splitSum rows c s x j
  have k := splitSum rows c (insert c s) (Function.update x c v) j
  rw [restSum_unaffected] at k
  unfold commit
  omega

/-- The incident-row candidate score, computed with an already materialized mean array. -/
def candidate (rows : I → Traffic C) (s : Finset C) (x : C → Fin (z+1)) (c : C)
    (old : Bins z → ℕ) (v : Fin (z+1)) : ℕ :=
  ∑ j, old j*incidentSum rows c (insert c s) (Function.update x c v) j

/-- The incident-row score on the exact old means. -/
def scoreNat (rows : I → Traffic C) (s : Finset C) (x : C → Fin (z+1)) (c : C) :=
  candidate rows s x c (cache rows s x)

/-- The omitted part of the full dot product is a single constant for every trial label. -/
theorem exists_offset (rows : I → Traffic C) (s : Finset C) (x : C → Fin (z+1)) (c : C) :
    ∃ off : ℕ, ∀ v, scoreNat rows s x c v + off =
      ∑ j, cache rows s x j * cache rows (insert c s) (Function.update x c v) j := by
  refine ⟨∑ j, cache rows s x j * restSum rows c s x j, fun v => ?_⟩
  unfold scoreNat candidate
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  have h := splitSum rows c (insert c s) (Function.update x c v) j
  rw [restSum_unaffected] at h
  rw [← Nat.mul_add,h]

/-- Sum of all delivered and cable widths. -/
def totalWidth (rows : I → Traffic C) := ∑ i, (rows i).width

/-- All maintained bin registers fit this uniform cap, including every trial cache. -/
theorem cache_le (rows : I → Traffic C) (s : Finset C) (x : C → Fin (z+1)) (j : Bins z) :
    cache rows s x j ≤ totalWidth rows*(z+1)^2 := by
  unfold cache totalWidth
  rw [Finset.sum_mul]
  exact sum_le_sum fun i _ => rowNat_le _ _ _ _

/-- The nonnegative candidate fits the stated public word budget. -/
theorem scoreNat_le (rows : I → Traffic C) (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1)) :
    scoreNat rows s x c v ≤ 2*(z+1)^6*(totalWidth rows)^2 := by
  let sj := insert c s
  let y := Function.update x c v
  have cap (j : Bins z) : incidentSum rows c sj y j ≤ cache rows sj y j := by
    have eq := splitSum rows c sj y j
    omega
  change (∑ j, cache rows s x j * incidentSum rows c sj y j) ≤ _
  calc (∑ j, cache rows s x j * incidentSum rows c sj y j) ≤ ∑ _j : Bins z, (totalWidth rows*(z+1)^2)^2 :=
         sum_le_sum fun j _ => (Nat.mul_le_mul (cache_le rows s x j) ((cap j).trans (cache_le rows sj y j))).trans_eq
           (pow_two _).symm
       _ = ((z+1)^2+(z+1))*(totalWidth rows*(z+1)^2)^2 := by simp [Bins,pow_two]
       _ ≤ (2*(z+1)^2)*(totalWidth rows*(z+1)^2)^2 := by
         gcongr; nlinarith
       _ = _ := by ring

end Cube.MeanChoice

end BorderVNP
end Computability
end OAI
