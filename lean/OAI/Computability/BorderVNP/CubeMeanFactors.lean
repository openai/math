import OAI.Computability.BorderVNP.CubeMeanChoice

/-! # Integer numerators for conditioned cable and delivery records -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.MeanChoice

open Balancing Finset
open scoped BigOperators

variable {C : Type*} [DecidableEq C] {z : ℕ}

/-- A single endpoint has probability numerator one while free and zero or the full
denominator after its label is pinned. -/
def factor (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1)) : ℕ :=
  if c ∈ s then if x c = v then z+1 else 0 else 1

/-- The endpoint numerator fits the common one-symbol denominator. -/
theorem factor_le (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1)) :
    factor s x c v ≤ z+1 := by unfold factor; split_ifs <;> omega

/-- Fixing an unrelated cell leaves this endpoint's probability unchanged. -/
theorem factor_unaffected (s : Finset C) (x : C → Fin (z+1)) (c k : C) (v t : Fin (z+1)) (hk : k ≠ c) :
    factor (insert c s) (Function.update x c v) k t = factor s x k t := by simp [factor,hk]

private theorem one_sdiff (s : Finset C) (c : C) :
    ({c} \ s : Finset C) = if c ∈ s then ∅ else {c} := by
  ext i; by_cases hc : c ∈ s <;> simp [hc] <;> aesop

variable [Fintype C]

/-- The data numerator represents exactly the conditioned one-endpoint probability. -/
theorem factor_datum (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1)) :
    (factor s x c v : ℝ) = (z+1 : ℝ)*pinnedChance (datum (fun _ : Unit => c) v ()) s x := by
  by_cases hc : c ∈ s <;> by_cases hv : x c = v <;>
    simp [factor,pinnedChance,datum,one_sdiff,hc,hv] <;> field_simp

/-- The two endpoint numerators represent the conditioned joint cable probability
even when the two requested labels coincide. Only the cable's cells must be distinct. -/
theorem factor_cable (s : Finset C) (x : C → Fin (z+1)) (a b : C) (u v : Fin (z+1)) (hne : a ≠ b) :
    (factor s x a u * factor s x b v : ℕ) = (z+1 : ℝ)^2*
      pinnedChance (cable (fun _ : Unit => a) (fun _ => b) u v ()) s x := by
  have dis : Disjoint (datum (fun _ : Unit => a) u ()).sites (datum (fun _ : Unit => b) v ()).sites := by
    simp [datum,hne]
  have together := pinned_independent (datum (fun _ : Unit => a) u ()) (datum (fun _ : Unit => b) v ()) s x dis
  have hit_product (y : C → Fin (z+1)) :
      hit (datum (fun _ : Unit => a) u ()) y * hit (datum (fun _ : Unit => b) v ()) y =
      hit (cable (fun _ : Unit => a) (fun _ => b) u v ()) y := by
    by_cases hu : y a = u <;> by_cases hv : y b = v <;> simp [hit,datum,cable,hne.symm,hu,hv]
  have combined : jointChance (datum (fun _ : Unit => a) u ()) (datum (fun _ : Unit => b) v ()) s x =
      pinnedChance (cable (fun _ : Unit => a) (fun _ => b) u v ()) s x := by
    rw [← expect_pinned_product,← expect_pinned_hit]; simp_rw [hit_product]
  rw [Nat.cast_mul,factor_datum s x a u,factor_datum s x b v,← combined,together]
  ring

end Cube.MeanChoice

end BorderVNP
end Computability
end OAI
