import OAI.Computability.BorderVNP.ShortenEpochDirections
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# The finite group permuting direction bins

A signed coordinate permutation chooses an underlying permutation of factor
addresses and a sign in each factor. These transformations form a finite
group of continuous isometries on the product tangent space, containing
the specific operators `A_j` of the paper.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open scoped Classical

variable {I : Type*} [Fintype I]

private def signed (b : Bool) (z : ℂ) : ℂ := if b then -z else z

private theorem signed_xor (b c : Bool) (z : ℂ) :
    signed b (signed c z) = signed (b ^^ c) z := by cases b <;> cases c <;> simp [signed]

private theorem signed_twice (b : Bool) (z : ℂ) : signed b (signed b z) = z := by
  cases b <;> simp [signed]

/-- Apply a signed permutation to all tangent components. -/
def factorPerm (e : Equiv.Perm I) (s : I → Bool) : Equiv.Perm (PiLp 2 fun _ : I => ℂ) where
  toFun v := WithLp.toLp 2 fun i => signed (s i) (v (e i))
  invFun v := WithLp.toLp 2 fun i => signed (s (e.symm i)) (v (e.symm i))
  left_inv v := by ext1 i; change signed _ (signed _ _) = _; simp [signed_twice]
  right_inv v := by ext1 i; change signed _ (signed _ _) = _; simp [signed_twice]

/-- Permuting factors and negating selected components preserves the product distance. -/
theorem factorPerm_isometry (e : Equiv.Perm I) (s : I → Bool) :
    Isometry (factorPerm e s) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [PiLp.dist_eq_of_L2, PiLp.dist_eq_of_L2]
  congr 1
  trans ∑ i, dist (x (e i)) (y (e i)) ^ 2
  · apply Finset.sum_congr rfl
    intro i _
    change dist (signed (s i) _) (signed (s i) _) ^ 2 = _
    cases hs : s i <;> simp [signed]
  · exact Equiv.sum_comp e (fun i => dist (x i) (y i)^2)

/-- The subgroup of all signed factor permutations acting on actual tangent
vectors. Identical permutations of the tangent space are identified. -/
def signedFactorGroup (I : Type*) : Subgroup (Equiv.Perm (PiLp 2 fun _ : I => ℂ)) where
  carrier := {f | ∃ e : Equiv.Perm I, ∃ s : I → Bool, f = factorPerm e s}
  one_mem' := ⟨Equiv.refl I, fun _ => false, by ext v i; rfl⟩
  mul_mem' := by
    rintro _ _ ⟨e,s,rfl⟩ ⟨f,t,rfl⟩
    refine ⟨e.trans f, fun i => s i ^^ t (e i), ?_⟩
    ext v i
    exact congrArg (fun z : ℂ => z) (signed_xor (s i) (t (e i)) (v (f (e i))))
  inv_mem' := by
    rintro _ ⟨e,s,rfl⟩
    exact ⟨e.symm, fun i => s (e.symm i), Equiv.ext (fun _ => rfl)⟩

/-- The factor group is a finite image of the permutations and Boolean sign lists. -/
instance : Finite (signedFactorGroup I) := by
  let make (es : Equiv.Perm I × (I → Bool)) : signedFactorGroup I :=
    ⟨factorPerm es.1 es.2, ⟨es.1, es.2, rfl⟩⟩
  apply Finite.of_surjective make
  intro g
  obtain ⟨e,s,hs⟩ := g.property
  exact ⟨(e,s), Subtype.ext hs.symm⟩

/-- Every element of the finite factor group acts isometrically. -/
theorem signedFactorGroup_isometry (g : signedFactorGroup I) :
    Isometry (fun x : PiLp 2 (fun _ : I => ℂ) => g • x) := by
  obtain ⟨e,s,hs⟩ := g.property
  change Isometry g.val
  rw [hs]
  exact factorPerm_isometry _ _

instance : ContinuousConstSMul (signedFactorGroup I) (PiLp 2 fun _ : I => ℂ) :=
  ⟨fun g => (signedFactorGroup_isometry g).continuous⟩

/-- Each orthogonalizing operator `A_j` is an element of this finite group. -/
theorem exists_signedFactor_smul {D : ℕ} (j : Fin D) :
    ∃ g : signedFactorGroup (Cube D), ∀ x : Direction D ℂ, g • x = signedFlip j x := by
  classical
  let flipj : Equiv.Perm (Cube D) := {
    toFun := flip j
    invFun := flip j
    left_inv := fun x => by ext k; by_cases h : k = j <;> simp [flip, h]
    right_inv := fun x => by ext k; by_cases h : k = j <;> simp [flip, h] }
  let sign (i : Cube D) := decide (prefixSign j i = -1)
  refine ⟨⟨factorPerm flipj sign, ⟨flipj, sign, rfl⟩⟩, ?_⟩
  intro x
  ext1 i
  change signed (sign i) (x (flip j i)) = prefixSign j i • x (flip j i)
  have hsq : (prefixSign j i)^2 = 1 := by
    simpa only [pow_two] using prefixSign_sq j i
  have hor : prefixSign j i = -1 ∨ prefixSign j i = 1 := by
    have hz : (prefixSign j i - 1) * (prefixSign j i + 1) = 0 := by nlinarith only [hsq]
    rcases mul_eq_zero.mp hz with h | h <;> [right; left] <;> linarith
  rcases hor with h | h <;> norm_num [sign, h, signed]

end Epoch

end BorderVNP
end Computability
end OAI
