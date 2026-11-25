import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Pi

/-! Rigidity of the integer relation used to broadcast a shared label. -/
namespace OAI
namespace Combinatorics
namespace Sunflower

open Finset

private theorem sphere_rigidity_int {D Z : Type*} [Fintype D] [Fintype Z]
    (u : D → ℤ) (w : Z → D → ℤ)
    (hn : ∀ z, ∑ i, (w z i)^2 = ∑ i, (u i)^2)
    (hd : ∑ z, ∑ i, u i * w z i = Fintype.card Z * ∑ i, (u i)^2) :
    ∀ z, w z = u := by
  classical
  have hdist (z : Z) :
      ∑ i, (w z i - u i)^2 = 2 * ((∑ i, (u i)^2) - ∑ i, u i * w z i) := by
    calc
      _ = ∑ i, ((w z i)^2 + (u i)^2 - 2 * (u i * w z i)) :=
        sum_congr rfl fun i _ => by ring
      _ = _ := by rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, hn]; ring
  have hz : ∑ z, ∑ i, (w z i - u i)^2 = 0 := by
    simp_rw [hdist]
    rw [← mul_sum, sum_sub_distrib, hd, sum_const, card_univ, nsmul_eq_mul]
    ring
  intro z
  have hz' := (sum_eq_zero_iff_of_nonneg (fun z _ => sum_nonneg
    fun i _ => sq_nonneg (w z i - u i))).mp hz z (mem_univ _)
  funext i
  have hi := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (w z i - u i))).mp
    hz' i (mem_univ _)
  exact sub_eq_zero.mp ((sq_eq_zero_iff).mp hi)

private theorem sphere_rigidity {D Z : Type*} [Fintype D] [Fintype Z]
    (u : D → ℕ) (w : Z → D → ℕ)
    (hn : ∀ z, ∑ i, (w z i)^2 = ∑ i, (u i)^2)
    (hd : ∑ z, ∑ i, u i * w z i = Fintype.card Z * ∑ i, (u i)^2) :
    ∀ z, w z = u := by
  classical
  have he := sphere_rigidity_int (fun i => (u i : ℤ)) (fun z i => (w z i : ℤ))
    (fun z => by exact_mod_cast hn z) (by exact_mod_cast hd)
  intro z
  funext i
  exact_mod_cast congrFun (he z) i

private theorem dot_sum {D Z : Type*} [Fintype D] [Fintype Z]
    (u : D → ℕ) (w : Z → D → ℕ) :
    ∑ i, u i * (∑ z, w z i) = ∑ z, ∑ i, u i * w z i := by
  simp_rw [mul_sum]
  exact sum_comm

private theorem dot_multiple {D : Type*} [Fintype D]
    (u v : D → ℕ) (c : ℕ) :
    ∑ i, u i * (c * v i) = c * ∑ i, u i * v i := by
  rw [mul_sum]
  exact sum_congr rfl fun i _ => Nat.mul_left_comm _ _ _

/-- On a common sphere for targets and a common spherical slice for sources,
the integer broadcast relation picks out the desired diagonal exactly.
The distinguished source has value `v₀` and the other sources are indexed by `J`. -/
theorem broadcast_relation_iff {D Z J : Type*} [Fintype D] [Fintype Z] [Fintype J]
    (u v₀ : D → ℕ) (g : Z → D → ℕ) (v : J → D → ℕ)
    (hg : ∀ z, ∑ i, (g z i)^2 = ∑ i, (u i)^2)
    (hv : ∀ j, ∑ i, (v j i)^2 = ∑ i, (v₀ i)^2)
    (huv : ∀ j, ∑ i, u i * v j i = ∑ i, u i * v₀ i) :
    (∀ i, (∑ z, g z i) + Fintype.card J * v₀ i = Fintype.card Z * u i + ∑ j, v j i) ↔
      (∀ z, g z = u) ∧ ∀ j, v j = v₀ := by
  classical
  constructor
  · intro h
    have hpair := sum_congr (s₁ := (univ : Finset D)) rfl
      (fun i _ => congrArg (u i * ·) (h i))
    simp only [Nat.mul_add, sum_add_distrib, dot_sum, dot_multiple] at hpair
    simp_rw [huv] at hpair
    simp only [sum_const, card_univ, nsmul_eq_mul] at hpair
    have htarget : ∀ z, g z = u := by
      apply sphere_rigidity u g hg
      simpa only [sq, Nat.cast_id, Nat.add_right_cancel_iff] using hpair
    have hsource (i : D) : (∑ j, v j i) = Fintype.card J * v₀ i := by
      simpa only [htarget, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id, Nat.add_left_cancel_iff]
        using (h i).symm
    refine ⟨htarget, sphere_rigidity v₀ v hv ?_⟩
    simp_rw [sq]
    rw [← dot_sum, ← dot_multiple]
    simp_rw [hsource]
  · rintro ⟨ht, hs⟩ i
    simp [ht, hs]

private theorem sum_box_le {q : ℕ} {I : Type*} [Fintype I] (f : I → ℕ) (hf : ∀ x, f x ≤ q - 1) :
    ∑ x, f x ≤ Fintype.card I * (q - 1) := by
  simpa [nsmul_eq_mul] using sum_le_sum (s := (univ : Finset I))
    (g := fun _ => q - 1) (fun x _ => hf x)

/-- The same test inside a product of cyclic groups. The modulus exceeds
both sides of the coordinatewise integer equation. -/
theorem broadcast_mod_relation_iff {D Z J : Type*} [Fintype D] [Fintype Z] [Fintype J]
    {q L : ℕ} (hL : (Fintype.card Z + Fintype.card J) * (q - 1) < L)
    (u v₀ : D → ℕ) (g : Z → D → ℕ) (v : J → D → ℕ)
    (bu : ∀ i, u i ≤ q - 1) (bv₀ : ∀ i, v₀ i ≤ q - 1)
    (bg : ∀ z i, g z i ≤ q - 1) (bv : ∀ j i, v j i ≤ q - 1)
    (hg : ∀ z, ∑ i, (g z i)^2 = ∑ i, (u i)^2)
    (hv : ∀ j, ∑ i, (v j i)^2 = ∑ i, (v₀ i)^2)
    (huv : ∀ j, ∑ i, u i * v j i = ∑ i, u i * v₀ i) :
    ((∑ z, fun i => (g z i : ZMod L)) + Fintype.card J • (fun i => (v₀ i : ZMod L)) =
       Fintype.card Z • (fun i => (u i : ZMod L)) + ∑ j, fun i => (v j i : ZMod L)) ↔
      (∀ z, g z = u) ∧ ∀ j, v j = v₀ := by
  classical
  rw [← broadcast_relation_iff u v₀ g v hg hv huv]
  rw [add_mul] at hL
  constructor
  · intro h i
    have h₁ := lt_of_le_of_lt (Nat.add_le_add (sum_box_le (g · i) (bg · i))
      (Nat.mul_le_mul_left _ (bv₀ i))) hL
    have h₂ := lt_of_le_of_lt (Nat.add_le_add (Nat.mul_le_mul_left _ (bu i))
      (sum_box_le (v · i) (bv · i))) hL
    have e : (((∑ z, g z i) + Fintype.card J * v₀ i : ℕ) : ZMod L) =
        ((Fintype.card Z * u i + ∑ j, v j i : ℕ) : ZMod L) := by
      simpa only [Pi.add_apply, sum_apply, Pi.smul_apply, nsmul_eq_mul,
        Pi.mul_apply, Pi.natCast_apply, Nat.cast_mul, Nat.cast_add, Nat.cast_sum] using congrFun h i
    simpa only [ZMod.val_natCast_of_lt h₁, ZMod.val_natCast_of_lt h₂] using
      congrArg ZMod.val e
  · intro h
    funext i
    simpa only [Pi.add_apply, sum_apply, Pi.smul_apply, nsmul_eq_mul,
      Pi.mul_apply, Pi.natCast_apply, Nat.cast_mul, Nat.cast_add, Nat.cast_sum] using
      congrArg (Nat.cast (R := ZMod L)) (h i)

end Sunflower
end Combinatorics
end OAI
