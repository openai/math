import OAI.Computability.NearSquareRoot.InterchangeBQuestMixed

/-! # Closing mixed-volume recursive interchange commands

The combined space potential pays for the live parent row on contracted calls
and for the retained descriptor on full-volume calls. A single tied command
then runs with this potential on both its data and return stacks.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpace

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom Space

variable {X : Type} {job : Job X} {small full : X → List X} {V : X → ℕ}

private theorem park_peak_le (budget : X → ℕ) (ys : List X) (park cap : ℕ)
    (hp : park ≤ cap) (hc : ∀ y ∈ ys, park + budget y ≤ cap) :
    park + childPeak budget ys ≤ cap := by
  have bound := childPeak_le budget ys (cap - park) fun y hy => by have := hc y hy; omega
  omega

/-- A volume term and a logarithmic term can be charged to different classes
of children even when one of the classes is empty. -/
theorem mixed_space_bound (C H : ℕ) (height : X → ℕ)
    (order : ∀ x y, y ∈ small x ++ full x → height y < height x)
    (shrink : ∀ x y, y ∈ small x → 3 * V y ≤ 2 * V x)
    (contract : ∀ x y, y ∈ full x → V y ≤ V x) (x : X) :
    let cap := fun y => interchangeSpacePotential C H (height y) (V y)
    max (C * V x + childPeak cap (small x))
      (H * (Nat.log 2 (V x) + 1) + childPeak cap (full x)) ≤ cap x := by
  dsimp only
  let u := Nat.log 2 (V x) + 1
  have smallBase : C * V x ≤ interchangeSpacePotential C H (height x) (V x) := by
    have h : C * V x ≤ 3 * C * V x :=
      Nat.mul_le_mul_right _ (by omega)
    exact h.trans (Nat.le_add_right ..)
  have fullBase : H * u ≤ interchangeSpacePotential C H (height x) (V x) := by
    have h : H ≤ H * (height x + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    exact (Nat.mul_le_mul_right u h).trans (Nat.le_add_left ..)
  apply max_le
  · apply park_peak_le _ _ _ _ smallBase
    intro y hy
    have sh := shrink x y hy
    exact interchange_space_potential_descend (order x y (List.mem_append_left _ hy))
      (by omega) (Or.inr ⟨Nat.le_add_right .., sh⟩)
  · apply park_peak_le _ _ _ _ fullBase
    intro y hy
    exact interchange_space_potential_descend (order x y (List.mem_append_right _ hy))
      (contract x y hy) (Or.inl le_rfl)

/-- Width descent closes both classes of calls with the same tied program.
The child fares add with unit coefficient and both physical stacks have
linear volume bounds. -/
theorem Mixed.resolve (h : Mixed job small full V job.issue job.reply)
    (height : X → ℕ) (fare : X → ℝ) (ε : ℝ) (hε : 0 < ε)
    (power : ∀ x, 2 ^ height x ≤ V x) (localCost : ∀ x, (V x : ℝ) ≤ fare x)
    (slack : ∀ x, ((small x ++ full x).map fare).sum + ε * fare x ≤ fare x)
    (order : ∀ x y, y ∈ small x ++ full x → height y < height x)
    (shrink : ∀ x y, y ∈ small x → 3 * V y ≤ 2 * V x)
    (contract : ∀ x y, y ∈ full x → V y ≤ V x) :
    BoundedTask (fun x => ⌈fare x⌉₊) V job.issue job.reply := by
  obtain ⟨cmd, C, H, step⟩ := h.build
  have pos (x : X) : 1 ≤ V x := (Nat.pow_pos (by decide : 0 < 2)).trans_le (power x)
  have one (x : X) : (1 : ℝ) ≤ fare x := (by exact_mod_cast pos x : (1 : ℝ) ≤ V x).trans (localCost x)
  have nonneg (x : X) : 0 ≤ fare x := le_trans zero_le_one (one x)
  have scaled (x : X) : ((C * V x : ℕ) : ℝ) + 1 ≤ ((C : ℝ) + 1) * fare x := by
    rw [Nat.cast_mul, add_mul, one_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (localCost x) (Nat.cast_nonneg _)) (one x)
  obtain ⟨D, clock⟩ := exists_floor_clock (fun x => C * V x) (fun x => small x ++ full x) fare
    nonneg ((C : ℝ) + 1) ε hε scaled slack
  let t (x : X) := ⌊(D : ℝ) * fare x⌋₊
  let p (x : X) := interchangeSpacePotential C H (height x) (V x)
  have tied := resolve_tie_exact cmd job.issue job.reply t p p height
    (fun x => small x ++ full x) order (fun x env ih deck base hc => ?_)
  · let K := 3 * C + 4 * H
    refine ⟨.tie cmd, max (D + 1) K, fun x env deck base hc => ?_⟩
    have tm : t x + 1 ≤ (D + 1) * (⌈fare x⌉₊ + 1) := by
      have ht := floor_clock_le_mul_ceil D (nonneg x)
      dsimp only [t]
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
      omega
    have hm := tm.trans (Nat.mul_le_mul_right _ (le_max_left (D + 1) K))
    have sp : p x ≤ max (D + 1) K * (V x + 1) :=
      (interchange_space_potential_linear C H _ _ (power x)).trans
        (Nat.mul_le_mul (le_max_right ..) (Nat.le_succ _))
    exact (tied x env deck base hc).mono hm (Nat.add_le_add_left sp _) sp
  · have localRun := step x cmd env t p p ih deck base hc
    have timeBound := clock x
    have peak := mixed_space_bound C H height order shrink contract x
    exact localRun.mono (by dsimp only [t]; omega) (Nat.add_le_add_left peak _) peak

end InterchangeSpace

end NearSquareRoot
end Computability
end OAI
