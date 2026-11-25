import OAI.LinearAlgebra.FiniteFourier.OpenConvolution
import OAI.LinearAlgebra.FiniteFourier.FractionFreeWires
import OAI.LinearAlgebra.FiniteFourier.ReadoutAlignment

/-! # Clearing the denominators of an open convolution reduction

The same cleared input map is used on each operand. On each shorter
convolution the two blocks have a common scale, whose square is the scale
of every coefficient passed to the output circuit.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators

/-- A common scaling on both blocks scales their entire convolution by its square. -/
theorem openConv_scale {R : Type*} [CommRing R] (n : ℕ) (x y : Fin n → R) (a : R)
    (k : Fin (2*n-1)) :
    openConv R n (fun i => a * x i) (fun j => a * y j) k = a ^ 2 * openConv R n x y k := by
  simp only [openConv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

/-- Use the least common multiple on a block whenever it is permitted by
the denominator support. A product works for an arbitrary submonoid. -/
noncomputable def supportedBlockScale {B : Type*} {F : B → Type*}
    [∀ b, Fintype (F b)] (S : Submonoid ℕ) (T : (Σ b, F b) → ℕ) (b : B) : ℕ := by
  classical
  let m := Finset.univ.lcm (fun i : F b => T ⟨b,i⟩)
  exact if m ∈ S then m else blockScale T b

/-- Over an LCM-closed localization, alignment takes the actual least common
multiple of the scales in the block. -/
theorem supportedBlockScale_eq_lcm {B : Type*} {F : B → Type*} [∀ b, Fintype (F b)]
    (S : Submonoid ℕ) (hS : ∀ {a b : ℕ}, a ∈ S → b ∈ S → a.lcm b ∈ S)
    (T : (Σ b, F b) → ℕ) (hT : ∀ z, T z ∈ S) (b : B) :
    supportedBlockScale S T b = Finset.univ.lcm (fun i : F b => T ⟨b,i⟩) := by
  classical
  have hmem (s : Finset (F b)) : s.lcm (fun i => T ⟨b,i⟩) ∈ S := by
    induction s using Finset.induction_on with
    | empty => exact S.one_mem
    | insert i s _ ih =>
      rw [Finset.lcm_insert]
      exact hS (hT _) ih
  simp [supportedBlockScale, hmem]

theorem supportedBlockScale_spec {B : Type*} {F : B → Type*} [∀ b, Fintype (F b)]
    (S : Submonoid ℕ) (T : (Σ b, F b) → ℕ) (hT : ∀ z, 0 < T z ∧ T z ∈ S) (b : B) :
    0 < supportedBlockScale S T b ∧ supportedBlockScale S T b ∈ S ∧
      ∀ i : F b, T ⟨b,i⟩ ∣ supportedBlockScale S T b := by
  classical
  unfold supportedBlockScale
  dsimp only
  split_ifs with hm
  · refine ⟨?_, hm, fun i => Finset.dvd_lcm (Finset.mem_univ i)⟩
    apply Nat.pos_of_ne_zero
    exact Finset.lcm_ne_zero_iff.mpr (fun i _ => (hT ⟨b,i⟩).1.ne')
  · exact ⟨Finset.prod_pos (fun i _ => (hT ⟨b,i⟩).1),
      S.prod_mem (fun i _ => (hT ⟨b,i⟩).2), fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)⟩

namespace OpenConvolution

variable {n : ℕ} {B : Type*} {len : B → ℕ}

/-- A scale common to the two operands of each child becomes that child's
squared scale, even when the shorter convolutions have different lengths. -/
theorem children_cast_of_scale {p : OpenConvolution ℚ n B len} {q : OpenConvolution ℤ n B len}
    (D : B → ℕ)
    (hL : ∀ (x : Fin n → ℤ) z, (q.input.eval x z : ℚ) =
      D z.1 * p.input.eval (fun i => (x i : ℚ)) z)
    (x y : Fin n → ℤ) (z : Σ b, Fin (2 * len b - 1)) :
    (q.children x y z : ℚ) = (D z.1 : ℚ)^2 *
      p.children (fun i => (x i : ℚ)) (fun i => (y i : ℚ)) z := by
  unfold children
  refine (openConv_map (Int.castRingHom ℚ) _ _ _ _).trans ?_
  simp only [Function.comp_def, Int.coe_castRingHom, hL, openConv_scale]

/-- Clear a localized rational formula before filling the convolution gates.
The scale of the resulting integer formula is positive and belongs to the
same denominator submonoid. Both linear circuits retain their gate counts. -/
theorem clearDenominators (p : OpenConvolution ℚ n B len) (S : Submonoid ℕ)
    (hL : p.input.DenominatorsIn S) (hH : p.output.DenominatorsIn S)
    (hp : p.RealizesMultiple 1) :
    ∃ (q : OpenConvolution ℤ n B len) (D : ℕ), 0 < D ∧ D ∈ S ∧
      q.inputSize = p.inputSize ∧ q.outputSize = p.outputSize ∧ q.RealizesMultiple (D : ℤ) := by
  classical
  let rule : WireAlignment S :=
    if h : ∀ {a b : ℕ}, a ∈ S → b ∈ S → a.lcm b ∈ S
    then WireAlignment.lcm S h else WireAlignment.product S
  obtain ⟨L, T, _, hT, hLe⟩ := p.input.clearDenominatorsWith S rule hL (fun _ => 1)
    (fun _ => ⟨Nat.one_pos, S.one_mem⟩)
  let D := supportedBlockScale S T
  have hblock := supportedBlockScale_spec S T hT
  let aligned := L.scaleReadouts (fun z => ((D z.1 / T z : ℕ) : ℤ))
  have hLa (x : Fin n → ℤ) (z : Σ b, Fin (len b)) :
      (aligned.eval x z : ℚ) = D z.1 * p.input.eval (fun i => (x i : ℚ)) z := by
    obtain ⟨b,i⟩ := z
    have hdiv := Nat.div_mul_cancel ((hblock b).2.2 i)
    simp only [aligned, Circuit.eval_scaleReadouts, Int.cast_mul, Int.cast_natCast, hLe,
      Nat.cast_one, div_one, ← mul_assoc, ← Nat.cast_mul, D, hdiv]
  let scale (z : Σ b, Fin (2 * len b - 1)) := (D z.1)^2
  obtain ⟨H, U, _, hU, hHe⟩ := p.output.clearDenominatorsWith S rule hH scale
    (fun z => ⟨pow_pos (hblock z.1).1 _, S.pow_mem (hblock z.1).2.1 _⟩)
  obtain ⟨hD, hHa⟩ := H.alignOutputs_spec U S _ hU hHe
  let q : OpenConvolution ℤ n B len :=
    ⟨p.inputSize, p.outputSize, aligned, H.alignOutputs U⟩
  refine ⟨q, ∏ j, U j, hD.1, hD.2, rfl, rfl, ?_⟩
  intro x y k
  apply Int.cast_injective (α := ℚ)
  have he (z : Σ b, Fin (2 * len b - 1)) :
      (q.children x y z : ℚ) / scale z =
        p.children (fun i => (x i : ℚ)) (fun i => (y i : ℚ)) z := by
    rw [children_cast_of_scale (p := p) (q := q) _ hLa]
    dsimp [scale]
    rw [Nat.cast_pow, mul_div_cancel_left₀]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (hblock z.1).1.ne')
  change ((H.alignOutputs U).eval (q.children x y) k : ℚ) = _
  rw [hHa, funext he]
  change _ * p.eval _ _ k = _
  rw [hp, one_mul, Int.cast_mul, Int.cast_natCast]
  congr 1
  exact (openConv_map (Int.castRingHom ℚ) _ x y k).symm

end OpenConvolution

end FiniteFourier
end LinearAlgebra
end OAI
