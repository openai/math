import OAI.LinearAlgebra.FiniteFourier.CircuitParallel
import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization
import OAI.LinearAlgebra.FiniteFourier.ScalarDescent
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Cost of descent for a geometric grid

An extension-field word is simulated on all coordinates of a basis. A
monomial slot requires multiplication by fixed extension scalars. A shear
slot acts independently on the base coordinates. When a word implements a
ground-field matrix, the resulting ground-field circuit realizes one copy
per basis coordinate.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators

noncomputable section

variable {K E : Type*} [CommRing K] [CommRing E] [Algebra K E]
variable {D : Type*} [Fintype D] [DecidableEq D] {I : Type} [Fintype I] [DecidableEq I]

private theorem identity_free {A : Type*} [DecidableEq A] (K : Type*) [CommRing K] :
    RealizableAtMost (1 : Matrix A A K) 0 := by
  refine ⟨0, le_rfl, ⟨.nil, fun i => .scaled 1 (.inl i)⟩, ?_⟩
  ext i j
  simp [Circuit.matrix, Circuit.eval, Readout.eval, Matrix.one_apply, Pi.single_apply]

omit [Fintype D] [Fintype I] in
private theorem restrictMatrix_one (b : Module.Basis D K E) :
    restrictMatrix b (1 : Matrix I I E) = 1 := by
  classical
  ext ⟨i, u⟩ ⟨j, v⟩
  by_cases h : i = j
  · subst j
    simp [restrictMatrix, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  · simp [restrictMatrix, h]

/-- Two slots per stage give additive gate bounds when simulating an
extension word in base-field coordinates. -/
theorem realizable_restrictMatrix_of_word (b : Module.Basis D K E)
    {A : Matrix I I E} {d monCost shearCost : ℕ} (hw : LayerWord d A)
    (hmon : ∀ M : Matrix I I E, LayerMatrix .monomial M → RealizableAtMost (restrictMatrix b M) monCost)
    (hshear : ∀ S : Matrix I I E, LayerMatrix .shear S → RealizableAtMost (restrictMatrix b S) shearCost) :
    RealizableAtMost (restrictMatrix b A) (d * (monCost + shearCost)) := by
  induction d generalizing A with
  | zero =>
    obtain rfl : A = 1 := hw
    simpa only [restrictMatrix_one, Nat.zero_mul] using identity_free (A := I × D) K
  | succ d ih =>
    obtain ⟨M, S, P, hM, hS, hP, rfl⟩ := hw
    rw [restrictMatrix_mul, restrictMatrix_mul]
    simpa only [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      ((hshear S hS).mul (hmon M hM)).mul (ih hP)

/-- The circuit obtained by restricting the scalars of a word for a
ground-field transform implements independent copies on all basis coordinates. -/
theorem realizable_packed_of_word (b : Module.Basis D K E) (T : Matrix I I K)
    {d monCost shearCost : ℕ} (hw : LayerWord d (T.map (algebraMap K E)))
    (hmon : ∀ M : Matrix I I E, LayerMatrix .monomial M → RealizableAtMost (restrictMatrix b M) monCost)
    (hshear : ∀ S : Matrix I I E, LayerMatrix .shear S → RealizableAtMost (restrictMatrix b S) shearCost) :
    RealizableAtMost (Matrix.blockDiagonal (fun _ : D => T)) (d * (monCost + shearCost)) := by
  have h := realizable_restrictMatrix_of_word b hw hmon hshear
  rw [restrictMatrix_algebraMap] at h
  exact h

private def batchEmbedding (A : Type*) {X Y Z : Type*} (f : X ↪ Y × Z) : A × X ↪ (A × Y) × Z :=
  ((Function.Embedding.refl A).prodMap f).trans (Equiv.prodAssoc A Y Z).symm.toEmbedding

omit [DecidableEq I] in
/-- Repeat a packed circuit and restrict its last batch to the required number
of inputs. The cost counts every gate over the ground field. -/
theorem realizable_from_packed {R : Type*} [CommSemiring R] {J : Type*} (T : Matrix J I R) {s : ℕ}
    (hp : RealizableAtMost (Matrix.blockDiagonal (fun _ : D => T)) s)
    (hd : 0 < Fintype.card D) (h : ℕ) :
    RealizableAtMost (Matrix.blockDiagonal (fun _ : Fin h => T)) ((h ⌈/⌉ Fintype.card D) * s) := by
  classical
  let q := h ⌈/⌉ Fintype.card D
  have hcap : h ≤ Fintype.card D * q := (ceilDiv_le_iff_le_mul hd).mp le_rfl
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := Fin h) (β := D × Fin q)
    (by simpa using hcap)
  have hbatch := (hp.blockDiagonal (Fin q)).submatrix (batchEmbedding J f) (batchEmbedding I f)
  rw [Fintype.card_fin] at hbatch
  convert hbatch using 1
  ext ⟨j,u⟩ ⟨i,v⟩
  change (if u = v then T j i else 0) =
    if (f u).2 = (f v).2 then (if (f u).1 = (f v).1 then T j i else 0) else 0
  by_cases huv : u = v
  · simp [huv]
  · have hf : f u ≠ f v := fun he => huv (f.injective he)
    by_cases h₂ : (f u).2 = (f v).2
    · have h₁ : (f u).1 ≠ (f v).1 := fun h₁ => hf (Prod.ext h₁ h₂)
      simp [huv, h₁, h₂]
    · simp [huv, h₂]

/-- The number of base arrays after padding a last, partial batch is at most
twice the number required, whenever the extension degree fits the capacity. -/
theorem paddedBatch_capacity (h e : ℕ) (he : e ≤ h) :
    (h ⌈/⌉ e) * e ≤ 2 * h := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have := Nat.div_mul_le_self (h + e - 1) e
  omega

/-- The logarithmic number of layers is absorbed by the gap between the
single-layer exponent `β` and the target exponent `α`. This estimate is
uniform on all base sizes, including the smallest grids. -/
theorem absorb_grid_depth {t α β : ℝ} (ht : 0 ≤ t) (hβα : β < α) :
    (1 + Real.logb 2 (1+t)) * (1+t)^β ≤
      (1 + 1 / ((α - β) * Real.log 2)) * (1+t)^α := by
  have hpos : 0 < 1+t := by linarith
  have hg := sub_pos.mpr hβα
  have hpow : 1 ≤ (1+t)^(α-β) := Real.one_le_rpow (by linarith) hg.le
  have hlog := Real.log_le_rpow_div hpos.le hg
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf : Real.logb 2 (1+t) ≤ (1+t)^(α-β) / ((α-β) * Real.log 2) := by
    rw [Real.logb, ← div_div]
    exact div_le_div_of_nonneg_right hlog hlog2.le
  calc
    _ ≤ ((1+t)^(α-β) + (1+t)^(α-β) / ((α-β) * Real.log 2)) * (1+t)^β :=
      mul_le_mul_of_nonneg_right (add_le_add hpow hf) (Real.rpow_nonneg hpos.le _)
    _ = (1 + 1 / ((α-β) * Real.log 2)) * ((1+t)^(α-β) * (1+t)^β) := by ring
    _ = _ := by rw [← Real.rpow_add hpos, sub_add_cancel]

/-- Quantitative field descent for one group of small axes. If a monomial/shear
stage on the extension can be simulated within the single-stage budget, a word
of logarithmic depth gives the advertised bound over the base field on all
complementary fibers. The bound is independent of the extension degree. -/
theorem grid_group_descent (b : Module.Basis D K E) (T : Matrix I I K) {h depth monCost shearCost : ℕ}
    (he : 0 < Fintype.card D) (hcap : Fintype.card D ≤ h)
    (hw : LayerWord depth (T.map (algebraMap K E)))
    (hmon : ∀ M : Matrix I I E, LayerMatrix .monomial M → RealizableAtMost (restrictMatrix b M) monCost)
    (hshear : ∀ S : Matrix I I E, LayerMatrix .shear S → RealizableAtMost (restrictMatrix b S) shearCost)
    {B C D₀ t α β : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D₀) (ht : 0 ≤ t)
    (hβα : β < α) (hd : (depth : ℝ) ≤ D₀ * (1 + Real.logb 2 (1+t)))
    (hstage : ((monCost + shearCost : ℕ) : ℝ) ≤ C * Fintype.card D * B * (1+t)^β) :
    (complexity (Matrix.blockDiagonal (fun _ : Fin h => T)) : ℝ) ≤
      (2 * C * D₀ * (1 + 1 / ((α-β) * Real.log 2))) * ((h : ℝ) * B) * (1+t)^α := by
  let q := h ⌈/⌉ Fintype.card D
  have hr := realizable_from_packed T (realizable_packed_of_word b T hw hmon hshear) he h
  have hcost := (complexity_le_iff _ _).2 hr
  have hpad : (q : ℝ) * (Fintype.card D : ℝ) ≤ 2 * h := by
    exact_mod_cast paddedBatch_capacity h (Fintype.card D) hcap
  have hlog : 0 ≤ Real.logb 2 (1+t) := Real.logb_nonneg (by norm_num) (by linarith)
  push_cast at hstage
  calc
    _ ≤ (q : ℝ) * ((depth : ℝ) * (monCost + (shearCost : ℝ))) := by exact_mod_cast hcost
    _ ≤ (q : ℝ) * ((D₀ * (1+Real.logb 2 (1+t))) * (C * Fintype.card D * B * (1+t)^β)) := by
      gcongr
    _ = ((q : ℝ) * Fintype.card D) * (C * D₀ * B) * ((1+Real.logb 2 (1+t)) * (1+t)^β) := by ring
    _ ≤ (2 * h) * (C * D₀ * B) * ((1 + 1 / ((α-β) * Real.log 2)) * (1+t)^α) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hpad (by positivity))
        (absorb_grid_depth ht hβα) (by positivity) (by positivity)
    _ = _ := by ring

end

end FiniteFourier
end LinearAlgebra
end OAI
