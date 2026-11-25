import OAI.LinearAlgebra.SpectralBooks.CrossingShortening
import OAI.LinearAlgebra.SpectralBooks.WireWidthClass
import OAI.LinearAlgebra.SpectralBooks.ConcreteSpectrum

/-!
# The crossing as a product of ordinary wires

The coefficient tensor with equality constraints on the diameters is the
tensor product, in the semiring of marked-site tensors, of those diameter
wires. Thus every normalized spectral point evaluates it as their product.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

namespace SiteTensor

universe v

variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]

/-- Group local coordinates of finitely many, possibly different, factors. -/
def Raw.finProduct {n : ℕ} (T : Fin n → Raw.{v} I K) : Raw.{v} I K :=
  ⟨fun i => ∀ j, (T j).Leg i, fun _ => inferInstance,
    fun x => ∏ j, (T j).coeff (fun i => x i j)⟩

/-- Grouping the factors represents their product in the restriction semiring. -/
theorem ofRaw_finProduct {n : ℕ} (T : Fin n → Raw.{v} I K) :
    ofRaw (Raw.finProduct T) = ∏ j, ofRaw (T j) := by
  classical
  induction n with
  | zero =>
    rw [Fin.prod_univ_zero]
    apply Quotient.sound
    apply Raw.reindex_equivalent (fun i => Equiv.equivPUnit ((j : Fin 0) → (T j).Leg i))
    intro x
    change ∏ j : Fin 0, (T j).coeff (fun i => x i j) = 1
    simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, ← ih, ← ofRaw_mul]
    apply Quotient.sound
    apply Raw.reindex_equivalent (fun i => (Fin.consEquiv (fun j => (T j).Leg i)).symm)
    intro x
    exact Fin.prod_univ_succ _

end SiteTensor

namespace Crossing

open SiteTensor

variable {D : ℕ}

/-- The marked diameter wire of width `m`. -/
def diameterWire (i : Fin D) (m : ℕ) : Wire (AxisSite D) :=
  ⟨some (i, false), some (i, true), by simp, m⟩

/-- The crossing tensor as a finite-site raw tensor. -/
def crossingRaw (F : Type*) [Field F] (D m : ℕ) : Raw.{0} (AxisSite D) F where
  Leg := AxisLeg m
  finiteLeg
    | none => inferInstanceAs (Fintype Unit)
    | some _ => inferInstanceAs (Fintype (BitString m))
  coeff := crossingTensor F D m

private def diameterLegEquiv (m : ℕ) (p : AxisSite D) :
    (∀ i : Fin D, (diameterWire i m).Leg p) ≃ AxisLeg m p :=
  match p with
  | none =>
    { toFun := fun _ => ()
      invFun := fun _ _ _ => false
      left_inv := fun _ => by funext i t; rcases t.2 with h | h <;> cases h
      right_inv := fun _ => rfl }
  | some (i, b) =>
    { toFun := fun x t => x i ⟨t, by cases b <;> simp [diameterWire]⟩
      invFun := fun u _ t => u t.1
      left_inv := fun x => by
        funext j t
        rcases t with ⟨v, ht⟩
        rcases ht with h | h <;> cases h <;> rfl
      right_inv := fun _ => rfl }

/-- The grouped product of diameter wires is precisely the crossing array. -/
theorem ofRaw_crossingRaw (F : Type*) [Field F] (D m : ℕ) :
    ofRaw (crossingRaw F D m) = ∏ i : Fin D, ofRaw ((diameterWire i m).raw F) := by
  rw [← ofRaw_finProduct]
  symm
  apply Quotient.sound
  apply Raw.reindex_equivalent (diameterLegEquiv m)
  intro x
  change ∀ p : AxisSite D, ∀ i : Fin D, (diameterWire i m).Leg p at x
  change (∏ i : Fin D, ((diameterWire i m).raw F).coeff (fun p => x p i)) = _
  change _ = ∏ i : Fin D, equalityEntry F
    (diameterLegEquiv m _ (x (some (i, false)))) (diameterLegEquiv m _ (x (some (i, true))))
  apply Finset.prod_congr rfl
  intro i _
  exact Wire.raw_coeff F (diameterWire i m) (fun p => x p i)

/-- Separate bits give independent copies of the unit-width crossing. -/
theorem ofRaw_crossingRaw_eq_pow (F : Type*) [Field F] (D m : ℕ) :
    ofRaw (crossingRaw F D m) = ofRaw (crossingRaw F D 1) ^ m := by
  rw [ofRaw_crossingRaw, ofRaw_crossingRaw, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact Wire.ofRaw_setWidth_eq_pow F (diameterWire i 1) m

/-- Multiplying the bit width corresponds to a tensor power. -/
theorem ofRaw_crossingRaw_mul_width (F : Type*) [Field F] (D m j : ℕ) :
    ofRaw (crossingRaw F D (m * j)) = ofRaw (crossingRaw F D m) ^ j := by
  rw [ofRaw_crossingRaw_eq_pow F D (m * j), ofRaw_crossingRaw_eq_pow F D m, pow_mul]

/-- Assigning the zero string everywhere is a nonzero coefficient of a wire. -/
theorem Wire.raw_coeff_ne_zero {I : Type*} [Fintype I] (F : Type*) [Field F] (e : Wire I) :
    (e.raw F).coeff ≠ 0 := by
  intro h
  have hh := congrFun h (e.basisTerm (fun _ => false))
  change (e.raw F).coeff (e.basisTerm (fun _ => false)) = (0 : F) at hh
  rw [Wire.raw_coeff] at hh
  simp [Wire.basisTerm] at hh

/-- The crossing with equal zero strings on every diameter has coefficient one. -/
theorem crossingRaw_coeff_ne_zero (F : Type*) [Field F] (D m : ℕ) :
    (crossingRaw F D m).coeff ≠ 0 := by
  let x : ∀ p : AxisSite D, AxisLeg m p := fun p =>
    match p with
    | none => ()
    | some _ => fun _ => false
  intro h
  have hz := congrFun h x
  change (∏ i : Fin D, equalityEntry F (fun _ : Fin m => false) (fun _ => false)) = 0 at hz
  simp [equalityEntry] at hz

/-- The crossing price at unit width is the sum of all diameter wire prices. -/
theorem logb_crossingRaw_one_eq_sum (F : Type*) [Field F] {D : ℕ}
    (φ : normalizedSpectrum (fun a b : TensorClass.{0} (AxisSite D) F => a ≤ b)) :
    Real.logb 2 (φ.val (ofRaw (crossingRaw F D 1)) : ℝ) =
      ∑ i, Real.logb 2 (φ.val (ofRaw ((diameterWire i 1).raw F)) : ℝ) := by
  change Real.logb 2 ((normalizedSpectrum.toRingHom φ) (ofRaw (crossingRaw F D 1)) : ℝ) = _
  rw [ofRaw_crossingRaw, map_prod, NNReal.coe_prod]
  apply Real.logb_prod
  intro i _
  apply ne_of_gt
  change 0 < (φ.val (ofRaw ((diameterWire i 1).raw F)) : ℝ)
  apply NNReal.coe_pos.mpr
  apply spectral_value_pos φ
  exact fun h => (Wire.raw_coeff_ne_zero F _) ((ofRaw_eq_zero_iff _).mp h)

end Crossing
end

end

end SpectralBooks
end LinearAlgebra
end OAI
