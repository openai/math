import OAI.LinearAlgebra.FiniteFourier.Transform
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Character bases for translations

The positive Fourier transform diagonalizes every additive translation of a finite abelian
group. A symmetric identification of a group with its character group lets the same character
table act with either register as control in the two-phase construction.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

variable (G K : Type*) [AddCommGroup G] [Field K] [Fintype G]

/-- Fourier change of coordinates between the standard basis and the character basis. -/
def fourierEquiv (h : Admissible G K) : (G → K) ≃ₗ[K] (Character G K → K) :=
  { (fourierMatrix G K).mulVecLin with
    invFun := inverseTransform G K
    left_inv := inverseTransform_transform G K h
    right_inv := transform_inverseTransform G K h }

/-- In coordinates the translation sending the standard vector at `y` to the vector at
`y + x` pulls a coefficient function back along subtraction of `x`. -/
def translate (x : G) : (G → K) ≃ₗ[K] (G → K) :=
  LinearEquiv.funCongrLeft K K (Equiv.subRight x)

omit [Fintype G] in
@[simp] theorem translate_apply (x : G) (v : G → K) (y : G) :
    translate G K x v y = v (y - x) := rfl

/-- All translations are diagonal in Fourier coordinates, with nonzero character eigenvalues. -/
theorem fourierEquiv_translate (h : Admissible G K) (x : G) (v : G → K) (χ : Character G K) :
    fourierEquiv G K h (translate G K x v) χ =
      (χ (Multiplicative.ofAdd x) : K) * fourierEquiv G K h v χ := by
  change (∑ g : G, (χ (Multiplicative.ofAdd g) : K) * v (g - x)) = _ * ∑ g : G, _ * v g
  rw [← Equiv.sum_comp (Equiv.addRight x) (fun g : G => (χ (Multiplicative.ofAdd g) : K) * v (g - x))]
  simp [fourierMatrix, Finset.mul_sum, mul_left_comm, mul_comm]

/-- The inverse Fourier images of the standard vectors form the simultaneous eigenbasis. -/
def characterBasis (h : Admissible G K) : Module.Basis (Character G K) K (G → K) :=
  (Pi.basisFun K (Character G K)).map (fourierEquiv G K h).symm

/-- The basis vector indexed by a character is its negative-character column divided by the group order. -/
theorem characterBasis_apply (h : Admissible G K) (χ : Character G K) (g : G) :
    characterBasis G K h χ g =
      (Fintype.card G : K)⁻¹ * (χ (Multiplicative.ofAdd (-g)) : K) := by
  classical
  change inverseTransform G K (Pi.basisFun K (Character G K) χ) g = _
  rw [inverseTransform_apply]
  simp [Pi.basisFun_apply, Pi.single_apply]

/-- The eigenvalue of translation by `x` on a character column is the character evaluated at `x`. -/
theorem translate_characterBasis (h : Admissible G K) (x : G) (χ : Character G K) :
    translate G K x (characterBasis G K h χ) =
      (χ (Multiplicative.ofAdd x) : K) • characterBasis G K h χ := by
  funext g
  simp [characterBasis_apply, sub_eq_add_neg, mul_left_comm]

private theorem primitiveRoot_of_separates (hsep : ∀ x y : Multiplicative G,
    (∀ χ : Character G K, χ x = χ y) → x = y) :
    ∃ ζ : K, IsPrimitiveRoot ζ (AddMonoid.exponent G) := by
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent
    (G := Multiplicative G) Monoid.ExponentExists.of_finite
  let E : Character G K →* Kˣ := MonoidHom.eval g
  have : Finite E.range := Finite.of_surjective E.rangeRestrict E.rangeRestrict_surjective
  obtain ⟨z, hz⟩ := Monoid.exists_orderOf_eq_exponent
    (G := E.range) Monoid.ExponentExists.of_finite
  refine ⟨((z : Kˣ) : K), IsPrimitiveRoot.coe_units_iff.mpr
    (IsPrimitiveRoot.coe_submonoidClass_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr ?_))⟩
  change orderOf z = Monoid.exponent (Multiplicative G)
  rw [← hg, hz]
  apply Nat.dvd_antisymm
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext ?_
    obtain ⟨χ, hχ⟩ := MonoidHom.mem_range.mp a.2
    change (a : Kˣ) ^ orderOf g = 1
    change χ g = (a : Kˣ) at hχ
    rw [← hχ, ← map_pow, pow_orderOf_eq_one, map_one]
  · apply orderOf_dvd_of_pow_eq_one
    refine hsep _ _ fun χ => ?_
    rw [map_pow, map_one]
    exact congrArg Subtype.val (Monoid.pow_exponent_eq_one (E.rangeRestrict χ))

/-- The splitting-field condition of the paper's introduction is equivalent to the exact
hypotheses of the two-phase lemma: the group order is invertible and the field affords every
character. An invertible Fourier matrix separates group elements. Evaluating all characters
at an element of maximal order then gives a group of values having that same exponent. -/
theorem admissible_iff_card_character : Admissible G K ↔
    (Fintype.card G : K) ≠ 0 ∧ Fintype.card (Character G K) = Fintype.card G := by
  classical
  refine ⟨fun h => ⟨h.1, card_character G K h⟩, ?_⟩
  rintro ⟨hN, hcard⟩
  refine ⟨hN, primitiveRoot_of_separates G K ?_⟩
  have hright : inverseFourierMatrix G K * fourierMatrix G K = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp
      (fourier_mul_inverse_of_card_ne_zero G K hN)
  have hinj : Function.Injective (fourierMatrix G K).mulVec := by
    intro u v huv
    have heq := congrArg (inverseFourierMatrix G K).mulVec huv
    simpa only [Matrix.mulVec_mulVec, hright, Matrix.one_mulVec] using heq
  intro x y hxy
  apply (Matrix.mulVec_injective_iff.mp hinj).injective (a₁ := x.toAdd) (a₂ := y.toAdd)
  exact funext fun χ => congrArg Units.val (hxy χ)

private theorem cyclic_pairing_symmetric {A B : Type*} [CommGroup A] [IsCyclic A]
    [CommGroup B] (E : A ≃* (A →* B)) (x y : A) : E x y = E y x := by
  obtain ⟨a, h⟩ := IsCyclic.exists_generator (α := A)
  obtain ⟨i, rfl⟩ := h x
  obtain ⟨j, rfl⟩ := h y
  simp [← zpow_mul, mul_comm]

/-- On every admissible finite abelian group the character table admits a symmetric
enumeration. On a cyclic factor every isomorphism with its dual gives a symmetric pairing;
taking the product of the factor pairings proves the result for the whole group. -/
theorem exists_symmetric_character_equiv (h : Admissible G K) :
    ∃ e : Multiplicative G ≃* Character G K, ∀ x y : G,
      e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) =
      e (Multiplicative.ofAdd y) (Multiplicative.ofAdd x) := by
  classical
  let : HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative G)) :=
    ⟨h.2, rootsOfUnity.isCyclic _ _⟩
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite (Multiplicative G)
  let A (i : ι) := Multiplicative (ZMod (n i))
  have (i : ι) : NeZero (n i) := NeZero.of_gt (hn i)
  have (i : ι) : HasEnoughRootsOfUnity K (Nat.card (A i)) := by
    have he : n i = orderOf (e.symm (Pi.mulSingle i (.ofAdd 1))) := by
      simpa only [MulEquiv.orderOf_eq, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf]
        using (ZMod.addOrderOf_one (n i)).symm
    apply HasEnoughRootsOfUnity.of_dvd K (n := Monoid.exponent (Multiplicative G))
    change Nat.card (Multiplicative (ZMod (n i))) ∣ _
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, he]
    exact Monoid.order_dvd_exponent (e.symm (Pi.mulSingle i (.ofAdd 1)))
  let E (i : ι) : A i ≃* (A i →* Kˣ) := (IsCyclic.monoidHom_equiv_self (A i) K).some.symm
  let toDual := ((MulEquiv.piCongrRight E).trans (Pi.monoidHomMulEquiv A Kˣ).symm).trans
    e.symm.monoidHomCongrLeft
  refine ⟨e.trans toDual, fun x y => ?_⟩
  change ((∏ i, (E i (e (.ofAdd x) i)).comp (Pi.evalMonoidHom A i)) (e (.ofAdd y))) =
    ((∏ i, (E i (e (.ofAdd y) i)).comp (Pi.evalMonoidHom A i)) (e (.ofAdd x)))
  simp only [MonoidHom.finsetProd_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
  exact Finset.prod_congr rfl fun i _ => cyclic_pairing_symmetric (E i) _ _

end

end

end FiniteFourier
end LinearAlgebra
end OAI
