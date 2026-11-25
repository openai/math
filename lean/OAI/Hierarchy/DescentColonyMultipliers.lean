import OAI.Hierarchy.DescentColonyLayout
import OAI.Hierarchy.DescentResidueMultiplication

namespace OAI
/-! # A family of binary-linear address layouts indexed by nonzero field multipliers -/

noncomputable section

namespace Hierarchy.DescentColonies
open DescentGL DescentBaseVariance DescentBinaryField
open scoped Classical

variable {K : Type*} [Field K] [Algebra (ZMod 2) K] {k j : ℕ}

/-- Coordinates can come from the power basis of any selected irreducible polynomial. -/
def fieldMultiplier (e : K ≃ₗ[ZMod 2] Bits k) (μ : Nonzero k) : Layout k :=
  let scalar := Units.mk0 (e.symm μ.val) (fun eq => μ.property (by simpa using congrArg e eq))
  e.symm.trans ((Units.mulLeftLinearEquiv (ZMod 2) K scalar).trans e)

theorem fieldMultiplier_apply (e : K ≃ₗ[ZMod 2] Bits k) (μ : Nonzero k) (v : Bits k) :
    fieldMultiplier e μ v = e (e.symm μ.val * e.symm v) := rfl

private theorem exchange (e : K ≃ₗ[ZMod 2] Bits k) (a b : Nonzero k) :
    fieldMultiplier e a b.val = fieldMultiplier e b a.val := by
  simp only [fieldMultiplier_apply,mul_comm]

private def orbit (e : K ≃ₗ[ZMod 2] Bits k) (d : Nonzero k) : Nonzero k ≃ Nonzero k :=
  (fieldMultiplier e d).toEquiv.subtypeEquiv fun x => by
    change x≠0 ↔ fieldMultiplier e d x≠0
    simp

private theorem prefix_count (e : K ≃ₗ[ZMod 2] Bits k) (hj : j≤k) (x y : Bits k) (ne : x≠y) :
    (Finset.univ.filter (fun μ : Nonzero k =>
      headRows hj (fieldMultiplier e μ x)=headRows hj (fieldMultiplier e μ y))).card = 2^(k-j)-1 := by
  let d : Nonzero k := ⟨x-y,sub_ne_zero.mpr ne⟩
  have equiv : {μ : Nonzero k // headRows hj (fieldMultiplier e μ x)=headRows hj (fieldMultiplier e μ y)} ≃
      {z : Nonzero k // headRows hj z.val=0} := by
    apply Equiv.subtypeEquiv (orbit e d)
    intro μ
    change _ ↔ headRows hj (fieldMultiplier e d μ.val)=0
    rw [exchange]
    change _ ↔ headRows hj (fieldMultiplier e μ (x-y))=0
    rw [map_sub]
    change _ ↔ headRows hj (fieldMultiplier e μ x)-headRows hj (fieldMultiplier e μ y)=0
    exact sub_eq_zero.symm
  have h := (Fintype.card_congr equiv).trans (zero_prefix_card hj)
  rwa [Fintype.card_subtype] at h

theorem fieldMultiplier_pairs (e : K ≃ₗ[ZMod 2] Bits k) (hj : j≤k) :
    PairBound (fun μ : Nonzero k => dyadicLayout hj (fieldMultiplier e μ)) := by
  intro x y ne
  let a := (address k).symm x
  let b := (address k).symm y
  have ab : a ≠ b := fun eq => ne ((address k).symm.injective eq)
  have count := prefix_count e hj a b ab
  have bound := DescentLinearLayouts.pairBound k j hj a b ab
  rw [DescentLinearLayouts.collision_exact hj a b ab,card_bits] at bound
  have actual : (Finset.univ.filter fun μ : Nonzero k =>
      dyadicLayout hj (fieldMultiplier e μ) x = dyadicLayout hj (fieldMultiplier e μ) y).card = 2^(k-j)-1 := by
    simpa only [dyadicLayout,Equiv.apply_eq_iff_eq,a,b] using count
  unfold collision
  rw [card_nonzero,show Fintype.card (Block j)=2^j by simp [Block]]
  apply le_trans _ bound
  apply le_of_eq
  apply congrArg (fun count : ℕ=>(count:ℝ)/((2^k-1:ℕ):ℝ))
  refine Eq.trans ?_ actual
  apply congrArg Finset.card
  ext μ
  let hits := fun a : Nonzero k =>
    dyadicLayout hj (fieldMultiplier e a) x = dyadicLayout hj (fieldMultiplier e a) y
  have classicalMem := @Finset.mem_filter (Nonzero k) hits
    (fun a => Classical.propDecidable (hits a)) Finset.univ μ
  have finiteMem := @Finset.mem_filter (Nonzero k) hits
    (fun a => instDecidableEqFin (2^j) (dyadicLayout hj (fieldMultiplier e a) x)
      (dyadicLayout hj (fieldMultiplier e a) y)) Finset.univ μ
  exact classicalMem.trans finiteMem.symm

/-- The unique value returned by the finite search for an irreducible modulus. -/
def modulus {k : ℕ} (hk : 0<k) : Bits k := (lookupModulus_spec hk).choose

theorem modulus_found {k : ℕ} (hk : 0<k) : lookupModulus k=some (modulus hk) :=
  (lookupModulus_spec hk).choose_spec.1

theorem modulus_irreducible {k : ℕ} (hk : 0<k) : Irreducible (candidate (modulus hk)) :=
  (lookupModulus_spec hk).choose_spec.2.2.2

def multiplier {k : ℕ} (hk : 0<k) : Nonzero k → Layout k :=
  letI : Fact (Irreducible (candidate (modulus hk))) := ⟨modulus_irreducible hk⟩
  fieldMultiplier (residueCoordinates (modulus hk))

theorem multiplier_native {k : ℕ} (hk : 0<k) (μ : Nonzero k) (x : Bits k) :
    multiply (modulus hk) μ.val x=multiplier hk μ x := by
  let : Fact (Irreducible (candidate (modulus hk))) := ⟨modulus_irreducible hk⟩
  exact (multiply_correct hk _ _ _).trans (fieldMultiplier_apply (residueCoordinates (modulus hk)) μ x).symm

theorem multiplier_pairs {k j : ℕ} (hk : 0<k) (hj : j≤k) :
    PairBound (fun μ : Nonzero k => dyadicLayout hj (multiplier hk μ)) := by
  let : Fact (Irreducible (candidate (modulus hk))) := ⟨modulus_irreducible hk⟩
  exact fieldMultiplier_pairs (residueCoordinates (modulus hk)) hj

end Hierarchy.DescentColonies

end
end OAI
