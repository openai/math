import OAI.Computability.BorderVNP.CoverLorentzLayers
import Mathlib.GroupTheory.Index

/-!
# Sizes of the congruence layers

For the quaternion group of §5.1, reduction to the first three imaginary
coefficients identifies the kernel between consecutive levels. From depth two
onwards it takes all values in the three-dimensional additive group over `ZMod 7`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

/-- A norm-one quaternion as a unit, with inverse its conjugate. -/
def normUnit (x : Order) (h : norm x = 1) : Orderˣ :=
  ⟨x, star x, mul_star_eq_one x h, star_comm_self.eq.trans (mul_star_eq_one x h)⟩

/-- Inverse in the unit group agrees with quaternion conjugation at norm one. -/
theorem inverse_star (u : Orderˣ) (h : norm u = 1) :
    (↑u⁻¹ : Order) = star (u : Order) := by
  calc
    _ = (↑u⁻¹ : Order) * ((u : Order) * star (u : Order)) := by rw [mul_star_eq_one _ h, mul_one]
    _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]

/-- The norm-one principal congruence subgroup of level `7^d`. -/
def gamma (d : ℕ) : Subgroup Orderˣ where
  carrier := {u | norm u = 1 ∧ ∃ x, (u : Order) = atDepth d x}
  one_mem' := ⟨rfl, 0, by simp [atDepth]⟩
  mul_mem' := by
    rintro a b ⟨ha,x,hx⟩ ⟨hb,y,hy⟩
    exact ⟨by simp only [Units.val_mul,norm_mul,ha,hb,one_mul],
      _,by rw [Units.val_mul,hx,hy,depth_mul]⟩
  inv_mem' := by
    rintro a ⟨ha,x,hx⟩
    exact ⟨by rw [inverse_star a ha,norm_star,ha],
      star x,by rw [inverse_star a ha,hx,star_atDepth]⟩

/-- Conjugation by any integral unit preserves all principal norm-one congruence levels. -/
instance gammaNormal (d : ℕ) : (gamma d).Normal where
  conj_mem := by
    rintro x ⟨hx,y,hy⟩ g
    have hg : norm (g : Order) * norm (↑g⁻¹ : Order) = 1 := by
      rw [← norm_mul,Units.mul_inv]; rfl
    refine ⟨?_,(g : Order)*y*(↑g⁻¹ : Order),?_⟩
    · simp only [Units.val_mul,norm_mul,hx,mul_one,hg]
    · rw [Units.val_mul,Units.val_mul,hy]
      simp only [atDepth,mul_add,add_mul,mul_one,Units.mul_inv,mul_smul_comm,smul_mul_assoc]

/-- The deck group of the level-`7^d` cover over the first congruence level. -/
abbrev Deck (d : ℕ) := gamma 1 ⧸ (gamma d).subgroupOf (gamma 1)

/-- An integral coefficient is uniquely determined by its full congruence expansion. -/
theorem atDepth_inj (d : ℕ) : Function.Injective (atDepth d) := by
  intro x y h
  have hv : (7 : ℤ)^d • x = (7 : ℤ)^d • y := add_left_cancel h
  have hn : (7 : ℤ)^d ≠ 0 := pow_ne_zero d (by decide)
  ext
  all_goals
    first
    | exact mul_left_cancel₀ hn (congrArg QuaternionAlgebra.re hv)
    | exact mul_left_cancel₀ hn (congrArg QuaternionAlgebra.imI hv)
    | exact mul_left_cancel₀ hn (congrArg QuaternionAlgebra.imJ hv)
    | exact mul_left_cancel₀ hn (congrArg QuaternionAlgebra.imK hv)

/-- The full integral coefficient at depth `d`, before reduction modulo seven. -/
noncomputable def coefficient (d : ℕ) (x : gamma d) : Order := x.2.2.choose

/-- The first integral coefficient reconstructs the full element at its specified level. -/
theorem coefficient_spec (d : ℕ) (x : gamma d) :
    (x.val.val : Order) = atDepth d (coefficient d x) := x.2.2.choose_spec

/-- Exact coefficient of a product at equal depths. -/
theorem coeff_mul (d : ℕ) (x y : gamma d) : coefficient d (x*y) =
    coefficient d x + coefficient d y + (7 : ℤ)^d • (coefficient d x * coefficient d y) := by
  apply atDepth_inj
  rw [← depth_mul,← coefficient_spec,← coefficient_spec,← coefficient_spec]
  rfl

/-- The three imaginary coefficients modulo seven. -/
def residues : Order →+ (ZMod 7 × ZMod 7 × ZMod 7) where
  toFun x := (x.imI, x.imJ, x.imK)
  map_zero' := by simp
  map_add' x y := by ext <;> simp

/-- Multiples of seven vanish in each imaginary residue coordinate. -/
theorem residues_seven (x : Order) : residues ((7:ℤ) • x) = 0 := by
  change ((↑(7*x.imI) : ZMod 7), (↑(7*x.imJ) : ZMod 7), (↑(7*x.imK) : ZMod 7)) = (0,0,0)
  simp only [Int.cast_mul, Int.cast_ofNat, show (7 : ZMod 7) = 0 by decide, zero_mul]

/-- The imaginary residue vector respects the congruence relation modulo seven. -/
theorem residues_congr {x y : Order} (h : SevenEq x y) : residues x = residues y := by
  obtain ⟨u,rfl⟩ := h
  rw [map_add, residues_seven, add_zero]

/-- The homomorphism from a positive-depth group to its additive leading residues. -/
noncomputable def leading (d : ℕ) :
    gamma (d+1) →* Multiplicative (ZMod 7 × ZMod 7 × ZMod 7) where
  toFun x := Multiplicative.ofAdd (residues (coefficient (d+1) x))
  map_one' := by
    change residues (coefficient (d+1) 1) = 0
    have hc : coefficient (d+1) 1 = 0 := by
      apply atDepth_inj
      rw [← coefficient_spec]
      simp [atDepth]
    rw [hc,map_zero]
  map_mul' x y := by
    change residues (coefficient (d+1) (x*y)) =
      residues (coefficient (d+1) x) + residues (coefficient (d+1) y)
    rw [coeff_mul,map_add,map_add,pow_succ',← smul_smul,residues_seven,add_zero]

/-- The leading homomorphism is surjective at every depth at least two. -/
theorem leading_surj (d : ℕ) : Function.Surjective (leading (d+1)) := by
  rintro ⟨a,b,c⟩
  obtain ⟨x,hx,hr⟩ := imaginary_realized d ⟨a.val,a.val_lt⟩ ⟨b.val,b.val_lt⟩ ⟨c.val,c.val_lt⟩
  let g : gamma (d+2) := ⟨normUnit (atDepth (d+2) x) hx, hx, x, rfl⟩
  have he : coefficient (d+2) g = x :=
    atDepth_inj _ (coefficient_spec (d+2) g).symm
  refine ⟨g,?_⟩
  change residues (coefficient (d+2) g) = (a,b,c)
  rw [he,residues_congr hr]
  ext <;> simp [residues,basisI,basisJ,basisK]

/-- Increasing depth by one gives a subgroup of the preceding level. -/
theorem gamma_next (d : ℕ) : gamma (d+1) ≤ gamma d := by
  rintro x ⟨hx,y,hy⟩
  exact ⟨hx,(7:ℤ) • y, by rw [hy]; simp only [atDepth, smul_smul, pow_succ]⟩

/-- The next congruence level is the kernel of the leading coefficient homomorphism. -/
theorem leading_kernel (d : ℕ) :
    (leading d).ker = (gamma (d+2)).subgroupOf (gamma (d+1)) := by
  ext x
  let y := coefficient (d+1) x
  have hy : x.val.val = atDepth (d+1) y := coefficient_spec _ x
  change residues y = 0 ↔ norm x.val.val = 1 ∧ ∃ z, x.val.val = atDepth (d+2) z
  constructor
  · intro h
    have nr : norm (atDepth (d+1) y) = 1 := hy ▸ x.2.1
    have hr := leading_scalar_dvd d y nr
    have hi : 7 ∣ y.imI := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).1 (congrArg Prod.fst h)
    have hj : 7 ∣ y.imJ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).1 (congrArg (fun z => z.2.1) h)
    have hk : 7 ∣ y.imK := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).1 (congrArg (fun z => z.2.2) h)
    obtain ⟨r,hr⟩ := hr
    obtain ⟨i,hi⟩ := hi
    obtain ⟨j,hj⟩ := hj
    obtain ⟨k,hk⟩ := hk
    let z : Order := ⟨r,i,j,k⟩
    have hz : y = (7 : ℤ) • z := QuaternionAlgebra.ext hr hi hj hk
    exact ⟨x.2.1,z,by rw [hy,hz]; simp only [atDepth,smul_smul,pow_succ]⟩
  · rintro ⟨_,z,hz⟩
    have he : y = (7:ℤ) • z := by
      apply atDepth_inj (d+1)
      rw [← hy,hz]
      simp only [atDepth,smul_smul,pow_succ]
    rw [he,residues_seven]

/-- Consecutive layers have index seven cubed once the lower depth is at least two. -/
theorem layer_relIndex (d : ℕ) : (gamma (d+3)).relIndex (gamma (d+2)) = 7^3 := by
  rw [Subgroup.relIndex, ← leading_kernel (d+1), Subgroup.index_eq_card]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (leading_surj d)).toEquiv]
  change Nat.card (ZMod 7 × ZMod 7 × ZMod 7) = _
  simp

/-- Number of deck addresses over the first congruence level. -/
noncomputable def tileCount (d : ℕ) : ℕ := (gamma d).relIndex (gamma 1)

/-- The group cardinal equals the number of congruence tile addresses. -/
theorem deck_card (d : ℕ) : Nat.card (Deck d) = tileCount d := rfl

/-- The first relative group has at least one and at most 343 elements. -/
theorem tileCount_two_bounds : 0 < tileCount 2 ∧ tileCount 2 ≤ 7^3 := by
  rw [tileCount, Subgroup.relIndex, ← leading_kernel 0, Subgroup.index_ker]
  refine ⟨Nat.card_pos, ?_⟩
  have h := Nat.card_le_card_of_injective (Subtype.val : (leading 0).range →
    Multiplicative (ZMod 7 × ZMod 7 × ZMod 7)) Subtype.val_injective
  change Nat.card (leading 0).range ≤ Nat.card (ZMod 7 × ZMod 7 × ZMod 7) at h
  simpa using h

/-- Every positive congruence level is contained in the base group. -/
theorem gamma_le_one (d : ℕ) : gamma (d+1) ≤ gamma 1 := by
  induction d with
  | zero => exact le_rfl
  | succ d h => exact (gamma_next _).trans h

/-- Exact multiplicative growth of the tile count in the stable range. -/
theorem tileCount_eq (d : ℕ) : tileCount (d+2) = (7^3)^d * tileCount 2 := by
  induction d with
  | zero => simp
  | succ d h =>
    have e := Subgroup.relIndex_mul_relIndex (gamma (d+3)) (gamma (d+2)) (gamma 1)
      (gamma_next (d+2)) (gamma_le_one (d+1))
    rw [layer_relIndex] at e
    change 7^3 * tileCount (d+2) = tileCount (d+3) at e
    rw [← e,h,pow_succ]
    ring

end Cover

end BorderVNP
end Computability
end OAI
