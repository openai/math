import OAI.LinearAlgebra.FiniteFourier.DyadicCoefficients
import OAI.LinearAlgebra.FiniteFourier.PackedParameters

/-! # Coefficients and Fourier nodes for a packed dyadic list -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

noncomputable section

variable {η : ℝ} {n B : ℕ}

namespace DyadicAxisPacking

/-- The common root order is fixed before selecting the final axes from the pool. -/
def rootOrder (D : DyadicAxisPacking GaussianRationals η n B) : ℕ :=
  axisRootOrder D.pool (8*B)

theorem rootOrder_pos (D : DyadicAxisPacking GaussianRationals η n B) : 0 < D.rootOrder :=
  axisRootOrder_pos _ fun _ hp => (mem_dyadicEligibleAxes.mp (D.eligible hp)).2.1.two_le

theorem axis_properties (D : DyadicAxisPacking GaussianRationals η n B) (hB : 6 ≤ B)
    {p : ℕ} (hp : p ∈ D.packing.axes) :
    p.Prime ∧ 3 ≤ p ∧ p ≤ B ∧ p-1 ∣ D.rootOrder := by
  have h := D.packing.axes_subset hp
  obtain ⟨⟨hl,hu⟩,hpr,_⟩ := mem_dyadicEligibleAxes.mp (D.eligible h)
  refine ⟨hpr, by omega, hu, predecessor_dvd_axisRootOrder _ h⟩

theorem binaryPower_dvd (D : DyadicAxisPacking GaussianRationals η n B)
    {k : ℕ} (hk : 2^k ≤ 8*B) : 2^k ∣ D.rootOrder :=
  two_pow_dvd_axisRootOrder _ hk

end DyadicAxisPacking

/-- A single coefficient order, with the forbidden-prime and packing data used
at each stage of one dyadic open list. -/
structure DyadicCoefficientTower (D : DyadicAxisPacking GaussianRationals η n B) (L : Finset ℕ) where
  modulus : (protectedGaussian L)[X]
  monic : modulus.Monic
  degree_eq : modulus.natDegree = listCyclotomicDegree GaussianRationals D.pool B
  domain : IsDomain (AdjoinRoot modulus)
  primitive : IsPrimitiveRoot (AdjoinRoot.root modulus) D.rootOrder
  gaussian : AdjoinRoot.root modulus ^ (D.rootOrder/4) =
    algebraMap _ (AdjoinRoot modulus) (protectedGaussianI L)
  width : 6 ≤ B
  protected_prime : ∀ l ∈ L, l.Prime
  protected_coprime : ∀ l ∈ L, l.Coprime D.orderTimesVolume

/-- Realize a tower at the chosen list degree whenever the specified primes avoid the list. -/
theorem exists_dyadicCoefficientTower (D : DyadicAxisPacking GaussianRationals η n B)
    (L : Finset ℕ) (hB : 6 ≤ B) (hL : ∀ l ∈ L, l.Prime)
    (ha : ∀ l ∈ L, ¬ l ∣ D.orderTimesVolume) : Nonempty (DyadicCoefficientTower D L) := by
  let : NeZero D.rootOrder := ⟨D.rootOrder_pos.ne'⟩
  have h₄ : 4 ∣ D.rootOrder := D.binaryPower_dvd (k := 2) (by norm_num; omega)
  obtain ⟨m,hm,hd,dom,prim,gauss⟩ := exists_protectedGaussian_presentation L h₄
  exact ⟨⟨m,hm,hd,dom,prim,gauss,hB,hL,fun l hl => (hL l hl).coprime_iff_not_dvd.mpr (ha l hl)⟩⟩

namespace DyadicCoefficientTower

variable {D : DyadicAxisPacking GaussianRationals η n B} {L : Finset ℕ} (T : DyadicCoefficientTower D L)

/-- The coefficient order acts on every jet in both endpoints of the deformation. -/
abbrev Order := AdjoinRoot T.modulus

theorem degree_pos : 0 < listCyclotomicDegree GaussianRationals D.pool B := by
  let : NeZero D.rootOrder := ⟨D.rootOrder_pos.ne'⟩
  let : FiniteDimensional GaussianRationals (CyclotomicField D.rootOrder GaussianRationals) :=
    IsCyclotomicExtension.finite_of_singleton D.rootOrder GaussianRationals _
  exact Module.finrank_pos (R := GaussianRationals) (M := CyclotomicField D.rootOrder GaussianRationals)

theorem order_dvd_orderTimesVolume : D.rootOrder ∣ D.orderTimesVolume :=
  dvd_mul_right D.rootOrder _

private theorem unit_cast {k : ℕ} (hk : k ∣ D.orderTimesVolume) :
    IsUnit (k : T.Order) := by
  exact protectedGaussian_isUnit_cast T.modulus (RingHom.id _) (Nat.pos_of_dvd_of_pos hk D.orderTimesVolume_pos)
    (fun l hl => (T.protected_coprime l hl).coprime_dvd_right hk)

/-- All transform divisors and their Fourier nodes work over every algebra receiving the order. -/
theorem transform_nodes {k : ℕ} (hk : k ∣ D.rootOrder) {A : Type*} [CommRing A] (f : T.Order →+* A) :
    IsUnit (k : A) ∧ ∃ u : Aˣ, (u : A) = f (AdjoinRoot.root T.modulus)^(D.rootOrder/k) ∧
      u^k = 1 ∧ ∀ i j : Fin k, i ≠ j → IsUnit ((u : A)^i.val - (u : A)^j.val) := by
  let := T.domain
  have hdiv : D.rootOrder ∣ D.orderTimesVolume := order_dvd_orderTimesVolume
  exact ⟨by simpa using (T.unit_cast (hk.trans hdiv)).map f,
    protectedGaussian_axisRoot D.rootOrder_pos T.primitive
      (fun l hl => (T.protected_coprime l hl).coprime_dvd_right hdiv) hk f⟩

theorem axis_unit {p : ℕ} (hp : p ∈ D.packing.axes) {A : Type*} [CommRing A] (f : T.Order →+* A) :
    IsUnit (p : A) := by
  have hd := Finset.dvd_prod_of_mem (fun q : ℕ => q) hp
  simpa using (T.unit_cast (hd.trans (dvd_mul_left _ D.rootOrder))).map f

/-- A divisor root retains exact order after specialization, including in
every residue field of the truncated jet algebra. -/
theorem primitive_map {k : ℕ} (hk : k ∣ D.rootOrder) {A : Type*} [CommRing A] [Nontrivial A]
    (f : T.Order →+* A) : IsPrimitiveRoot (f (AdjoinRoot.root T.modulus)^(D.rootOrder/k)) k := by
  let := T.domain
  have hM := T.unit_cast (order_dvd_orderTimesVolume (D := D))
  exact (primitiveRoot_map_of_unit_order f T.primitive hM).pow D.rootOrder_pos
    (Nat.div_mul_cancel hk).symm

include T in
/-- Zero, the positive frequencies, and the inverse transform share these nodes
at the rounded binary workspace sizes. -/
theorem padded_dvd {t : ℕ} (ht : t ≤ 4*B) : 2^Nat.clog 2 t ∣ D.rootOrder := by
  apply D.binaryPower_dvd
  cases he : Nat.clog 2 t with
  | zero => simp; have := T.width; omega
  | succ k =>
    have hp := Nat.pow_lt_of_lt_clog (by omega : k < Nat.clog 2 t)
    rw [pow_succ]
    omega

/-- The primitive eighth root used by the binary word squares to the specified Gaussian unit. -/
theorem eighthRoot :
    IsPrimitiveRoot ((AdjoinRoot.root T.modulus)^(D.rootOrder/8)) 8 ∧
      ((AdjoinRoot.root T.modulus)^(D.rootOrder/8))^2 =
        algebraMap _ T.Order (protectedGaussianI L) := by
  have hd : 8 ∣ D.rootOrder := D.binaryPower_dvd (k := 3) (by have := T.width; norm_num; omega)
  refine ⟨T.primitive.pow D.rootOrder_pos (Nat.div_mul_cancel hd).symm, ?_⟩
  rw [← pow_mul, ← T.gaussian]
  congr 1
  omega

theorem two_unit {A : Type*} [CommRing A] (f : T.Order →+* A) : IsUnit (2 : A) := by
  have hd := D.binaryPower_dvd (k := 1) (by have := T.width; norm_num; omega)
  simpa using (T.transform_nodes hd f).1

theorem semilocal : Finite (MaximalSpectrum T.Order) :=
  protectedGaussian_presentation_semilocal L T.protected_prime T.monic

theorem jet_semilocal (h : ℕ) : Finite (MaximalSpectrum (JetQuotient T.modulus h)) :=
  protectedGaussian_jet_semilocal L T.protected_prime T.monic h

theorem split (x : T.Order) : ∃ t : T.Order, IsUnit t ∧ IsUnit (x-t) := by
  let := T.semilocal
  exact exists_unit_split (T.two_unit (RingHom.id _)) x

theorem jet_split (h : ℕ) (x : JetQuotient T.modulus h) :
    ∃ t : JetQuotient T.modulus h, IsUnit t ∧ IsUnit (x-t) := by
  let := T.jet_semilocal h
  exact exists_unit_split (T.two_unit (algebraMap T.Order (JetQuotient T.modulus h))) x

/-- The two rational components of a Gaussian coefficient are unique and exhaustive. -/
theorem protectedGaussian_coordinates (L : Finset ℕ) :
    Function.Bijective (fun t : Fin 2 → protectedRationals L =>
      algebraMap _ (protectedGaussian L) (t 0) + protectedGaussianI L * algebraMap _ _ (t 1)) := by
  refine ⟨protectedGaussian_coord_injective L, fun s => ?_⟩
  obtain ⟨a,b,h⟩ := protectedGaussian_span L s
  exact ⟨![a,b],h⟩

theorem jets {h : ℕ} (hh : 0 < h) :
    JetCircuitsOver (algebraMap (protectedRationals L) (protectedGaussian L)) (protectedGaussianI L)
      T.modulus (listCyclotomicDegree GaussianRationals D.pool B) h :=
  protectedGaussian_jet_circuits L degree_pos hh T.modulus T.monic T.degree_eq

end DyadicCoefficientTower
end

end FiniteFourier
end LinearAlgebra
end OAI
