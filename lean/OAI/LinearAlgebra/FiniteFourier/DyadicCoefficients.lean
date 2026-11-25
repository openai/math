import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetCyclotomic
import OAI.LinearAlgebra.FiniteFourier.ProtectedCyclotomic
import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionCyclotomicNodes
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-! # The protected Gaussian cyclotomic coefficient tower

The relative minimal polynomial of a primitive root of unity over the
Gaussian rationals has Gaussian integer coefficients. Extending those
coefficients to the protected Gaussian order gives a monic presentation of
the same degree, embedded in the original cyclotomic field.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

noncomputable section

/-- The field used to fix each dyadic list's relative cyclotomic degree. -/
abbrev GaussianRationals := FractionRing GaussianInt

/-- The standard Gaussian unit in the rational head field. -/
def gaussianI : GaussianRationals := algebraMap GaussianInt _ Zsqrtd.sqrtd

theorem gaussianI_sq : gaussianI ^ 2 = -1 := by
  simp [gaussianI, pow_two, ← map_mul, Zsqrtd.dmuld]

/-- The Gaussian order over the rationals avoiding the denominator primes in `L`. -/
def protectedGaussian (L : Finset ℕ) : Subalgebra (protectedRationals L) GaussianRationals :=
  Algebra.adjoin _ {gaussianI}

/-- The Gaussian coordinate in the protected order. -/
def protectedGaussianI (L : Finset ℕ) : protectedGaussian L :=
  ⟨gaussianI, Algebra.subset_adjoin (Set.mem_singleton _)⟩

theorem protectedGaussianI_sq (L : Finset ℕ) : protectedGaussianI L ^ 2 = -1 :=
  Subtype.ext gaussianI_sq

/-- Every protected Gaussian coefficient is represented by a pair of protected rationals. -/
theorem protectedGaussian_span (L : Finset ℕ) (s : protectedGaussian L) :
    ∃ a b : protectedRationals L, algebraMap _ _ a + protectedGaussianI L * algebraMap _ _ b = s := by
  let φ := algebraMap (protectedRationals L) GaussianRationals
  have H (x : GaussianRationals) (hx : x ∈ protectedGaussian L) :
      ∃ a b, φ a + gaussianI * φ b = x := by
    refine Algebra.adjoin_induction (p := fun x _ => ∃ a b, φ a + gaussianI * φ b = x)
      ?_ ?_ ?_ ?_ hx
    · rintro _ rfl
      exact ⟨0, 1, by simp⟩
    · intro r
      exact ⟨r, 0, by simp [φ]⟩
    · rintro _ _ _ _ ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
      exact ⟨a+c,b+d,by simp only [map_add]; ring⟩
    · rintro _ _ _ _ ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
      exact ⟨a*c-b*d,a*d+b*c,by
        simp only [map_sub, map_mul, map_add]
        linear_combination -(φ b * φ d) * gaussianI_sq⟩
  obtain ⟨a,b,h⟩ := H s s.property
  exact ⟨a,b,Subtype.ext h⟩

/-- Real and imaginary coordinates in the protected Gaussian order are unique. -/
theorem protectedGaussian_coord_injective (L : Finset ℕ) :
    Function.Injective (fun u : Fin 2 → protectedRationals L =>
      algebraMap _ (protectedGaussian L) (u 0) + protectedGaussianI L * algebraMap _ _ (u 1)) := by
  intro x y h
  let φ := algebraMap ℚ GaussianRationals
  let a : ℚ := (x 0 : ℚ) - y 0
  let b : ℚ := (x 1 : ℚ) - y 1
  have he : φ a + gaussianI * φ b = 0 := by
    have H := congrArg Subtype.val h
    change φ (x 0) + gaussianI * φ (x 1) = φ (y 0) + gaussianI * φ (y 1) at H
    dsimp only [a, b]
    simp only [map_sub]
    linear_combination H
  have hs : a^2 + b^2 = 0 := by
    apply φ.injective
    simp only [map_add, map_pow, map_zero]
    linear_combination (φ a - gaussianI * φ b) * he + (φ b)^2 * gaussianI_sq
  have ha : a = 0 := by nlinarith [sq_nonneg b]
  have hb : b = 0 := by nlinarith [sq_nonneg a]
  funext j
  fin_cases j
  · exact Subtype.ext (sub_eq_zero.mp ha)
  · exact Subtype.ext (sub_eq_zero.mp hb)

/-- Gaussian integers have coefficients in every protected Gaussian order. -/
def gaussianIntegerToProtected (L : Finset ℕ) : GaussianInt →+* protectedGaussian L :=
  Zsqrtd.lift ⟨protectedGaussianI L, by simpa [pow_two] using protectedGaussianI_sq L⟩

theorem gaussianIntegerToProtected_comp (L : Finset ℕ) :
    (protectedGaussian L).val.toRingHom.comp (gaussianIntegerToProtected L) =
      algebraMap GaussianInt GaussianRationals := by
  apply Zsqrtd.hom_ext
  simp [gaussianIntegerToProtected, protectedGaussianI, gaussianI]

/-- The root can be oriented so its fourth-root power is the specified Gaussian unit. -/
theorem exists_primitiveRoot_over_gaussian {M : ℕ} [NeZero M] (h₄ : 4 ∣ M) :
    ∃ ξ : CyclotomicField M GaussianRationals, IsPrimitiveRoot ξ M ∧
      ξ ^ (M/4) = algebraMap GaussianRationals _ gaussianI := by
  let F := GaussianRationals
  let K := CyclotomicField M GaussianRationals
  obtain ⟨ξ, hξ⟩ : ∃ ξ : K, IsPrimitiveRoot ξ M := ⟨_, IsCyclotomicExtension.zeta_spec M F K⟩
  have h₀ := NeZero.pos M
  have hξ₄ : IsPrimitiveRoot (ξ^(M/4)) 4 := hξ.pow h₀ (Nat.div_mul_cancel h₄).symm
  have hs : (ξ^(M/4))^2 = -1 := (hξ₄.pow (by decide) (by decide : 4 = 2*2)).eq_neg_one_of_two_right
  let i := algebraMap F K gaussianI
  have hi : i^2 = -1 := by
    dsimp only [i, F]
    rw [← map_pow, gaussianI_sq, map_neg, map_one]
  obtain h | h := sq_eq_sq_iff_eq_or_eq_neg.mp (hs.trans hi.symm)
  · exact ⟨ξ,hξ,h⟩
  · refine ⟨ξ⁻¹,hξ.inv, ?_⟩
    change (ξ⁻¹)^(M/4) = i
    rw [inv_pow, h]
    apply inv_eq_of_mul_eq_one_right
    linear_combination -hi

/-- The monic presentation cut out over the protected Gaussian order. -/
def protectedGaussianModulus (L : Finset ℕ) {M : ℕ} (ξ : CyclotomicField M GaussianRationals) :
    (protectedGaussian L)[X] :=
  (minpoly GaussianInt ξ).map (gaussianIntegerToProtected L)

theorem protectedGaussianModulus_map (L : Finset ℕ) {M : ℕ} [NeZero M]
    {ξ : CyclotomicField M GaussianRationals} (hξ : IsPrimitiveRoot ξ M) :
    (protectedGaussianModulus L ξ).map (protectedGaussian L).val.toRingHom =
      minpoly GaussianRationals ξ := by
  rw [protectedGaussianModulus, map_map, gaussianIntegerToProtected_comp]
  exact (minpoly.isIntegrallyClosed_eq_field_fractions' _ (IsIntegral.of_pow (NeZero.pos M) (hξ.pow_eq_one ▸ isIntegral_one))).symm

theorem protectedGaussianModulus_monic (L : Finset ℕ) {M : ℕ} [NeZero M]
    {ξ : CyclotomicField M GaussianRationals} (hξ : IsPrimitiveRoot ξ M) :
    (protectedGaussianModulus L ξ).Monic :=
  (minpoly.monic (A := GaussianInt) (IsIntegral.of_pow (NeZero.pos M) (hξ.pow_eq_one ▸ isIntegral_one))).map _

theorem protectedGaussianModulus_natDegree (L : Finset ℕ) {M : ℕ} [NeZero M]
    {ξ : CyclotomicField M GaussianRationals} (hξ : IsPrimitiveRoot ξ M) :
    (protectedGaussianModulus L ξ).natDegree =
      Module.finrank GaussianRationals (CyclotomicField M GaussianRationals) := by
  rw [← (protectedGaussianModulus_monic L hξ).natDegree_map (protectedGaussian L).val.toRingHom,
    protectedGaussianModulus_map L hξ, ← hξ.powerBasis_dim GaussianRationals]
  exact (hξ.powerBasis GaussianRationals).finrank.symm

/-- Embedding the relative monic presentation in the cyclotomic field. -/
theorem exists_protectedGaussian_embedding (L : Finset ℕ) {M : ℕ} [NeZero M]
    {ξ : CyclotomicField M GaussianRationals} (hξ : IsPrimitiveRoot ξ M) :
    let m := protectedGaussianModulus L ξ
    ∃ f : AdjoinRoot m →+* CyclotomicField M GaussianRationals,
      Function.Injective f ∧ f (AdjoinRoot.root m) = ξ ∧
      f.comp (algebraMap (protectedGaussian L) (AdjoinRoot m)) =
        (algebraMap GaussianRationals _).comp (protectedGaussian L).val.toRingHom := by
  intro m
  let K := CyclotomicField M GaussianRationals
  let ι := (protectedGaussian L).val.toRingHom
  let φ := (algebraMap GaussianRationals K).comp ι
  have hm : m.map ι = minpoly GaussianRationals ξ := protectedGaussianModulus_map L hξ
  have heval (q : (protectedGaussian L)[X]) : q.eval₂ φ ξ = aeval ξ (q.map ι) := by
    rw [aeval_def, eval₂_map]
  have hz : m.eval₂ φ ξ = 0 := by rw [heval, hm, minpoly.aeval]
  let f := AdjoinRoot.lift φ ξ hz
  refine ⟨f, ?_, AdjoinRoot.lift_root .., AdjoinRoot.lift_comp_of ..⟩
  apply (injective_iff_map_eq_zero f).mpr
  intro x hx
  obtain ⟨q,rfl⟩ := AdjoinRoot.mk_surjective x
  change AdjoinRoot.lift φ ξ hz (AdjoinRoot.mk m q) = 0 at hx
  rw [AdjoinRoot.lift_mk, heval] at hx
  apply AdjoinRoot.mk_eq_zero.mpr
  apply (map_dvd_map ι (Subtype.coe_injective) (protectedGaussianModulus_monic L hξ)).mp
  rw [hm]
  exact minpoly.dvd _ _ hx

/-- Each dyadic list admits a relative presentation at its prescribed degree,
with a primitive root reducing to the specified fourth root in the Gaussian subring. -/
theorem exists_protectedGaussian_presentation (L : Finset ℕ) {M : ℕ} [NeZero M] (h₄ : 4 ∣ M) :
    ∃ m : (protectedGaussian L)[X], m.Monic ∧
      m.natDegree = Module.finrank GaussianRationals (CyclotomicField M GaussianRationals) ∧
      IsDomain (AdjoinRoot m) ∧ IsPrimitiveRoot (AdjoinRoot.root m) M ∧
      AdjoinRoot.root m ^ (M/4) = algebraMap _ (AdjoinRoot m) (protectedGaussianI L) := by
  obtain ⟨ξ,hξ,h₄ξ⟩ := exists_primitiveRoot_over_gaussian h₄
  let m := protectedGaussianModulus L ξ
  obtain ⟨f,hinj,hf,hcomp⟩ := exists_protectedGaussian_embedding L hξ
  refine ⟨m,protectedGaussianModulus_monic L hξ, protectedGaussianModulus_natDegree L hξ,
    hinj.isDomain f, IsPrimitiveRoot.of_map_of_injective (f := f) (ζ := AdjoinRoot.root m) (by rw [hf]; exact hξ) hinj, hinj ?_⟩
  rw [map_pow, hf, h₄ξ]
  exact (RingHom.congr_fun hcomp (protectedGaussianI L)).symm

/-- All rings in the protected coefficient tower are semilocal. -/
theorem protectedGaussian_presentation_semilocal (L : Finset ℕ) (hL : ∀ p ∈ L, p.Prime)
    {m : (protectedGaussian L)[X]} (hm : m.Monic) : Finite (MaximalSpectrum (AdjoinRoot m)) := by
  let := finite_maximalSpectrum_protectedRationals hL
  have h₄ : gaussianI^4 = 1 := by rw [show 4 = 2*2 by decide, pow_mul, gaussianI_sq]; norm_num
  let : Finite (MaximalSpectrum (protectedGaussian L)) :=
    finite_maximalSpectrum_adjoin_root (protectedRationals L) (by decide : 0 < 4) h₄
  let := hm.finite_adjoinRoot
  exact finite_maximalSpectrum_of_finite_algebra (protectedGaussian L) _

/-- Jet multiplication over the protected Gaussian coefficient tower reduces to
three identical length-`2eh` products over the protected rational base. -/
theorem protectedGaussian_jet_circuits (L : Finset ℕ) {e h : ℕ} (he : 0 < e) (hh : 0 < h)
    (m : (protectedGaussian L)[X]) (hm : m.Monic) (hd : m.natDegree = e) :
    JetCircuitsOver (algebraMap (protectedRationals L) (protectedGaussian L))
      (protectedGaussianI L) m e h :=
  exists_jetProduct_circuits_over _ _ (-1) 0 (by simp [protectedGaussianI_sq])
    (protectedGaussian_span L) he hh hm hd

/-- A positive integer avoiding all excluded primes is invertible throughout
the coefficient tower, including in jets of any length. -/
theorem protectedGaussian_isUnit_cast {L : Finset ℕ} (m : (protectedGaussian L)[X])
    {A : Type*} [CommRing A] (f : AdjoinRoot m →+* A)
    {k : ℕ} (hk : 0 < k) (hc : ∀ p ∈ L, p.Coprime k) : IsUnit (k : A) := by
  let φ := (f.comp (algebraMap _ (AdjoinRoot m))).comp (algebraMap (protectedRationals L) (protectedGaussian L))
  simpa using (isUnit_natCast_protectedRationals hk.ne' hc).map φ

/-- For a divisor of the common root order, the same Fourier nodes have
pairwise unit differences in the coefficient order and in every jet algebra. -/
theorem protectedGaussian_axisRoot {L : Finset ℕ} {m : (protectedGaussian L)[X]}
    [IsDomain (AdjoinRoot m)] {M k : ℕ} (hM : 0 < M) (hξ : IsPrimitiveRoot (AdjoinRoot.root m) M)
    (hc : ∀ p ∈ L, p.Coprime M) (hk : k ∣ M) {A : Type*} [CommRing A] (f : AdjoinRoot m →+* A) :
    ∃ u : Aˣ, (u : A) = f (AdjoinRoot.root m)^(M/k) ∧ u^k = 1 ∧
      ∀ i j : Fin k, i ≠ j → IsUnit ((u : A)^i.val - (u : A)^j.val) := by
  have hz : (cyclotomic M A).IsRoot (f (AdjoinRoot.root m)) := by
    change (cyclotomic M A).eval (f _) = 0
    rw [cyclotomic.eval_apply, (hξ.isRoot_cyclotomic hM).eq_zero, map_zero]
  obtain ⟨hpow,hs⟩ := Deformation.cyclotomicNodePowers hz hM (protectedGaussian_isUnit_cast m f hM hc) hk
  obtain ⟨u,hu⟩ := IsUnit.of_pow_eq_one hpow (Nat.pos_of_dvd_of_pos hk hM).ne'
  exact ⟨u,hu,Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_one, hu] using hpow),
    by simpa only [hu] using hs⟩

/-- Semilocality is preserved upon passing from the coefficient order to truncated jets. -/
theorem protectedGaussian_jet_semilocal (L : Finset ℕ) (hL : ∀ p ∈ L, p.Prime)
    {m : (protectedGaussian L)[X]} (hm : m.Monic) (h : ℕ) :
    Finite (MaximalSpectrum (JetQuotient m h)) := by
  let := protectedGaussian_presentation_semilocal L hL hm
  let := (monic_X_pow (R := AdjoinRoot m) h).finite_adjoinRoot
  exact finite_maximalSpectrum_of_finite_algebra (AdjoinRoot m) (JetQuotient m h)

end

end FiniteFourier
end LinearAlgebra
end OAI
