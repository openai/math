import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Order.Module.Rat
import Mathlib.Analysis.Convex.Cone.Extension

/-!
# Separation by a rational-linear state

Appendix A.1 of *VP and VNP differ over every field* works with a rational cone
in the localized tensor algebra. For a vector `z` outside the cone, adjoining
`-z` preserves exclusion of the negative order unit. A positive extension from
the rational order-unit line to the whole space then has value at most zero at `z`.

The scalar coefficients of the linear maps are rational. Their values lie in
`ℝ`, where the supremum needed to choose a value in a new direction exists.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

open Set Submodule

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- Extend a positive rational-linear functional in one new direction. -/
theorem rational_extension_step (s : PointedCone ℚ E) (f : E →ₗ.[ℚ] ℝ)
    (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) (hdom : f.domain ≠ ⊤) :
    ∃ g, f < g ∧ ∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x := by
  obtain ⟨y, _, hy⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hdom)
  let lows : Set ℝ := {u | ∃ a : f.domain, (a : E) + y ∈ s ∧ u = -f a}
  have compat (a b : f.domain) (ha : (a : E) + y ∈ s) (hb : (b : E) - y ∈ s) :
      -f a ≤ f b := by
    have hab : ((a + b : f.domain) : E) ∈ s := by
      have h := s.add_mem ha hb
      rw [sub_eq_add_neg, add_add_add_comm, add_neg_cancel, add_zero] at h
      exact h
    exact neg_le_iff_add_nonneg.mpr (by simpa only [f.map_add, add_comm] using nonneg _ hab)
  have upper (b : f.domain) (hb : (b : E) - y ∈ s) : f b ∈ upperBounds lows := by
    rintro _ ⟨a, ha, rfl⟩
    exact compat a b ha hb
  obtain ⟨b, hb⟩ := dense (-y)
  have bound : BddAbove lows := ⟨f b, upper b (by simpa only [sub_eq_add_neg] using hb)⟩
  obtain ⟨a, ha⟩ := dense y
  have inhabited : lows.Nonempty := ⟨-f a, a, ha, rfl⟩
  let c := sSup lows
  have lower_value (x : f.domain) (hx : (x : E) + y ∈ s) : 0 ≤ f x + c :=
    neg_le_iff_add_nonneg'.mp (le_csSup bound ⟨x, hx, rfl⟩)
  have upper_value (x : f.domain) (hx : (x : E) - y ∈ s) : 0 ≤ f x - c :=
    sub_nonneg.mpr (csSup_le inhabited (upper x hx))
  refine ⟨f.supSpanSingleton y c hy, lt_of_le_of_ne (f.left_le_sup _ _) ?_, ?_⟩
  · intro heq
    apply hy
    rw [heq, LinearPMap.domain_supSpanSingleton]
    exact mem_sup_right (mem_span_singleton_self _)
  · rintro ⟨z, hz⟩ hcone
    obtain ⟨x, hx, z', hz', rfl⟩ := mem_sup.mp hz
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hz'
    change x + r • y ∈ s at hcone
    rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ _ _ hx, RingHom.id_apply]
    let u : f.domain := ⟨x, hx⟩
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · let t := -r
      have ht : 0 < t := neg_pos.mpr hr
      have ht' : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
      have hnorm : ((t⁻¹ • u : f.domain) : E) - y ∈ s := by
        apply (s.smul_mem_iff ht).mp
        simpa only [Submodule.coe_smul, smul_sub, smul_smul, ht', one_smul, t, neg_smul,
          sub_neg_eq_add] using hcone
      have hval := smul_nonneg ht.le (upper_value (t⁻¹ • u) hnorm)
      simpa only [smul_sub, f.map_smul, RingHom.id_apply, smul_smul, ht', one_smul, t, neg_smul,
        sub_neg_eq_add] using hval
    · simpa only [zero_smul, add_zero] using
        (nonneg u (by simpa only [zero_smul, add_zero] using hcone))
    · have hr' : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
      have hnorm : ((r⁻¹ • u : f.domain) : E) + y ∈ s := by
        apply (s.smul_mem_iff hr).mp
        simpa only [Submodule.coe_smul, smul_add, smul_smul, hr', one_smul] using hcone
      have hval := smul_nonneg hr.le (lower_value (r⁻¹ • u) hnorm)
      simpa only [smul_add, f.map_smul, RingHom.id_apply, smul_smul, hr', one_smul] using hval

/-- An increasing chain of positive partial functionals is positive on the union
of its domains. -/
private theorem chain_positive (P : PointedCone ℚ E) (c : Set (E →ₗ.[ℚ] ℝ))
    (hne : c.Nonempty) (hc : DirectedOn (· ≤ ·) c)
    (hpos : ∀ p ∈ c, ∀ x : p.domain, (x : E) ∈ P → 0 ≤ p x) :
    ∀ x : (LinearPMap.sSup c hc).domain, (x : E) ∈ P → 0 ≤ LinearPMap.sSup c hc x := by
  rintro ⟨x, hx⟩ hPx
  obtain ⟨p, hpc, hpx⟩ := (LinearPMap.mem_domain_sSup_iff hne hc).mp hx
  rw [LinearPMap.sSup_apply hc hpc ⟨x, hpx⟩]
  exact hpos p hpc ⟨x, hpx⟩ hPx

/-- A real-valued positive functional on a rational subspace extends whenever
the subspace contains a translate of every vector into the cone. -/
theorem rational_riesz_extension (P : PointedCone ℚ E) (p : E →ₗ.[ℚ] ℝ)
    (hp : ∀ x : p.domain, (x : E) ∈ P → 0 ≤ p x)
    (hdense : ∀ y : E, ∃ x : p.domain, (x : E) + y ∈ P) :
    ∃ f : E →ₗ[ℚ] ℝ, (∀ x : p.domain, f x = p x) ∧ ∀ x ∈ P, 0 ≤ f x := by
  let positive := {q : E →ₗ.[ℚ] ℝ | ∀ x : q.domain, (x : E) ∈ P → 0 ≤ q x}
  have hub : ∀ c ⊆ positive, IsChain (· ≤ ·) c → ∀ q ∈ c,
      ∃ b ∈ positive, ∀ r ∈ c, r ≤ b := by
    intro c hsub hchain q hqc
    refine ⟨LinearPMap.sSup c hchain.directedOn, ?_, fun _ hr => LinearPMap.le_sSup _ hr⟩
    exact chain_positive P c ⟨q, hqc⟩ hchain.directedOn fun _ hr => hsub hr
  obtain ⟨q, hpq, hq, hmax⟩ := zorn_le_nonempty₀ positive hub p hp
  have htop : q.domain = ⊤ := by
    by_contra hproper
    have hcofinal (y : E) : ∃ x : q.domain, (x : E) + y ∈ P := by
      obtain ⟨x, hx⟩ := hdense y
      exact ⟨⟨x, hpq.1 x.property⟩, hx⟩
    obtain ⟨r, hqr, hr⟩ := rational_extension_step P q hq hcofinal hproper
    exact hqr.not_ge (hmax hr hqr.le)
  let inc : E →ₗ[ℚ] q.domain := LinearMap.id.codRestrict q.domain (fun x => htop ▸ trivial)
  refine ⟨q.toFun.comp inc, ?_, ?_⟩
  · intro x
    exact (hpq.2 (y := inc (x : E)) rfl).symm
  · intro x hx
    exact hq (inc x) hx

/-- The cone obtained by adjoining the ray generated by `-z` to `P`. -/
def augmentCone (P : PointedCone ℚ E) (z : E) : PointedCone ℚ E :=
  P ⊔ PointedCone.hull ℚ {-z}

theorem le_augmentCone (P : PointedCone ℚ E) (z : E) : P ≤ augmentCone P z :=
  le_sup_left

theorem neg_mem_augmentCone (P : PointedCone ℚ E) (z : E) : -z ∈ augmentCone P z :=
  (show PointedCone.hull ℚ {-z} ≤ augmentCone P z from le_sup_right)
    (PointedCone.subset_hull (Set.mem_singleton (-z)))

theorem mem_augmentCone_iff {P : PointedCone ℚ E} {z x : E} :
    x ∈ augmentCone P z ↔ ∃ p ∈ P, ∃ r : ℚ, 0 ≤ r ∧ p - r • z = x := by
  rw [augmentCone, Submodule.mem_sup]
  constructor
  · rintro ⟨p, hp, y, hy, h⟩
    obtain ⟨r, hr, rfl⟩ := PointedCone.mem_hull_singleton.mp hy
    exact ⟨p, hp, r, hr, by simpa [sub_eq_add_neg] using h⟩
  · rintro ⟨p, hp, r, hr, rfl⟩
    exact ⟨p, hp, r • (-z), PointedCone.mem_hull_singleton.mpr ⟨r, hr, rfl⟩,
      by simp [sub_eq_add_neg]⟩

/-- If `z` lies outside the cone, adjoining `-z` still excludes the negative order unit. -/
theorem neg_notMem_augmentCone {P : PointedCone ℚ E} {e z : E}
    (he : e ∈ P) (hne : -e ∉ P) (hz : z ∉ P) : -e ∉ augmentCone P z := by
  intro h
  obtain ⟨p, hp, r, hr, hrepr⟩ := mem_augmentCone_iff.mp h
  rcases eq_or_lt_of_le hr with hzero | hpos
  · subst r
    simp only [zero_smul, sub_zero] at hrepr
    exact hne (hrepr ▸ hp)
  · have hrz : r • z = p + e := by
      rw [sub_eq_iff_eq_add] at hrepr
      rw [hrepr]
      simp [add_comm]
    apply hz
    apply (PointedCone.smul_mem_iff P hpos).mp
    exact hrz ▸ P.add_mem hp he

/-- The functional on the order-unit line sends a rational multiple of the unit
to its coefficient. Cone positivity and the order-unit property make this line
a suitable initial domain for positive extension. -/
theorem exists_orderUnitLine (P : PointedCone ℚ E) (e : E)
    (hne : -e ∉ P) (horder : ∀ y : E, ∃ n : ℕ, n • e + y ∈ P) :
    ∃ f : E →ₗ.[ℚ] ℝ, ∃ he : e ∈ f.domain,
      f ⟨e, he⟩ = 1 ∧
      (∀ x : f.domain, (x : E) ∈ P → 0 ≤ f x) ∧
      ∀ y : E, ∃ x : f.domain, (x : E) + y ∈ P := by
  have h0 : e ≠ 0 := by
    rintro rfl
    exact hne (by simpa only [neg_zero] using P.zero_mem)
  let f : E →ₗ.[ℚ] ℝ := LinearPMap.mkSpanSingleton e 1 h0
  have he : e ∈ f.domain := Submodule.mem_span_singleton_self e
  refine ⟨f, he, LinearPMap.mkSpanSingleton_apply ℚ ℚ h0 1, ?_, ?_⟩
  · rintro ⟨x, hx⟩ hP
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hr : 0 ≤ r := by
      by_contra! hneg
      apply hne
      have hsc : 0 ≤ -r⁻¹ := neg_nonneg.mpr (inv_nonpos.mpr hneg.le)
      have hs := P.smul_mem hsc hP
      simpa [smul_smul, neg_mul, inv_mul_cancel₀ hneg.ne] using hs
    change 0 ≤ LinearPMap.mkSpanSingleton' e (1 : ℝ) _ ⟨r • e, hx⟩
    rw [LinearPMap.mkSpanSingleton'_apply, RingHom.id_apply, Rat.smul_def, mul_one]
    exact_mod_cast hr
  · intro y
    obtain ⟨n, hn⟩ := horder y
    exact ⟨⟨n • e, f.domain.nsmul_mem he n⟩, hn⟩

/-- A vector outside the rational order-unit cone admits a normalized
nonnegative functional whose value on the vector is at most zero. -/
theorem separate_order_unit (P : PointedCone ℚ E) (e z : E) (he : e ∈ P)
    (hneg : -e ∉ P) (horder : ∀ x : E, ∃ n : ℕ, n • e + x ∈ P) (hz : z ∉ P) :
    ∃ f : E →ₗ[ℚ] ℝ, f e = 1 ∧ (∀ x ∈ P, 0 ≤ f x) ∧ f z ≤ 0 := by
  let Q := augmentCone P z
  have hQneg : -e ∉ Q := neg_notMem_augmentCone he hneg hz
  have hQorder (x : E) : ∃ n : ℕ, n • e + x ∈ Q := by
    obtain ⟨n, hn⟩ := horder x
    exact ⟨n, le_augmentCone P z hn⟩
  obtain ⟨p, hep, hpone, hppos, hpdense⟩ := exists_orderUnitLine Q e hQneg hQorder
  obtain ⟨f, hfp, hfpos⟩ := rational_riesz_extension Q p hppos hpdense
  have hfe : f e = 1 := (hfp ⟨e, hep⟩).trans hpone
  refine ⟨f, hfe, fun x hx => hfpos x (le_augmentCone P z hx), ?_⟩
  simpa only [map_neg, neg_nonneg] using hfpos (-z) (neg_mem_augmentCone P z)

end Spectral

end VPVNP
end Computability
end OAI
