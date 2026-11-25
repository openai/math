import OAI.Computability.BorderVNP.CoverHeckeDenominators
import OAI.Computability.BorderVNP.CoverHeckeCorrespondenceHaar

/-!
# Degree of the maps between congruence levels

A fixed denominator motion loses twice its denominator exponent in depth.
Conjugation in the opposite direction also has this loss, so the image
contains a still deeper principal congruence subgroup. Its index is bounded
independently of the starting depth.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open BorderVNP.Hecke

private theorem gamma_add_le (d k : ℕ) : gamma (d+k) ≤ gamma d := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (gamma_next _).trans ih

private theorem gamma_index (d k : ℕ) :
    (gamma (d+2+k)).relIndex (gamma (d+2)) = (7^3)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show d+2+(k+1) = d+2+k+1 by omega]
    rw [← Subgroup.relIndex_mul_relIndex _ (gamma (d+2+k)) _ (gamma_next _) (gamma_add_le _ _)]
    have h := layer_relIndex (d+k)
    have h₁ : d+k+3 = d+2+k+1 := by omega
    have h₂ : d+k+2 = d+2+k := by omega
    rw [h₁,h₂] at h
    rw [h,ih,pow_succ' (7^3) k]

/-- Exact relative index of the represented congruence subgroups in the stable range. -/
theorem lattice_index (d k : ℕ) :
    (lattice (d+2+k)).relIndex (lattice (d+2)) = (7^3)^k := by
  let e := MonoidHom.ofInjective (gammaSL_injective (d+2))
  let S := (gamma (d+2+k)).subgroupOf (gamma (d+2))
  have hm : S.map e.toMonoidHom = (lattice (d+2+k)).subgroupOf (lattice (d+2)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y.val,hy⟩,rfl⟩
    · rintro ⟨y, hy⟩
      let t : gamma (d+2) := ⟨y.val, gamma_add_le _ _ y.property⟩
      exact ⟨t,y.property,Subtype.ext hy⟩
  change ((lattice (d+2+k)).subgroupOf (lattice (d+2))).index = _
  rw [← hm]
  exact (Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective S).trans (gamma_index d k)

/-- The image of the lattice for a motion whose input cover is at depth `l+2a`. -/
noncomputable def movedLattice (g : SL) (d : ℕ) : Subgroup SL :=
  (lattice d).map (MulAut.conj g).toMonoidHom

/-- The moved lattice is sandwiched between two principal levels separated by `4a`. -/
theorem movedLattice_bounds {g : SL} {a : ℕ} (hg : Clears g a) (l : ℕ) :
    lattice (l+4*a) ≤ movedLattice g (l+2*a) ∧ movedLattice g (l+2*a) ≤ lattice l := by
  constructor
  · intro x hx
    have hx' : x ∈ lattice (l+2*a+2*a) := by rwa [show l+2*a+2*a = l+4*a by omega]
    refine ⟨g⁻¹*x*g, ?_, ?_⟩
    · simpa using conjugate_lattice hg.inv (l+2*a) hx'
    · change g*(g⁻¹*x*g)*g⁻¹ = x
      simp [mul_assoc]
  · rintro _ ⟨x,hx,rfl⟩
    exact conjugate_lattice hg l hx

/-- The covering index is positive and bounded by a function of the denominator alone. -/
theorem movedLattice_index_bounds {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ) :
    0 < (movedLattice g (d+2+2*a)).relIndex (lattice (d+2)) ∧
    (movedLattice g (d+2+2*a)).relIndex (lattice (d+2)) ≤ (7^3)^(4*a) := by
  have hdiv := Subgroup.relIndex_dvd_of_le_left (lattice (d+2)) (movedLattice_bounds hg (d+2)).1
  rw [lattice_index] at hdiv
  have hpos : 0 < (7^3 : ℕ)^(4*a) := by positivity
  exact ⟨Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hpos.ne' hdiv), Nat.le_of_dvd hpos hdiv⟩

/-- The normalized frame at the deeper level is sent to the shallower one by left
multiplication by the motion. The conjugation estimate proves well-definedness. -/
noncomputable def descend {g : SL} {a : ℕ} (hg : Clears g a) (l : ℕ) :
    Cosets (lattice (l+2*a)) → Cosets (lattice l) :=
  Quotient.map (g * ·) fun x y h => QuotientGroup.rightRel_apply.mpr (by
    have hi := conjugate_lattice hg l (QuotientGroup.rightRel_apply.mp h)
    simpa [mul_assoc] using hi)

/-- Every frame on the shallower cover has a preimage on the deeper cover. -/
theorem descend_surjective {g : SL} {a : ℕ} (hg : Clears g a) (l : ℕ) :
    Function.Surjective (descend hg l) := by
  rintro ⟨x⟩
  exact ⟨coset _ (g⁻¹*x), by change coset _ (g*(g⁻¹*x)) = coset _ x; rw [mul_inv_cancel_left]⟩

private theorem map_relIndex_dvd {G Q : Type*} [Group G] [Group Q] (p : G →* Q)
    {A B : Subgroup G} (hAB : A ≤ B) :
    (A.map p).relIndex (B.map p) ∣ A.relIndex B := by
  have he : (A.map p).subgroupOf (B.map p) = (A.subgroupOf B).map (p.subgroupMap B) := by
    ext x
    constructor
    · rintro ⟨y,hy,h⟩
      exact ⟨⟨y,hAB hy⟩,hy,Subtype.ext h⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.val,hy,rfl⟩
  rw [Subgroup.relIndex, he]
  exact Subgroup.index_map_dvd _ (p.subgroupMap_surjective B)

/-- In the projective frame group the covering index is also positive and bounded
independently of the base depth. -/
theorem projective_index_bounds {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ) :
    let D := ((movedLattice g (d+2+2*a)).map project).relIndex ((lattice (d+2)).map project)
    0 < D ∧ D ≤ (7^3)^(4*a) := by
  have hdiv := map_relIndex_dvd project (movedLattice_bounds hg (d+2)).2
  have hb := movedLattice_index_bounds hg d
  exact ⟨Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hb.1.ne' hdiv),
    (Nat.le_of_dvd hb.1 hdiv).trans hb.2⟩

/-- Left multiplication gives the frame map between the actual projective covers. -/
noncomputable def projectiveDescend {g : SL} {a : ℕ} (hg : Clears g a) (l : ℕ) :
    Cosets ((lattice (l+2*a)).map project) → Cosets ((lattice l).map project) :=
  Quotient.map (project g * ·) fun x y h => QuotientGroup.rightRel_apply.mpr (by
    obtain ⟨v,hv,e⟩ := QuotientGroup.rightRel_apply.mp h
    refine ⟨g*v*g⁻¹,conjugate_lattice hg l hv,?_⟩
    simp [map_mul,e,mul_assoc])

end Cover.Frame

end BorderVNP
end Computability
end OAI
