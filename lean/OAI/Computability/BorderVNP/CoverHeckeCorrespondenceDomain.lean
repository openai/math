import OAI.Computability.BorderVNP.CoverHeckeCorrespondence
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-!
# Fundamental domains for the two finite covering maps

Given a tile with boundary representatives already assigned as in §5.1, taking
one translated copy for each right coset gives a fundamental domain for the
smaller group. Conjugation gives the second domain in the Hecke correspondence.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Hecke

open Set MeasureTheory
open scoped Pointwise ENNReal

variable {G : Type*} [Group G] (Γ : Subgroup G)

/-- Boundary ties are resolved so that every orbit meets the chosen domain exactly once. -/
def ExactTile (D : Set G) : Prop := ∀ x : G, ∃! a : Γ, (a : G) * x ∈ D

/-- The domain for a subgroup is assembled from translates indexed by its right cosets. -/
noncomputable def expandedTile (S : Subgroup Γ) (D : Set G) : Set G :=
  ⋃ i : Cosets S, (i.out : G) • D

private theorem mem_expanded (S : Subgroup Γ) (D : Set G) (x : G) :
    x ∈ expandedTile Γ S D ↔ ∃ i : Cosets S, (i.out : G)⁻¹ * x ∈ D := by
  simp [expandedTile, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]

/-- The translates making up the expanded domain are disjoint as sets. -/
theorem disjoint_expandedTile (S : Subgroup Γ) {D : Set G} (hd : ExactTile Γ D) :
    Pairwise (fun i j : Cosets S => Disjoint ((i.out : G) • D) ((j.out : G) • D)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hi hj
  have e : i.out⁻¹ = j.out⁻¹ := (hd x).unique hi hj
  exact hij (Quotient.out_injective (inv_inj.mp e))

/-- The expanded domain has a unique representative for the action of the smaller group. -/
theorem exact_expandedTile (S : Subgroup Γ) {D : Set G} (hd : ExactTile Γ D) (x : G) :
    ∃! h : S, ((h : Γ) : G) * x ∈ expandedTile Γ S D := by
  obtain ⟨a, ha, hu⟩ := hd x
  let i := coset S a⁻¹
  have hi : i.out * a ∈ S := by
    have e : coset S a⁻¹ = coset S i.out := (Quotient.out_eq i).symm
    simpa using QuotientGroup.rightRel_apply.mp (Quotient.exact e)
  let h : S := ⟨i.out * a, hi⟩
  refine ⟨h, (mem_expanded Γ S D _).mpr ⟨i, ?_⟩, ?_⟩
  · change (i.out : G)⁻¹ * (((i.out : G) * a) * x) ∈ D
    simpa [mul_assoc] using ha
  · intro k hk
    obtain ⟨j, hj⟩ := (mem_expanded Γ S D _).mp hk
    have he : j.out⁻¹ * (k : Γ) = a := hu _ (by simpa [mul_assoc] using hj)
    have hkj : (k : Γ) = j.out * a := by rw [← he]; simp
    have hji : j = i := by
      rw [← Quotient.out_eq j]
      apply Eq.symm
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      simp [← hkj]
    apply Subtype.ext
    simpa [h, hji] using hkj

variable [MeasurableSpace G] [MeasurableMul₂ G]

/-- The expanded domain is Borel whenever the chosen tile is Borel. -/
theorem measurableSet_expandedTile (S : Subgroup Γ) [Countable (Cosets S)]
    {D : Set G} (hD : MeasurableSet D) : MeasurableSet (expandedTile Γ S D) :=
  MeasurableSet.iUnion fun _ => hD.const_smul _

/-- The expanded domain is a measure-theoretic fundamental domain. -/
theorem fundamental_expandedTile (S : Subgroup Γ) [Countable (Cosets S)] {D : Set G}
    (hD : MeasurableSet D) (hd : ExactTile Γ D) (μ : Measure G) :
    IsFundamentalDomain S (expandedTile Γ S D) μ :=
  IsFundamentalDomain.mk' (measurableSet_expandedTile Γ S hD).nullMeasurableSet
    (exact_expandedTile Γ S hd)

/-- Conjugation identifies the two intersection subgroups. -/
def conjugateIndex (z : G) : intersection Γ z ≃* intersection Γ z⁻¹ where
  toFun h := ⟨⟨z * ((h : Γ) : G) * z⁻¹, h.property⟩, by
    change z⁻¹ * (z * ((h : Γ) : G) * z⁻¹) * z⁻¹⁻¹ ∈ Γ
    simp [mul_assoc]⟩
  invFun h := ⟨⟨z⁻¹ * ((h : Γ) : G) * z, by
    have hp := h.property
    change z⁻¹ * ((h : Γ) : G) * z⁻¹⁻¹ ∈ Γ at hp
    rwa [inv_inv] at hp⟩, by
    change z * (z⁻¹ * ((h : Γ) : G) * z) * z⁻¹ ∈ Γ
    simp [mul_assoc]⟩
  left_inv h := by ext; change z⁻¹ * (z * _ * z⁻¹) * z = _; simp [mul_assoc]
  right_inv h := by ext; change z * (z⁻¹ * _ * z) * z⁻¹ = _; simp [mul_assoc]
  map_mul' a b := by ext; change z * (_ * _) * z⁻¹ = (z * _ * z⁻¹) * (z * _ * z⁻¹); simp [mul_assoc]

/-- Translating the domain by `z` turns a domain for `H` into one for `z H z⁻¹`. -/
theorem fundamental_translatedTile (z : G) [Countable (Cosets (intersection Γ z))]
    {D : Set G} (hD : MeasurableSet D) (hd : ExactTile Γ D) (μ : Measure G) :
    IsFundamentalDomain (intersection Γ z⁻¹) (z • expandedTile Γ (intersection Γ z) D) μ := by
  apply IsFundamentalDomain.mk' ((measurableSet_expandedTile Γ _ hD).const_smul z).nullMeasurableSet
  intro x
  obtain ⟨a, ha, hu⟩ := exact_expandedTile Γ (intersection Γ z) hd (z⁻¹ * x)
  let e := conjugateIndex Γ z
  have he (b : intersection Γ z) :
      e b • x ∈ z • expandedTile Γ (intersection Γ z) D ↔
        ((b : Γ) : G) * (z⁻¹ * x) ∈ expandedTile Γ (intersection Γ z) D := by
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change z⁻¹ * ((z * _ * z⁻¹) * x) ∈ _ ↔ _
    simp [mul_assoc]
  refine ⟨e a, (he a).mpr ha, ?_⟩
  intro b hb
  obtain ⟨b, rfl⟩ := e.surjective b
  exact congrArg e (hu b ((he b).mp hb))

end Hecke

end BorderVNP
end Computability
end OAI
