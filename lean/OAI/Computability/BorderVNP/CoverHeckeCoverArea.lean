import OAI.Computability.BorderVNP.CoverHeckeCoverDegree
import OAI.Computability.BorderVNP.CoverLorentzPlane
import OAI.Computability.BorderVNP.CoverFrameNormalizedHaar

/-!
# Exact covering degree by normalized Haar area

Counting the tiles in a fundamental domain gives the relative index.
Translating such a domain gives a domain for the conjugated subgroup,
with exactly the same Haar volume. The central quotient preserves the
index because every positive-level lattice injects into the projective group.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open Hecke MeasureTheory Set Finset
open scoped ENNReal Pointwise

private theorem index_eq_card_cosets {G : Type*} [Group G] (S : Subgroup G)
    [Fintype (Cosets S)] : S.index = Fintype.card (Cosets S) :=
  (Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm).trans
    Nat.card_eq_fintype_card

private theorem area_expanded {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (Γ : Subgroup G) (S : Subgroup Γ) [Fintype (Cosets S)] (μ : Measure G)
    [μ.IsMulLeftInvariant] {D : Set G} (hD : MeasurableSet D) (hd : ExactTile Γ D) (hμ : μ D = 1) :
    μ (expandedTile Γ S D) = S.index := by
  rw [expandedTile, measure_iUnion (disjoint_expandedTile Γ S hd)
    (fun i : Cosets S => hD.const_smul (i.out : G)), tsum_fintype]
  simp [measure_smul, hμ, index_eq_card_cosets]

private theorem equal_index_by_area {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (Γ : Subgroup G) [Countable Γ] (S T : Subgroup Γ) [Fintype (Cosets S)] [Fintype (Cosets T)]
    (z : G) (e : S ≃* T) (he : ∀ b : S, (((e b : T) : Γ) : G) = z * ((b : Γ) : G) * z⁻¹)
    (μ : Measure G) [μ.IsMulLeftInvariant] {D : Set G} (hD : MeasurableSet D)
    (hd : ExactTile Γ D) (hμ : μ D = 1) : S.index = T.index := by
  let E := expandedTile Γ S D
  have hzt : IsFundamentalDomain T (z • E) μ := by
    apply IsFundamentalDomain.mk' ((measurableSet_expandedTile Γ S hD).const_smul z).nullMeasurableSet
    intro x
    obtain ⟨b,hb,hu⟩ := exact_expandedTile Γ S hd (z⁻¹*x)
    have heq (a : S) : e a • x ∈ z • E ↔ ((a : Γ) : G) * (z⁻¹*x) ∈ E := by
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      change z⁻¹ * ((((e a : T) : Γ) : G)*x) ∈ E ↔ _
      rw [he]; simp [mul_assoc]
    refine ⟨e b,(heq b).mpr hb,?_⟩
    intro t ht
    obtain ⟨t,rfl⟩ := e.surjective t
    exact congrArg e (hu t ((heq t).mp ht))
  have h := hzt.measure_eq (fundamental_expandedTile Γ T hD hd μ)
  rw [measure_smul,area_expanded Γ S μ hD hd hμ,area_expanded Γ T μ hD hd hμ] at h
  exact_mod_cast h

/-- The degree of the moved lattice is the exact tile-count ratio, hence equals
`(7³)^(2a)` at every stable depth. -/
theorem movedLattice_index_eq {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ) :
    (movedLattice g (d+2+2*a)).relIndex (lattice (d+2)) = (7^3)^(2*a) := by
  let l := d+2
  let Γ := lattice l
  let A := lattice (l+2*a)
  let B := movedLattice g (l+2*a)
  have ha : A ≤ Γ := by
    rintro _ ⟨v,rfl⟩
    have hn : gamma (l+2*a) ≤ gamma l := by
      have h (k : ℕ) : gamma (l+k) ≤ gamma l := by
        induction k with
        | zero => exact le_rfl
        | succ k ih => exact (gamma_next _).trans ih
      exact h _
    exact ⟨⟨v.val, hn v.property⟩, rfl⟩
  have hb : B ≤ Γ := (movedLattice_bounds hg l).2
  let S := A.subgroupOf Γ
  let T := B.subgroupOf Γ
  have hfin (L : Subgroup Γ) (hL : L.index ≠ 0) : Fintype (Cosets L) := by
    have : Finite (Γ ⧸ L) := Nat.finite_of_card_ne_zero hL
    exact Fintype.ofFinite (Γ ⧸ L) |>.ofEquiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel L).symm
  let : Fintype (Cosets S) := hfin S (by change A.relIndex Γ ≠ 0; rw [lattice_index]; positivity)
  let : Fintype (Cosets T) := hfin T (movedLattice_index_bounds hg d).1.ne'
  let e : S ≃* T := ((Subgroup.subgroupOfEquivOfLe ha).trans ((MulAut.conj g).subgroupMap A)).trans
    (Subgroup.subgroupOfEquivOfLe hb).symm
  obtain ⟨μ,D,hμ,hD,hd,hm,_⟩ := exists_normalized_frameHaar l
  have he := equal_index_by_area Γ S T g e (fun _ => rfl) μ hD hd hm
  exact he.symm.trans (lattice_index d (2*a))

/-- Passing to the projective frame group keeps the exact degree of the covering. -/
theorem projective_index_eq {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ) :
    ((movedLattice g (d+2+2*a)).map project).relIndex ((lattice (d+2)).map project) =
      (7^3)^(2*a) := by
  let B := lattice (d+2)
  let A := movedLattice g (d+2+2*a)
  have hAB : A ≤ B := (movedLattice_bounds hg (d+2)).2
  have he : (A.map project).subgroupOf (B.map project) =
      (A.subgroupOf B).map (project.subgroupMap B) := by
    ext x
    constructor
    · rintro ⟨y,hy,h⟩
      exact ⟨⟨y,hAB hy⟩,hy,Subtype.ext h⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.val,hy,rfl⟩
  have hi : Function.Injective (project.subgroupMap B) := by
    rintro ⟨_,u,rfl⟩ ⟨_,v,rfl⟩ e
    apply Subtype.ext
    exact congrArg (gammaSL (d+2)) ((gammaPSL_injective (d+1)) (congrArg Subtype.val e))
  change ((A.map project).subgroupOf (B.map project)).index = _
  rw [he]
  exact (Subgroup.index_map_of_bijective ⟨hi,project.subgroupMap_surjective B⟩ _).trans
    (movedLattice_index_eq hg d)

end Cover.Frame

end BorderVNP
end Computability
end OAI
