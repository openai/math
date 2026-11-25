import OAI.Computability.BorderVNP.CoverLorentzCovering
import OAI.Computability.BorderVNP.CoverHeckeCoverArea

/-!
# Degree of the local isometry on the hyperbolic surfaces

The target lattice acts freely on every point of the hyperbolic plane. Thus
the fiber over a given surface point has one element for each right coset of
the conjugated source lattice in the target lattice. Combining this with
the Haar area calculation gives the exact stable covering degree of §5.2.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Hecke BorderVNP.Cover.Frame UpperHalfPlane

private theorem lattice_orbit_injective (d : ℕ) (y : ℍ) :
    Function.Injective (fun a : lattice (d+1) => (a : SL) • y) := by
  rintro ⟨_,a,rfl⟩ ⟨_,b,rfl⟩ he
  have hb : b⁻¹*a = 1 := eq_one_of_fix _ y (by
    rw [map_mul,map_inv,mul_smul]; change (gammaSL (d+1) b)⁻¹ • (gammaSL (d+1) a • y) = y
    rw [show gammaSL (d+1) a • y = gammaSL (d+1) b • y from he,inv_smul_smul])
  exact congrArg (fun v : gamma (d+1) => (gammaSL (d+1)).rangeRestrict v) ((eq_of_inv_mul_eq_one hb).symm)

/-- For positive base depth, each fiber of the surface map is parametrized by the
cosets of the conjugated lattice. -/
noncomputable def surfaceMotionFiber {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ) (y : ℍ) :
    Cosets ((movedLattice g (d+1+2*a)).subgroupOf (lattice (d+1))) ≃
      {x // surfaceMotion hg (d+1) x = projectPoint (d+1) y} := by
  let k := d+1+2*a
  let Γ := lattice (d+1)
  let T := (movedLattice g k).subgroupOf Γ
  let f (b : Γ) : {x // surfaceMotion hg (d+1) x = projectPoint (d+1) y} :=
    ⟨projectPoint k ((g⁻¹*(b : SL)) • y), by
      rw [surfaceMotion_project, mul_smul,smul_inv_smul]
      obtain ⟨v,hv⟩ := b.property
      exact Quotient.sound ((planeRel (d+1)).symm ⟨v,by rw [hv]⟩)⟩
  have he (b c : Γ) : f b = f c ↔ QuotientGroup.rightRel T b c := by
    rw [Subtype.ext_iff,QuotientGroup.rightRel_apply]
    change projectPoint k ((g⁻¹*(b : SL)) • y) = projectPoint k ((g⁻¹*(c : SL)) • y) ↔
      (c : SL)*(b : SL)⁻¹ ∈ movedLattice g k
    constructor
    · intro hbc
      obtain ⟨u,hu⟩ := Quotient.exact hbc
      let v : Γ := ⟨g*gammaSL k u*g⁻¹,conjugate_lattice hg (d+1) ⟨u,rfl⟩⟩
      have eq : v*b = c := lattice_orbit_injective d y (by
        have e := congrArg (fun z : ℍ => g • z) hu
        change ((g*gammaSL k u*g⁻¹)*(b : SL)) • y = (c : SL) • y
        simpa [mul_smul] using e)
      refine ⟨gammaSL k u,⟨u,rfl⟩,?_⟩
      change (v : SL) = (c : SL)*(b : SL)⁻¹
      rw [← eq,Subgroup.coe_mul,mul_inv_cancel_right]
    · rintro ⟨_,⟨u,rfl⟩,hu⟩
      change g * gammaSL k u * g⁻¹ = (c : SL)*(b : SL)⁻¹ at hu
      apply Quotient.sound
      refine ⟨u,?_⟩
      have eq : gammaSL k u * (g⁻¹*(b : SL)) = g⁻¹*(c : SL) := by
        calc
          _ = g⁻¹ * (g * gammaSL k u * g⁻¹) * (b : SL) := by group
          _ = _ := by rw [hu]; group
      exact (mul_smul _ _ _).symm.trans (congrArg (fun m : SL => m • y) eq)
  let F : Cosets T → _ := Quotient.lift f fun b c h => (he b c).mpr h
  apply Equiv.ofBijective F
  constructor
  · rintro ⟨b⟩ ⟨c⟩ e
    exact Quotient.sound ((he b c).mp e)
  · rintro ⟨⟨w⟩, hw⟩
    obtain ⟨u,hu⟩ := Quotient.exact hw.symm
    let b : Γ := (gammaSL (d+1)).rangeRestrict u
    refine ⟨coset T b,Subtype.ext ?_⟩
    change projectPoint k ((g⁻¹*(b : SL)) • y) = projectPoint k w
    rw [mul_smul,show (b : SL) • y = g • w from hu,inv_smul_smul]

/-- Exact fiber cardinality of the paper's hyperbolic surface covering map, uniform
over every target point at stable depth. -/
theorem surfaceMotion_card {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ) (y : Surface (d+2)) :
    Nat.card {x // surfaceMotion hg (d+2) x = y} = (7^3)^(2*a) := by
  rcases y with ⟨y⟩
  let e := surfaceMotionFiber hg (d+1) y
  exact (Nat.card_congr (e.symm.trans (QuotientGroup.quotientRightRelEquivQuotientLeftRel _))).trans
    (movedLattice_index_eq hg d)

end Cover

end BorderVNP
end Computability
end OAI
