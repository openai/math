import OAI.Computability.BorderVNP.DecisionComponents
import OAI.Computability.BorderVNP.GeneratorGeneric

/-! # Separating a component before an affine slice

A polynomial can vanish on all the other components while remaining nonzero
somewhere on the chosen component. On its principal open, a finite slice of
that component isolates points of the full sliced variety.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Generator

open MvPolynomial Decision Set

variable {E : Type*} [Field E] {I : Type}

/-- The affine Zariski topology in which the component separator is a principal open. -/
noncomputable local instance pointTopologyComponents : TopologicalSpace (I → E) := affineTopology I E

private theorem equation_off_closed {B : Set (I → E)} {x : I → E}
    (hB : IsClosed B) (hx : x ∉ B) :
    ∃ p : MvPolynomial I E, eval x p ≠ 0 ∧ VanishesOn B p := by
  rw [← hB.closure_eq, affine_closure] at hx
  change ¬ ∀ p : MvPolynomial I E, VanishesOn B p → eval x p = 0 at hx
  push Not at hx
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p, hx, hp⟩

/-- A single polynomial selects the chosen irreducible component on a
nonempty principal open, regardless of the number of other components. -/
theorem component_separator [IsAlgClosed E] [Finite I] {A V : Set (I → E)}
    (closed : imageClosure V = V) (component : IsComponent A V) :
    ∃ f : MvPolynomial I E, (∃ x ∈ A, eval x f ≠ 0) ∧
      ∀ y ∈ V, eval y f ≠ 0 → y ∈ A := by
  classical
  obtain ⟨parts, cover, hp⟩ := closed_eq_union_components closed
  let others := parts.erase A
  let B := ⋃₀ (others : Set (Set (I → E)))
  have hclosed (W) (hW : W ∈ others) : imageClosure W = W :=
    (hp W (Finset.mem_of_mem_erase hW)).2.1
  have hc : IsClosed B := others.finite_toSet.isClosed_sUnion fun W hW =>
    closure_eq_iff_isClosed.mp ((affine_closure W).trans (hclosed W hW))
  have h : ¬ A ⊆ B := by
    intro hsub
    obtain ⟨W, hW, hAW⟩ := subset_member_of_finite_closed_cover component.2.2.1 others hclosed hsub
    have hcomp := hp W (Finset.mem_of_mem_erase hW)
    have hWA := component.2.2.2 W hcomp.1 hcomp.2.1 hcomp.2.2.1 hAW
    exact (Finset.mem_erase.mp hW).1 (Subset.antisymm hWA hAW)
  obtain ⟨x, hx, hxB⟩ := not_subset.mp h
  obtain ⟨f, hxf, hf⟩ := equation_off_closed hc hxB
  refine ⟨f, ⟨x, hx, hxf⟩, fun y hy hn => ?_⟩
  rw [cover] at hy
  obtain ⟨W, hW, hyW⟩ := hy
  by_contra hny
  have hWA : W ≠ A := fun e => hny (e ▸ hyW)
  exact hn (hf y ⟨W, Finset.mem_erase.mpr ⟨hWA, hW⟩, hyW⟩)

/-- Every rational point is Zariski closed in the affine topology. -/
theorem affine_singleton_closed (x : I → E) : IsClosed ({x} : Set (I → E)) := by
  rw [← closure_subset_iff_isClosed, affine_closure]
  intro y hy
  apply mem_singleton_iff.mpr
  funext i
  have h := hy (X i - MvPolynomial.C (x i)) (by simp)
  simpa [sub_eq_zero] using h

/-- If a component has finite intersection with a slice, each point of that
intersection lying off the other components is isolated by a principal open
in the full slice. The slice can be specified by any set of equations. -/
theorem isolate_slice_point {A V T : Set (I → E)} {x : I → E} {f : MvPolynomial I E}
    (sep : ∀ y ∈ V, eval y f ≠ 0 → y ∈ A)
    (finiteSlice : (A ∩ T).Finite) (hf : eval x f ≠ 0) :
    ∃ g : MvPolynomial I E, eval x g ≠ 0 ∧
      ∀ y ∈ V ∩ T, eval y g ≠ 0 → y = x := by
  classical
  let B := (A ∩ T) \ {x}
  have hb : B.Finite := finiteSlice.subset sdiff_subset
  have hc : IsClosed B := by
    let : T1Space (I → E) := ⟨affine_singleton_closed⟩
    exact hb.isClosed
  obtain ⟨p, hpx, hp⟩ := equation_off_closed hc (show x ∉ B by simp [B])
  refine ⟨f * p, by simpa using mul_ne_zero hf hpx, fun y hy hn => ?_⟩
  rw [map_mul, mul_ne_zero_iff] at hn
  by_contra hne
  exact hn.2 (hp y ⟨⟨sep y hy.1 hn.1, hy.2⟩, hne⟩)

/-- A principal open isolating a point in a set makes that point a
maximal irreducible closed subset of the set. -/
theorem singleton_component_of_isolating_polynomial {V : Set (I → E)}
    {x : I → E} {g : MvPolynomial I E} (hx : x ∈ V) (hg : eval x g ≠ 0)
    (isolates : ∀ y ∈ V, eval y g ≠ 0 → y = x) : IsComponent {x} V := by
  have closed := (affine_closure ({x} : Set (I → E))).symm.trans (affine_singleton_closed x).closure_eq
  refine ⟨singleton_subset_iff.mpr hx, closed, (irreducible_iff_prime _).mpr inferInstance, ?_⟩
  intro D hDV _ hirr hxD y hy
  rw [← closed]
  intro p hp
  have prod : VanishesOn D (g * p) := by
    intro z hz
    rw [map_mul]
    by_cases h : eval z g = 0
    · rw [h, zero_mul]
    · rw [isolates z (hDV hz) h, hp x rfl, mul_zero]
  have hnp : ¬ VanishesOn D g := fun h => hg (h x (singleton_subset_iff.mp hxD))
  exact ((hirr.2 g p prod).resolve_left hnp) y hy

/-- An isolated affine point of a zero locus gives a minimal prime above the
actual defining ideal, including when the equations generate a nonradical ideal. -/
theorem point_minimalPrime_of_isolating_polynomial [IsAlgClosed E] [Finite I]
    {J : Ideal (MvPolynomial I E)} {x : I → E} {g : MvPolynomial I E}
    (hx : x ∈ zeroLocus E J) (hg : eval x g ≠ 0)
    (isolates : ∀ y ∈ zeroLocus E J, eval y g ≠ 0 → y = x) :
    vanishingIdeal E {x} ∈ J.minimalPrimes := by
  refine ⟨⟨inferInstance, le_zeroLocus_iff_le_vanishingIdeal.mp (singleton_subset_iff.mpr hx)⟩, ?_⟩
  intro Q hQ hQx
  have : Q.IsPrime := hQ.1
  have hxQ : x ∈ zeroLocus E Q := singleton_subset_iff.mp (le_zeroLocus_iff_le_vanishingIdeal.mpr hQx)
  intro p hp
  have prod : g * p ∈ vanishingIdeal E (zeroLocus E Q) := by
    intro y hy
    rw [aeval_eq_eval, map_mul]
    by_cases h : eval y g = 0
    · rw [h, zero_mul]
    · rw [isolates y (zeroLocus_anti_mono hQ.2 hy) h, show eval x p = 0 from hp x rfl, mul_zero]
  rw [IsPrime.vanishingIdeal_zeroLocus] at prod
  exact (Ideal.IsPrime.mem_or_mem inferInstance prod).resolve_left fun h => hg (hxQ g h)

end Generator

end BorderVNP
end Computability
end OAI
