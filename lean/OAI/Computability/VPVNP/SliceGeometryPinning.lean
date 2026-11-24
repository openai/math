import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Finite slices from coordinate projections

For a coordinate image that is cofinite in the algebraic closure, pin that
coordinate to a base-field value in the image. Finite coordinate images only
shrink during later cuts. If each exceptional set has at most `B` elements and
`B < #K`, at most one pin per variable produces a nonempty slice with at most
`B^t` geometric points.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceGeometry

open Set

variable {K E : Type*} [Field K] [Field E] [Algebra K E] {t : ℕ}

/-- Geometric points satisfying the original equations and a set of base-field
coordinate pins. -/
def pinnedPoints (V : Set (Fin t → E)) (s : Finset (Fin t)) (a : Fin t → K) : Set (Fin t → E) :=
  {x | x ∈ V ∧ ∀ i ∈ s, x i = algebraMap K E (a i)}

/-- The possible values of coordinate `i` on a geometric set. -/
def coordinateImage (V : Set (Fin t → E)) (i : Fin t) : Set E := (fun x => x i) '' V

/-- A coordinate image has at most `B` points, or its complement has at most
`B` points. The finite-set hypotheses distinguish these alternatives even when
`Set.ncard` would vanish on an infinite set. -/
def boundedOrCobounded (S : Set E) (B : ℕ) : Prop :=
  (S.Finite ∧ S.ncard ≤ B) ∨ (Sᶜ.Finite ∧ Sᶜ.ncard ≤ B)

private theorem exists_base_point [Fintype K] {S : Set E} {B : ℕ}
    (h : Sᶜ.Finite) (hc : Sᶜ.ncard ≤ B) (hB : B < Fintype.card K) :
    ∃ c : K, algebraMap K E c ∈ S := by
  by_contra! hall
  let f (c : K) : ↥(Sᶜ) := ⟨algebraMap K E c, hall c⟩
  let : Finite ↥(Sᶜ) := finite_coe_iff.mpr h
  have hle := Nat.card_le_card_of_injective f (fun _ _ he => (algebraMap K E).injective
    (congrArg Subtype.val he))
  change Nat.card K ≤ Sᶜ.ncard at hle
  exact hB.not_ge ((Nat.card_eq_fintype_card (α := K)) ▸ hle.trans hc)

private theorem insert_pin (V : Set (Fin t → E)) (s : Finset (Fin t)) (a : Fin t → K)
    (i : Fin t) (hi : i ∉ s) (c : K) :
    pinnedPoints V (insert i s) (Function.update a i c) =
      pinnedPoints V s a ∩ {x | x i = algebraMap K E c} := by
  ext x
  constructor
  · rintro ⟨hv, hx⟩
    refine ⟨⟨hv, fun j hj => ?_⟩, ?_⟩
    · have hji : j ≠ i := fun e => hi (e ▸ hj)
      simpa only [Function.update_of_ne hji] using hx j (Finset.mem_insert_of_mem hj)
    · change x i = algebraMap K E c
      simpa only [Function.update_self] using hx i (Finset.mem_insert_self ..)
  · rintro ⟨⟨hv, hx⟩, hc⟩
    refine ⟨hv, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hs
    · change x j = algebraMap K E c at hc
      simpa only [Function.update_self] using hc
    · have hji : j ≠ i := fun e => hi (e ▸ hs)
      rw [Function.update_of_ne hji]
      exact hx j hs

omit [Field E] in
private theorem bounded_set_of_coordinate_images {W : Set (Fin t → E)} {B : ℕ}
    (h : ∀ i, (coordinateImage W i).Finite ∧ (coordinateImage W i).ncard ≤ B) :
    W.Finite ∧ W.ncard ≤ B ^ t := by
  classical
  let target (i : Fin t) := coordinateImage W i
  let (i : Fin t) : Finite (target i) := finite_coe_iff.mpr (h i).1
  let f (x : W) (i : Fin t) : target i := ⟨x.val i, ⟨x.val, x.prop, rfl⟩⟩
  have hf : Function.Injective f := fun u v he => Subtype.ext (funext fun i =>
    congrArg Subtype.val (congrFun he i))
  refine ⟨finite_coe_iff.mp (Finite.of_injective f hf), ?_⟩
  calc
    W.ncard ≤ Nat.card ((i : Fin t) → target i) := Nat.card_le_card_of_injective f hf
    _ = ∏ i, (coordinateImage W i).ncard := Nat.card_pi
    _ ≤ ∏ _ : Fin t, B := Finset.prod_le_prod (fun i _ => (h i).2)
    _ = B ^ t := by simp

/-- At most `t` distinct coordinate equations suffice when every projection of
a partially pinned system has a bounded exceptional set. -/
theorem exists_finite_pinned_slice [Fintype K] (V : Set (Fin t → E)) (hv : V.Nonempty)
    (B : ℕ) (hpos : 0 < B) (hB : B < Fintype.card K)
    (hproj : ∀ (s : Finset (Fin t)) (a : Fin t → K) (i : Fin t),
      boundedOrCobounded (coordinateImage (pinnedPoints V s a) i) B) :
    ∃ (s : Finset (Fin t)) (a : Fin t → K),
      let W := pinnedPoints V s a
      W.Nonempty ∧ W.Finite ∧ W.ncard ≤ B ^ t := by
  classical
  have build (T : Finset (Fin t)) : ∃ (s : Finset (Fin t)) (a : Fin t → K), s ⊆ T ∧
      let W := pinnedPoints V s a
      W.Nonempty ∧ ∀ i ∈ T, (coordinateImage W i).Finite ∧ (coordinateImage W i).ncard ≤ B := by
    induction T using Finset.induction_on with
    | empty =>
      exact ⟨∅, 0, le_rfl, by simpa [pinnedPoints] using hv, by simp⟩
    | @insert i T hi ih =>
      obtain ⟨s, a, hs, hw, hbound⟩ := ih
      let W := pinnedPoints V s a
      rcases hproj s a i with hfin | ⟨hco, hsize⟩
      · refine ⟨s, a, hs.trans (Finset.subset_insert ..), hw, fun j hj => ?_⟩
        rcases Finset.mem_insert.mp hj with rfl | hT
        · exact hfin
        · exact hbound j hT
      · obtain ⟨c, x, hx, he⟩ := exists_base_point hco hsize hB
        let W' := pinnedPoints V (insert i s) (Function.update a i c)
        have hW : W' = W ∩ {y | y i = algebraMap K E c} :=
          insert_pin V s a i (fun hm => hi (hs hm)) c
        refine ⟨insert i s, Function.update a i c, Finset.insert_subset_insert _ hs,
          ⟨x, (show x ∈ W' from hW.symm ▸ ⟨hx, he⟩)⟩, fun j hj => ?_⟩
        rcases Finset.mem_insert.mp hj with rfl | hT
        · have hsub : coordinateImage W' j ⊆ {algebraMap K E c} := by
            rintro _ ⟨y, hy, rfl⟩
            exact (hW ▸ hy).2
          exact ⟨(finite_singleton _).subset hsub, (ncard_le_ncard hsub).trans (by simpa using (Nat.succ_le_of_lt hpos))⟩
        · have hsub : coordinateImage W' j ⊆ coordinateImage W j :=
            image_mono (hW.symm ▸ inter_subset_left)
          exact ⟨(hbound j hT).1.subset hsub, (ncard_le_ncard hsub (hbound j hT).1).trans (hbound j hT).2⟩
  obtain ⟨s, a, _, hn, hb⟩ := build Finset.univ
  exact ⟨s, a, hn, bounded_set_of_coordinate_images (fun i => hb i (Finset.mem_univ _))⟩

end SliceGeometry

end VPVNP
end Computability
end OAI
