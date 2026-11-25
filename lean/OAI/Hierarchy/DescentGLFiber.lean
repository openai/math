import OAI.Hierarchy.DescentGLTransitive
import OAI.Hierarchy.DescentGLPrefix
import Mathlib.Data.Fintype.BigOperators

namespace OAI
/-! # Counting invertible layouts by their action on a nonzero difference -/

namespace Hierarchy.DescentGL

open scoped Classical
noncomputable section

abbrev Layout (k : ℕ) := Bits k ≃ₗ[ZMod 2] Bits k

instance layoutFintype (k : ℕ) : Fintype (Layout k) :=
  Fintype.ofInjective (fun L : Layout k => (L : Bits k → Bits k)) (by
    intro L M eqn
    exact LinearEquiv.ext (fun x => congrFun eqn x))

def image {k : ℕ} (d : Nonzero k) (L : Layout k) : Nonzero k :=
  ⟨L d.val, fun h => d.property (L.injective (h.trans L.map_zero.symm))⟩

private def postcompose {k : ℕ} (T : Layout k) : Layout k ≃ Layout k where
  toFun L := L.trans T
  invFun L := L.trans T.symm
  left_inv L := LinearEquiv.ext (fun x => T.symm_apply_apply (L x))
  right_inv L := LinearEquiv.ext (fun x => T.apply_symm_apply (L x))

theorem equal_fibers {k : ℕ} (d a b : Nonzero k) :
    Fintype.card {L : Layout k // image d L=a} =
      Fintype.card {L : Layout k // image d L=b} := by
  obtain ⟨T,hT⟩ := exists_map a.property b.property
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (postcompose T)
  intro L
  simp only [Subtype.ext_iff]
  change (L d.val=a.val) ↔ T (L d.val)=b.val
  rw [←hT,T.injective.eq_iff]

/-- Count a subset by its equal-sized fibers. This applies to a conditional
ensemble as soon as the residual transformations are transitive there. -/
theorem uniform_multiplicity {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (f : A → B)
    (b : B) (P : B → Prop) (Q : A → Prop) [DecidablePred P] [DecidablePred Q]
    (compatible : ∀ a, Q a ↔ P (f a))
    (uniform : ∀ t, Fintype.card {a // f a=t} = Fintype.card {a // f a=b}) :
    Fintype.card {a // Q a} * Fintype.card B =
      Fintype.card {t // P t} * Fintype.card A := by
  let m := Fintype.card {a // f a=b}
  have all : Fintype.card A=Fintype.card B*m := calc
    _ = Fintype.card ((t : B) × {a // f a=t}) := (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ t : B, Fintype.card {a // f a=t} := Fintype.card_sigma
    _ = ∑ _ : B, m := Finset.sum_congr rfl fun t _ => uniform t
    _ = _ := by simp
  have hit : Fintype.card {a // Q a}=Fintype.card {t // P t}*m := calc
    _ = Fintype.card ((t : {t // P t}) × {a // f a=t.val}) :=
      (Fintype.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype f compatible)).symm
    _ = ∑ t : {t // P t}, Fintype.card {a // f a=t.val} := Fintype.card_sigma
    _ = ∑ _ : {t // P t}, m := Finset.sum_congr rfl fun t _ => uniform t.val
    _ = _ := by simp
  rw [all,hit]
  ac_rfl

/-- The exact count of colliding layouts, before converting to a probability. -/
theorem prefix_collision_count {k j : ℕ} (hj : j≤k) (x y : Bits k) (ne : x≠y) :
    (Finset.univ.filter (fun L : Layout k => headRows hj (L x) = headRows hj (L y))).card *
        (2^k-1) = (2^(k-j)-1)*Fintype.card (Layout k) := by
  let d : Nonzero k := ⟨x-y,sub_ne_zero.mpr ne⟩
  have compat (L : Layout k) :
      headRows hj (L x)=headRows hj (L y) ↔ headRows hj (image d L).val=0 := by
    change _ ↔ headRows hj (L (x-y))=0
    rw [map_sub]
    change _ ↔ headRows hj (L x)-headRows hj (L y)=0
    exact sub_eq_zero.symm
  have count := uniform_multiplicity (image d) d (fun t => headRows hj t.val=0)
    (fun L => headRows hj (L x)=headRows hj (L y)) compat (fun t => equal_fibers d t d)
  rw [zero_prefix_card,card_nonzero] at count
  rw [Fintype.card_subtype] at count
  exact count

end
end Hierarchy.DescentGL

end OAI
