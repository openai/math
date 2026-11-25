import OAI.Hierarchy.TaggedData
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Physical payload slicing at a common address length -/

noncomputable section
namespace Hierarchy.Tagged.Slices
open scoped Classical BigOperators

variable {F : Type*} [Field F] {h w m : ℕ} (v : Fin m → ℕ)
  (total : ∑ i, v i = w)

def column : (Σ i, Fin (v i)) ≃ Fin w := finSigmaFinEquiv.trans (finCongr total)

private def split : Bits w ↪ ((i : Fin m) → Bits (v i)) where
  toFun x i j := x (column v total ⟨i,j⟩)
  inj' := by
    intro x y eq
    funext b
    obtain ⟨⟨i,j⟩,rfl⟩ := (column v total).surjective b
    exact congrFun (congrFun eq i) j

private def select (i : Fin m) : Port h (v i) → Port h w
  | .inl (r,b) => .inl (r,column v total ⟨i,b⟩)
  | .inr (.inl t) => .inr (.inl t)
  | .inr (.inr (r,b)) => .inr (.inr (r,column v total ⟨i,b⟩))

/-- Source and target columns are disjoint across slices, while each tag
address is read from its unique original input. -/
def pin (i : Fin m) : Fin (pins h (v i)) → Fin (pins h w) :=
  portIndex h w ∘ select v total i ∘ (portIndex h (v i)).symm

theorem coefficient [Nonempty (Fin m)] (x : Fin (pins h w) → Bool) :
    (∏ i, coeff F h (v i) (x ∘ pin v total i)) = coeff F h w x := by
  have s (i : Fin m) : source (x ∘ pin v total i) =
      fun r => split v total (source x r) i := by
    funext r b
    simp [source,pin,select,split]
    rfl
  have t (i : Fin m) : target (x ∘ pin v total i) =
      fun r => split v total (target x r) i := by
    funext r b
    simp [target,pin,select,split]
    rfl
  have a (i : Fin m) : tag (x ∘ pin v total i) = tag x := by
    funext r
    simp [tag,pin,select]
  have e := (valid_map_iff (split v total) (source x) (target x) (tag x)).symm.trans
    (valid_iff_slices ((split v total) ∘ source x) ((split v total) ∘ target x) (tag x))
  simp only [coeff,s,t,a,Fintype.prod_boole]
  simp only [Function.comp_apply] at e
  by_cases valid : Valid (source x) (tag x) (target x)
  · rw [ite_eq_left (e.mp valid), ite_eq_left valid]
  · rw [ite_eq_right (fun h => valid (e.mpr h)), ite_eq_right valid]

include total in
theorem pins_le_sum (positive : 0 < m) : pins h w ≤ ∑ i, pins h (v i) := by
  have payload : ∑ i, 2^h * v i = 2^h * w := by rw [← Finset.mul_sum,total]
  simp only [pins, Finset.sum_add_distrib, payload, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,Nat.cast_id]
  have bill := Nat.le_mul_of_pos_left (2^h*h) positive
  omega

end Hierarchy.Tagged.Slices

end
end OAI
