import OAI.Computability.NearSquareRoot.BoxShape
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.ZMod.Basic

/-! # Finite cyclic and padded coordinates of a valid coprime box -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

variable (box : List (ℕ × ℕ))

/-- The axis order in the group used by the CRT transform. -/
def modulus (i : Fin box.length) : ℕ := (box.get i).2

/-- Number of the unused addresses on this axis. -/
def padding (i : Fin box.length) : ℕ := 2 ^ (box.get i).1 - modulus box i

variable {box} {k l : ℕ}

theorem modulus_neZero (hb : BoxShape.Valid k l box) (i : Fin box.length) :
    NeZero (modulus box i) := by
  have h := (hb.axisBounds _ (List.get_mem box i)).2.2.1
  exact ⟨Nat.ne_of_gt (by unfold modulus; omega)⟩

theorem pairwise (hb : BoxShape.Valid k l box) :
    Pairwise (fun i j => (modulus box i).Coprime (modulus box j)) := by
  have h := List.pairwise_map.mp hb.coprime
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact List.pairwise_iff_get.mp h i j hlt
  · exact (List.pairwise_iff_get.mp h j i hgt).symm

theorem prod_modulus : (∏ i, modulus box i) = (box.map Prod.snd).prod :=
  Fin.prod_univ_fun_getElem box Prod.snd

theorem capacity (hb : BoxShape.Valid k l box) {h : ℕ} (hk : 4 * h ≤ 2 ^ k) :
    2 * h ≤ ∏ i, modulus box i := by
  rw [prod_modulus]
  exact hb.capacity hk

/-- In `ZMod a ⊕ Fin b`, the left summand enumerates the valid axis coordinates and
the right summand enumerates the padding, giving exactly one slot per binary address. -/
theorem card_padded (hb : BoxShape.Valid k l box) [∀ i, NeZero (modulus box i)] :
    Fintype.card ((i : Fin box.length) → ZMod (modulus box i) ⊕ Fin (padding box i)) = 2 ^ k := by
  classical
  have h (i : Fin box.length) : modulus box i + padding box i = 2 ^ (box.get i).1 := by
    exact Nat.add_sub_of_le (hb.axisBounds _ (List.get_mem box i)).2.2.2
  rw [Fintype.card_pi]
  simp only [Fintype.card_sum, ZMod.card, Fintype.card_fin, h]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact (Fin.sum_univ_fun_getElem box Prod.fst).trans hb.widthSum

end BoxFin

end NearSquareRoot
end Computability
end OAI
