import OAI.Computability.NearSquareRoot.CRTRouting
import OAI.Computability.NearSquareRoot.CRTTree
import Mathlib.Data.List.Sort

/-! # Assembly of the padded CRT routing tree -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRT
open CRTTree

variable {d : ℕ} {a : Fin d → ℕ} {E : Fin d → Type} [∀ i, NeZero (a i)]

/-- At most one controlled merge per depth. The two recursive calls are on disjoint
sets of axes. The returned program includes inverses on every padding address. -/
def build : (depth : ℕ) → (xs : List (Fin d)) → xs.Pairwise (· < ·) →
    xs.length ≤ 2 ^ depth → {p : BlockPerm a E xs.toFinset // Computes p}
  | 0, xs, _, h => ⟨identityBlock _, computes_leaf (xs.toFinset_card_le.trans (by simpa using h))⟩
  | depth+1, xs, sorted, size => by
    have hs := List.pairwise_append.mp (show (left xs ++ right xs).Pairwise (· < ·) by simpa)
    have ord : ∀ j ∈ (left xs).toFinset, ∀ i ∈ (right xs).toFinset, j < i := by
      simpa only [List.mem_toFinset] using hs.2.2
    have dis : Disjoint (left xs).toFinset (right xs).toFinset :=
      Finset.disjoint_left.mpr fun i hi hj => (lt_irrefl i) (ord i hi i hj)
    have cap : xs.length ≤ 2 * 2 ^ depth := by simpa only [pow_succ, mul_comm] using size
    have sizeL := length_le_of_mem_children cap (show left xs ∈ children xs by simp [children])
    have sizeR := length_le_of_mem_children cap (show right xs ∈ children xs by simp [children])
    let l := build depth (left xs) hs.1 sizeL
    let r := build depth (right xs) hs.2.1 sizeR
    have hu : xs.toFinset = (left xs).toFinset ∪ (right xs).toFinset := by
      rw [← List.toFinset_append, append_halves]
    rw [hu]
    exact ⟨merge l.val r.val dis, computes_merge _ _ dis ord l.property r.property⟩

/-- The realized full-box equivalence, at a depth fixed by the number of axes. -/
def paddedPermutation (a : Fin d → ℕ) (E : Fin d → Type) [∀ i, NeZero (a i)] :
    Equiv.Perm (Address a E) :=
  (build (a := a) (E := E) (Nat.clog 2 d) (List.finRange d) (List.sortedLT_finRange d).pairwise
    (by simpa using Nat.le_pow_clog (by decide : 1 < 2) d)).val.perm

theorem paddedPermutation_valid (h : Pairwise (fun i j => (a i).Coprime (a j)))
    (t : ∀ i, ZMod (a i)) : paddedPermutation a E (fun i => Sum.inl (t i)) =
      fun i => Sum.inl (scaled a h (rank a (fun j => (t j).val)) i) := by
  let p := build (a := a) (E := E) (Nat.clog 2 d) (List.finRange d) (List.sortedLT_finRange d).pairwise
    (by simpa using Nat.le_pow_clog (by decide : 1 < 2) d)
  funext i
  have h' := p.property (fun j => Sum.inl (t j)) t (fun _ _ => rfl) i (by simp)
  have fi : ((List.finRange d).toFinset.filter (· < i)) = Finset.Iio i := by ext; simp
  rw [scaled_rank a h]
  simpa only [p, paddedPermutation, partialRank, fi, ZMod.natCast_zmod_val] using h'

/-- Inverse routing recovers the same occupied coordinates, including in the presence of
unused axis addresses. -/
theorem paddedPermutation_inverse (h : Pairwise (fun i j => (a i).Coprime (a j)))
    (t : ∀ i, ZMod (a i)) :
    (paddedPermutation a E).symm
      (fun i => Sum.inl (scaled a h (rank a (fun j => (t j).val)) i)) =
      fun i => Sum.inl (t i) := by
  rw [← paddedPermutation_valid h t, Equiv.symm_apply_apply]

end CRT

end NearSquareRoot
end Computability
end OAI
