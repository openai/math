import OAI.Computability.NearSquareRoot.CRTControlledBenesSplit
import OAI.Computability.NearSquareRoot.CRTTableWordRows

/-! # Interpreting padded unary indices as fixed-width Beneš words -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication IntegerMultiplication.Code

private def encodeWord (d : ℕ) (j : Fin (2 ^ d)) : Benes.Word d :=
  fun i => (Bits.phrase d j.val).reverse[i.val]'(by simp [Bits.phrase_length])

private theorem encodeWord_ofFn (d : ℕ) (j : Fin (2 ^ d)) :
    List.ofFn (encodeWord d j) = (Bits.phrase d j.val).reverse := by
  apply List.ext_getElem
  · simp [Bits.phrase_length]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    rfl

private def decodeWord (d : ℕ) (w : Benes.Word d) : Fin (2 ^ d) :=
  ⟨Bits.value (List.ofFn w).reverse, by simpa using Bits.value_lt (List.ofFn w).reverse⟩

/-- Binary spelling with the most significant bit at Beneš port zero. -/
def wordEquiv (d : ℕ) : Fin (2 ^ d) ≃ Benes.Word d where
  toFun := encodeWord d
  invFun := decodeWord d
  left_inv j := by
    apply Fin.ext
    simp [decodeWord, encodeWord_ofFn, Bits.value_phrase j.isLt]
  right_inv w := by
    apply List.ofFn_injective
    rw [encodeWord_ofFn]
    apply List.reverse_injective
    rw [List.reverse_reverse]
    exact Bits.word_inject _ _ (by simp [Bits.phrase_length])
      (Bits.value_phrase (decodeWord d w).isLt)

@[simp] theorem ofFn_wordEquiv (d : ℕ) (j : Fin (2 ^ d)) :
    List.ofFn (wordEquiv d j) = (Bits.phrase d j.val).reverse :=
  encodeWord_ofFn d j

theorem finRows_represents (d : ℕ) (π : Equiv.Perm (Fin (2 ^ d))) :
    Benes.RawRepresents ((wordEquiv d).symm.trans (π.trans (wordEquiv d)))
      ((List.finRange (2 ^ d)).map (fun j =>
        ((Bits.phrase d j.val).reverse,(Bits.phrase d (π j).val).reverse))) := by
  refine ⟨(List.finRange (2 ^ d)).map (wordEquiv d), ?_, ?_, ?_⟩
  · exact (List.nodup_finRange _).map (wordEquiv d).injective
  · intro w
    exact List.mem_map.mpr ⟨(wordEquiv d).symm w, by simp, (wordEquiv d).apply_symm_apply w⟩
  · simp [List.map_map, Function.comp_def]

private theorem ofFn_rows_eq (d : ℕ) (tab : List Tally) (π : Equiv.Perm (Fin (2 ^ d)))
    (hlen : tab.length = 2 ^ d)
    (entries : ∀ j : Fin (2 ^ d), (tab[j.val]'(by rw [hlen]; exact j.isLt)).length = (π j).val) :
    List.ofFn (fun j : Fin tab.length =>
      ((Bits.short d j.val).reverse, (Bits.short d (tab[j.val]).length).reverse)) =
      (List.finRange (2 ^ d)).map (fun j =>
        ((Bits.phrase d j.val).reverse,(Bits.phrase d (π j).val).reverse)) := by
  apply List.ext_getElem
  · simpa using hlen
  · intro j hl hr
    have hj : j < 2 ^ d := by simpa using hr
    let i : Fin (2 ^ d) := ⟨j,hj⟩
    have he := entries i
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_finRange, Bits.short]
    change (_, (Bits.phrase d ((tab[j]).length % 2 ^ d)).reverse) = (_, (Bits.phrase d (π i).val).reverse)
    rw [he, Nat.mod_eq_of_lt (π i).isLt, Nat.mod_eq_of_lt hj]
    rfl

/-- If each entry of a full padded unary table is the destination index of
its port, the generated raw bit rows represent the same permutation on
most-significant-first Beneš words. -/
theorem wordRows_represents (d : ℕ) (tab : List Tally) (π : Equiv.Perm (Fin (2 ^ d)))
    (hlen : tab.length = 2 ^ d)
    (entries : ∀ j : Fin (2 ^ d), (tab[j.val]'(by rw [hlen]; exact j.isLt)).length = (π j).val) :
    Benes.RawRepresents ((wordEquiv d).symm.trans (π.trans (wordEquiv d))) (wordRows (tally d,tab)) := by
  rw [wordRows_eq, ofFn_rows_eq d tab π hlen entries]
  exact finRows_represents _ _

end CRTTable

end NearSquareRoot
end Computability
end OAI
