import OAI.LinearAlgebra.MatrixExponent.Tagged.Array
import OAI.LinearAlgebra.MatrixExponent.Diagram.Permute
import OAI.LinearAlgebra.MatrixExponent.Batcher
import OAI.LinearAlgebra.MatrixExponent.BitonicMerge
import OAI.LinearAlgebra.MatrixExponent.CompareExchange
import OAI.LinearAlgebra.MatrixExponent.AdjacentDuplicates

section
/-! # Verifying a large permutation by sorting both lists -/

namespace OAI.LinearAlgebra.MatrixExponent.Tagged

variable {F : Type} [Field F] {a : Wire} {w m : ℕ}

theorem cap (a : Wire) :
    Net F (.pair a a) .unit (fun x _ => if x.1 = x.2 then 1 else 0) (wd a) := by
  induction a with
  | bit => exact .table _ _ _ (by decide)
  | unit => exact Net.empty.pre (.unit _)
  | pair a b ha hb =>
    have h := ((ha.par hb).pre (.middle a b a b)).post (.unit' _)
    simpa only [wd, Prod.ext_iff, ite_and, ite_mul, one_mul, zero_mul] using h

private theorem sort_eq_iff [LinearOrder (Val a)] (x y : Val (tree w a)) :
    sortTree w x = sortTree w y ↔ (flatten w y).Perm (flatten w x) := by
  constructor
  · intro h
    exact (sortTree_perm w y).symm.trans (h ▸ sortTree_perm w x)
  · intro h
    apply flatten_inj w
    exact List.Perm.eq_of_pairwise' (sortTree_sorted w x) (sortTree_sorted w y)
      ((sortTree_perm w x).trans (h.symm.trans (sortTree_perm w y).symm))

/-- The order used by the sorter is immaterial for this permutation test. -/
theorem tag_of_sort [LinearOrder (Val (row w a))]
    (h : DNet F (tree w (row w a)) (tree w (row w a)) (sortTree w) m) :
    ∃ v ≤ 2 * m + 3 * 2 ^ w * (w + wd a), Net F (inputs w a) .unit (tag F w a) v := by
  obtain ⟨v, hv, g⟩ := ((label_net F w a).comp h).par h
  refine ⟨v + wd (tree w (row w a)), ?_, ?_⟩
  · refine (Nat.add_le_add_right hv _).trans ?_
    rw [wd_tree, wd, wd_word]
    exact le_of_eq (by ring)
  · convert g.comp (cap _) using 1
    funext x y
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      sort_eq_iff, tag, permuted]

/-- Any bit bundle can be ordered by permuting its bits into a word. -/
theorem exists_comparator (F : Type) [Field F] (a : Wire) :
    ∃ o : LinearOrder (Val a),
      DNet F (.pair a a) .bit (fun x => decide (@LT.lt _ o.toLT x.1 x.2)) (100 * (wd a + 1)) := by
  obtain ⟨f, hf, hi⟩ := Rewire.exists_of_width (wd_word (wd a)).symm
  refine ⟨LinearOrder.lift' f hi, ?_⟩
  exact (compare_lt F _).pre (hf.par hf)

end OAI.LinearAlgebra.MatrixExponent.Tagged
end

section
/-! # Testing distinctness at independent list and word lengths -/

namespace OAI.LinearAlgebra.MatrixExponent

theorem nodup_net (F : Type) [Field F] (j n : ℕ) :
    DNet F (tree j (word n)) .bit (fun x => decide (flatten j x).Nodup)
      (400 * 2 ^ j * (j + 1) ^ 2 * (n + 1)) := by
  have sort := sortTree_net (compare_exchange F n) j
  have test := adjacent_net (compare_lt F n) j
  have ok (x : Val (tree j (word n))) :
      adjacent j (sortTree j x) = decide (flatten j x).Nodup := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, adjacent_iff _ _ (sortTree_sorted j x), (sortTree_perm j x).nodup_iff]
  have hn := sort.comp test
  simp only [ok] at hn
  apply hn.mono
  rw [wd_word]
  ring_nf
  omega

end OAI.LinearAlgebra.MatrixExponent
end
