import OAI.LinearAlgebra.MatrixExponent.BitonicSort
import OAI.LinearAlgebra.MatrixExponent.FunctionNetwork
import Mathlib.Tactic.Ring

/-!
# Trivalent realization of Batcher's sorting network

Splitting applies one layer of comparators to corresponding records.
Merging adds at most one such layer per level. Sorting merges at every level.
The cost includes identities on single records. Reversals and the
permutations between layers only relabel ports.
-/

namespace OAI.LinearAlgebra.MatrixExponent

private theorem rewire_reverseTree (w : ℕ) (a : Wire) :
    Rewire (tree w a) (tree w a) (reverseTree w) := by
  induction w with
  | zero => exact Rewire.id a
  | succ w ih => exact (Rewire.swap _ _).comp (ih.par ih)

variable {F : Type} [Field F] {a : Wire} [LinearOrder (Val a)] {k : ℕ}
    (h : DNet F (.pair a a) (.pair a a) (fun x => (min x.1 x.2, max x.1 x.2)) k)

include h

private theorem splitTree_net (w : ℕ) :
    DNet F (tree (w + 1) a) (tree (w + 1) a) (splitTree w) (2 ^ w * k) := by
  induction w with
  | zero => rw [pow_zero, one_mul]; exact h
  | succ w ih =>
    have hm := Rewire.middle (tree w a) (tree w a) (tree w a) (tree w a)
    rw [show 2 ^ (w + 1) * k = 2 ^ w * k + 2 ^ w * k by ring]
    exact ((ih.par ih).pre hm).post hm

private theorem mergeTree_net (w : ℕ) :
    DNet F (tree w a) (tree w a) (mergeTree w) (2 ^ w * (w * k + wd a)) := by
  induction w with
  | zero =>
    rw [pow_zero, one_mul, zero_mul, zero_add]
    exact DNet.id F a
  | succ w ih =>
    refine ((splitTree_net h w).comp (ih.par ih)).mono ?_
    ring_nf
    omega

theorem sortTree_net (w : ℕ) :
    DNet F (tree w a) (tree w a) (sortTree w) (2 ^ w * (w + 1) ^ 2 * (k + wd a)) := by
  induction w with
  | zero => exact (DNet.id F a).mono (by simp)
  | succ w ih =>
    have hp := ih.par (ih.post (rewire_reverseTree w a))
    refine (hp.comp (mergeTree_net h (w + 1))).mono ?_
    ring_nf
    omega

end OAI.LinearAlgebra.MatrixExponent
