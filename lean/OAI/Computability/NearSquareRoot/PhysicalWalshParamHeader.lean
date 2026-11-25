import OAI.Computability.NearSquareRoot.PhysicalWalshPaddingHeader

/-! # Padding and depth from runtime template parameters

The same command computes the logarithm and the binary padding count when
the radix and fanout vary as parts of the physical descriptor.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.ParamHeader

open IntegerMultiplication Code Carry Staff Strip

variable {I : Type} {r : Regime I} {a w k s n : I → ℕ}

theorem log_realizes (ha : Realizes r a) (hA : ∀ i, 1 < a i) (hn : Realizes r n) :
    Realizes r (fun i => Nat.log (a i) (n i)) := by
  let addOne := (floor_ n hn).plus (Realizes.fix 1)
  have pow := (Figure.of_spoken (landing n hn a ha)).repeated addOne
  have pred := (Figure.of_spoken (landing n hn n hn)).compare_ pow
  have record := (Realizes.fix 0).select (Realizes.fix 1) pred
  have test (i : I) (j : Fin (n i)) : (if n i < (a i)^(j.val+1) then 0 else 1) =
      (if j.val < Nat.log (a i) (n i) then 1 else 0) := by
    by_cases h : n i < (a i)^(j.val+1)
    · have t := Nat.log_lt_of_lt_pow' (by omega : j.val+1 ≠ 0) h
      simp [h, show ¬j.val < Nat.log (a i) (n i) by omega]
    · have t := Nat.le_log_of_pow_le (hA i) (le_of_not_gt h)
      simp [h, show j.val < Nat.log (a i) (n i) by omega]
  have rows : r.Has (fun i => List.ofFn
      (fun j : Fin (n i) => tally (if n i < (a i)^(j.val+1) then 0 else 1))) :=
    harvest n hn _ record
  simpa only [Function.comp_def,test,PaddingHeader.markedPrefix _ _ (Nat.log_le_self _ _),Realizes,box]
    using rows.ez Easy.flatten

theorem depth_realizes (ha : Realizes r a) (hA : ∀ i, 1 < a i) (hs : Realizes r s) :
    Realizes r (fun i => WalshPadding.depth (a i) (s i)) :=
  log_realizes ha hA (hs.dividing (Realizes.fix 2))

theorem paddedRows_figure (ha : Realizes r a) (hA : ∀ i, 1 < a i)
    (hw : Realizes r w) (hk : Realizes r k) (hs : Realizes r s) :
    Figure r (fun i => WalshPadding.paddedRows (2^(k i-s i)) (w i) (WalshPadding.depth (a i) (s i))) := by
  let q := PaddingHeader.rows_figure hk hs
  let m := (Figure.of_spoken hw).repeated (depth_realizes ha hA hs)
  have q' := m.multiplied (((q.added m).subtracted (Figure.natural 1)).quotients m)
  simpa only [WalshPadding.paddedRows, Nat.ceilDiv_eq_add_pred_div] using q'

theorem extra_figure (ha : Realizes r a) (hA : ∀ i, 1 < a i)
    (hw : Realizes r w) (hk : Realizes r k) (hs : Realizes r s) :
    Figure r (fun i => PaddingHeader.extra (a i) (w i) (k i) (s i)) :=
  ((paddedRows_figure ha hA hw hk hs).subtracted (PaddingHeader.rows_figure hk hs)).multiplied
    (PaddingHeader.rowSize_figure hs)

end PhysicalWalsh.ParamHeader

end NearSquareRoot
end Computability
end OAI
