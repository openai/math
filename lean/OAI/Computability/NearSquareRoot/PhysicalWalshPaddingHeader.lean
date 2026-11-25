import OAI.Computability.NearSquareRoot.WalshPadding
import OAI.Computability.NearSquareRoot.PhysicalWalshMint

/-! # Uniform computation of the selected-Walsh padding descriptor

A binary power is needed for every candidate exponent tested by the floor
logarithm. The candidate range is controlled by the supplied unary bit count;
even the unsuccessful powers have only polynomially many bits.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.PaddingHeader

open IntegerMultiplication Code Carry Staff Strip

theorem markedPrefix (n m : ℕ) (h : m ≤ n) :
    (List.ofFn (fun i : Fin n => tally (if i.val < m then 1 else 0))).flatten = tally m := by
  induction n generalizing m with
  | zero =>
    have hm : m = 0 := by omega
    simp [hm, tally]
  | succ n ih =>
    rw [List.ofFn_succ]
    cases m with
    | zero => simpa only [List.flatten_cons, Nat.not_lt_zero, ↓reduceIte, tally, List.replicate_zero, List.nil_append]
                using ih 0 (by omega)
    | succ m =>
      have ht := ih m (by omega)
      simp only [List.flatten_cons, Fin.val_zero, Nat.zero_lt_succ, ↓reduceIte,
        Fin.val_succ, Nat.succ_lt_succ_iff, ht, tally_succ]
      rfl

variable {I : Type} {r : Regime I} {k s : I → ℕ}

/-- Polynomial-time evaluation of the floor logarithm in any fixed base,
on every input including zero. -/
theorem log_realizes (A : ℕ) {n : I → ℕ} (hn : Realizes r n) :
    Realizes r (fun i => Nat.log A (n i)) := by
  by_cases hA : 1 < A
  · let addOne := (floor_ n hn).plus (Realizes.fix 1)
    have pow := (Figure.natural A).repeated addOne
    have pred := (Figure.of_spoken (landing n hn n hn)).compare_ pow
    have record := (Realizes.fix 0).select (Realizes.fix 1) pred
    have test (i : I) (j : Fin (n i)) : (if n i < A^(j.val+1) then 0 else 1) =
        (if j.val < Nat.log A (n i) then 1 else 0) := by
      by_cases h : n i < A^(j.val+1)
      · have t := Nat.log_lt_of_lt_pow' (by omega : j.val+1 ≠ 0) h
        simp [h, show ¬j.val < Nat.log A (n i) by omega]
      · have t := Nat.le_log_of_pow_le hA (le_of_not_gt h)
        simp [h, show j.val < Nat.log A (n i) by omega]
    have rows : r.Has (fun i => List.ofFn
        (fun j : Fin (n i) => tally (if n i < A^(j.val+1) then 0 else 1))) :=
      harvest n hn _ record
    have joined := rows.ez Easy.flatten
    simpa only [Function.comp_def, test, markedPrefix _ _ (Nat.log_le_self _ _), Realizes, box]
      using joined
  · simpa only [Nat.log_of_left_le_one (Nat.le_of_not_gt hA)] using
      (Realizes.fix (r := r) 0)

theorem depth_realizes (A : ℕ) (hs : Realizes r s) :
    Realizes r (fun i => WalshPadding.depth A (s i)) :=
  log_realizes A (hs.dividing (Realizes.fix 2))

theorem total_figure (hk : Realizes r k) : Figure r (fun i => 2^(k i)) :=
  (Figure.natural 2).repeated hk

theorem rows_figure (hk : Realizes r k) (hs : Realizes r s) :
    Figure r (fun i => 2^(k i - s i)) := (Figure.natural 2).repeated (hk.minused hs)

theorem rowSize_figure (hs : Realizes r s) : Figure r (fun i => 2^(s i)) := total_figure hs

theorem fanout_figure (A W : ℕ) (hs : Realizes r s) :
    Figure r (fun i => W^WalshPadding.depth A (s i)) :=
  (Figure.natural W).repeated (depth_realizes A hs)

theorem paddedRows_figure (A W : ℕ) (hk : Realizes r k) (hs : Realizes r s) :
    Figure r (fun i => WalshPadding.paddedRows (2^(k i-s i)) W (WalshPadding.depth A (s i))) := by
  let q := rows_figure hk hs
  let m := fanout_figure A W hs
  have q' := m.multiplied (((q.added m).subtracted (Figure.natural 1)).quotients m)
  simpa only [WalshPadding.paddedRows, Nat.ceilDiv_eq_add_pred_div] using q'

/-- Number of full-width record slots appended by the root padding stage. -/
def extra (A W k s : ℕ) : ℕ :=
  (WalshPadding.paddedRows (2^(k-s)) W (WalshPadding.depth A s) - 2^(k-s))*2^s

theorem extra_figure (A W : ℕ) (hk : Realizes r k) (hs : Realizes r s) :
    Figure r (fun i => extra A W (k i) (s i)) :=
  ((paddedRows_figure A W hk hs).subtracted (rows_figure hk hs)).multiplied (rowSize_figure hs)

/-- Compact physical input carrying the total width and selected width in unary.
Every binary field in the descriptor is polynomial-time in their sum. -/
def input : Regime (ℕ × ℕ) where
  scale p := p.1+p.2
  header p := send (tally p.1, tally p.2)
  gauge := by
    refine ⟨1,3,fun p => ?_⟩
    change size (tally p.1,tally p.2) ≤ 3*((p.1+p.2)+1)^1
    simp only [size_prod, size_tally, tally_length, pow_one]
    omega

private theorem given : input.Has (fun p => (tally p.1, tally p.2)) := Regime.self

theorem width : Realizes input Prod.fst := given.ez Easy.fst

theorem selected : Realizes input Prod.snd := given.ez Easy.snd

/-- The compact descriptor emits the exact padding length followed by the
original number of records. Each field is converted from its binary magnitude
to unary with a charge proportional to its emitted length. -/
theorem countsMint (A W : ℕ) :
    Mint input (fun p => (tally (extra A W p.1 p.2), tally (2^p.1))) :=
  (Mint.tally (extra_figure A W width selected)).pair (Mint.tally (total_figure width))

/-- One physical stack command computes the two tallies. The polynomial
depends only on the fixed template parameters and the compact input size. -/
theorem countsTask (A W : ℕ) : ∃ d C : ℕ,
    let cost (p : ℕ × ℕ) := C*(p.1+p.2+1)^d + extra A W p.1 p.2 + 2^p.1
    Space.BoundedTask cost cost (fun p => send (tally p.1,tally p.2))
      (fun p => send (tally (extra A W p.1 p.2), tally (2^p.1))) := by
  obtain ⟨d,C,h⟩ := (countsMint A W).bounded
  refine ⟨d,C,?_⟩
  apply h.bound 4 4 <;> intro p <;>
    simp only [input, size_prod, size_tally, tally_length] <;> omega

end PhysicalWalsh.PaddingHeader

end NearSquareRoot
end Computability
end OAI
