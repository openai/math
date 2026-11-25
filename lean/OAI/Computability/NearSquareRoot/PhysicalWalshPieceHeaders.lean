import OAI.Computability.NearSquareRoot.PhysicalWalshPaddingHeader
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeHeader
import OAI.Computability.NearSquareRoot.PhysicalWalshPieceGeometry

/-! # Physical descriptor list for the selected even Walsh pieces

The outer loop enumerates the base-`A` digit positions; the inner loop
emits one descriptor for each copy of that piece. The offset is measured in
the selected field. Leading spectator rows therefore contain the offset
factor, while the trailing spectator length contains the remaining bits.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication Code Carry Staff Strip PhysicalWalshNode

variable {I : Type} {r : Regime I} {k s w j t : I → ℕ}

theorem digitLength_realizes (A : ℕ) (hA : 1 < A) (hs : Realizes r s) :
    Realizes r (fun i => (walshPieceDigits A (s i)).length) := by
  have half := hs.dividing (Realizes.fix 2)
  have p := (Realizes.fix 0).select ((PaddingHeader.depth_realizes A hs).plus (Realizes.fix 1))
    (half.below (Realizes.fix 1))
  convert p using 1
  funext i
  by_cases h : s i / 2 = 0
  · simp [walshPieceDigits, h]
  · rw [walshPieceDigits, Nat.length_digits _ _ hA h]
    simp [WalshPadding.depth, show ¬s i / 2 < 1 by omega]

theorem digit_realizes (A : ℕ) (hA : 1 < A) (hs : Realizes r s) (hj : Realizes r j) :
    Realizes r (fun i => digit A (s i) (j i)) := by
  have d := (((Figure.of_spoken (hs.dividing (Realizes.fix 2))).quotients
    ((Figure.natural A).repeated hj)).modded (Figure.natural A))
  apply d.pay
  exact (Dom.const _ A).mono fun i => (Nat.mod_lt _ (by omega : 0 < A)).le

private theorem one_header (A W : ℕ) (hW : 0 < W)
    (hk : Realizes r k) (hs : Realizes r s) (hw : Realizes r (fun i => w i+1))
    (hj : Realizes r j) (ht : Realizes r t) (fits : ∀ i, A^(j i) ≤ s i / 2) :
    r.Has (fun i => Header.wire A (shape A W hW (k i) (s i) (w i) (j i) (t i))) := by
  have pow : Realizes r (fun i => A^(j i)) :=
    ((Figure.natural A).repeated hj).pay ((diameter s hs).mono (fun i => (fits i).trans (Nat.div_le_self ..)))
  have bits : Realizes r (fun i => grow A (j i)) := (Realizes.fix 2).times pow
  have off : Realizes r (fun i => offset A (s i) (j i) (t i)) :=
    ((Realizes.fix 2).times ((hs.dividing (Realizes.fix 2)).rem pow)).plus (ht.times bits)
  have pref := (PaddingHeader.paddedRows_figure A W hk hs).multiplied ((Figure.natural 2).repeated off)
  have suff := (Figure.natural 2).repeated ((hs.minused off).minused bits)
  exact (Regime.Has.pair hj (Regime.Has.pair bits hw)).pair ((Header.toBinary pref).pair (Header.toBinary suff))

/-- The same program works for every choice of bit counts and any ambient
regime which supplies their unary encodings. -/
theorem headers_has (A W : ℕ) (hA : 1 < A) (hW : 0 < W)
    (hk : Realizes r k) (hs : Realizes r s) (hw : Realizes r (fun i => w i+1)) :
    r.Has (fun i => (schedule A W hW (k i) (s i) (w i)).map (Header.wire A)) := by
  let len (i : I) := (walshPieceDigits A (s i)).length
  let n (u : Across len) := digit A (s u.1) u.2.val
  have H : Realizes r len := digitLength_realizes A hA hs
  have sj := landing len H s hs
  have jj := floor_ len H
  have D : Realizes (signal len H) n := digit_realizes A hA sj jj
  have term : (signal n D).Has (fun z : Across n =>
      Header.wire A (shape A W hW (k z.1.1) (s z.1.1) (w z.1.1) z.1.2.val z.2.val)) :=
    one_header (w := fun z : Across n => w z.1.1) A W hW
      (landing n D _ (landing len H k hk)) (landing n D _ sj)
      (landing n D _ (landing len H _ hw)) (landing n D _ jj) (floor_ n D)
      (fun z => (Nat.lt_digits_length_iff hA (s z.1.1 / 2)).mp z.1.2.isLt)
  let wire (u : Across len) (t : Fin (n u)) :=
    Header.wire A (shape A W hW (k u.1) (s u.1) (w u.1) u.2.val t.val)
  have byDigit := harvest n D wire term
  have byPosition := harvest len H (fun i j => List.ofFn (wire ⟨i,j⟩)) byDigit
  have both := byPosition.ez Easy.flatten
  simpa only [Function.comp_def, schedule, List.map_flatten, List.map_ofFn, len, n, wire] using both

/-- The conventional compact controller header carries the word width as the
positive unary length `w+1`. -/
def scheduleInput : Regime (ℕ × ℕ × ℕ) where
  scale p := p.1 + p.2.1 + p.2.2
  header p := send ((tally p.1,tally p.2.1),tally (p.2.2+1))
  gauge := by
    refine ⟨1,7,fun p => ?_⟩
    change size ((tally p.1,tally p.2.1),tally (p.2.2+1)) ≤ 7*((p.1+p.2.1+p.2.2)+1)^1
    simp only [size_prod, size_tally, tally_length, pow_one]
    omega

/-- All compact binary spectator headers are emitted in increasing digit
position then copy order by one fixed command at a polynomial cost. -/
theorem headersTask (A W : ℕ) (hA : 1 < A) (hW : 0 < W) : ∃ d C : ℕ,
    let cost (p : ℕ × ℕ × ℕ) := C*(p.1+p.2.1+p.2.2+1)^d
    Space.BoundedTask cost cost (fun p => send ((tally p.1,tally p.2.1),tally (p.2.2+1)))
      (fun p => send ((schedule A W hW p.1 p.2.1 p.2.2).map (Header.wire A))) := by
  have given : scheduleInput.Has (fun p => ((tally p.1,tally p.2.1),tally (p.2.2+1))) := Regime.self
  have hk : Realizes scheduleInput Prod.fst := given.ez (Easy.fst.compose Easy.fst)
  have hs : Realizes scheduleInput (fun p => p.2.1) := given.ez (Easy.fst.compose Easy.snd)
  have hw : Realizes scheduleInput (fun p => p.2.2+1) := given.ez Easy.snd
  obtain ⟨b,hb,task⟩ := headers_has (w := fun p : ℕ × ℕ × ℕ => p.2.2) A W hA hW hk hs hw
  obtain ⟨d,C,bound⟩ := scheduleInput.gauge.add hb
  refine ⟨d,C,(Space.BoundedTask.of_time task).mono (fun p => ?_) (fun p => ?_)⟩
  · exact (Nat.le_add_left (b p) (scheduleInput.header p).count).trans (bound p)
  · exact bound p

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
