import OAI.Computability.NearSquareRoot.PhysicalWalshSwapGeometry
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapPrefix

/-! # Computing the three headers of a wide Walsh slot swap

The small descriptor specifies the dimensions in binary and the bit-field
widths in unary. Only the record packing and unpacking commands require
numerically large tally rulers. Their lengths fit in the padded lane volume.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.SlotSwap.Rulers

open IntegerMultiplication Code Strip Carry Staff PhysicalWalsh Space

variable {A : ℕ} (D W : ℕ) (i j : Fin A)

private abbrev layout (s : Shape) := geometry W i j s (reserve D A s)
private abbrev tail (s : Shape) := stride i j s (reserve D A s)

def packHeader (s : Shape) :=
  (tally (layout D W i j s).grid.count,tally (wordWidth i j s (reserve D A s)))

def unpackHeader (s : Shape) :=
  (tally ((layout D W i j s).grid.count * tail D i j s),tally (2*(s.w+1)))

private theorem countFigure : Figure (Header.regime A) (fun s => (layout D W i j s).grid.count) := by
  have hd := geometry_has (W:=W) D i j
  have p : Realizes (Header.regime A) (fun s => (layout D W i j s).pre) := hd.ez Easy.fst
  have g : Realizes (Header.regime A) (fun s => (layout D W i j s).gap) := hd.ez (Easy.snd.compose Easy.fst)
  have n : Realizes (Header.regime A) (fun s => (layout D W i j s).wing) := hd.ez (Easy.snd.compose Easy.snd)
  simp_rw [geometry_count]
  exact (Figure.natural 2).repeated (((p.plus n).plus g).plus n)

private theorem strideFigure : Figure (Header.regime A) (tail D i j) := by
  have hA : 1 ≤ A := by have := i.isLt; omega
  have L := Header.childBits A hA
  have b := ((Realizes.fix (A-1-max i.val j.val)).times L).plus (reserve_realizes D A hA)
  exact ((Figure.natural 2).repeated b).multiplied (Header.suff A)

private theorem recordFigure : Figure (Header.regime A) (fun s => 2*(s.w+1)) := by
  have hd : (Header.regime A).Has (Header.wire A) := (Header.regime A).self
  have w : Realizes (Header.regime A) (fun s => s.w+1) := hd.ez (Easy.fst.compose (Easy.snd.compose Easy.snd))
  exact (Figure.natural 2).multiplied (Figure.of_spoken w)

private theorem packMint : Mint (Header.regime A) (packHeader D W i j) :=
  (Mint.tally (countFigure D W i j)).pair (Mint.tally ((strideFigure D i j).multiplied recordFigure))

private theorem unpackMint : Mint (Header.regime A) (unpackHeader D W i j) :=
  (Mint.tally ((countFigure D W i j).multiplied (strideFigure D i j))).pair (Mint.tally recordFigure)

private theorem payload_bound (ne : i ≠ j) (s : Shape) (pos : 0 < s.level) (d : ℕ) :
    (layout D W i j s).grid.count * tail D i j s*(2*(s.w+1)) ≤ 4*allowance A d s := by
  have total : (layout D W i j s).grid.count * tail D i j s = SwapPrefix.paddedSize A W s :=
    volume_eq i j ne s pos _ (min_le_left ..)
  have h := (SwapPrefix.paddedSize_le A W s).trans
    (Nat.mul_le_mul_left 2 (SwapPrefix.length_le_count A W s))
  have lower : count A s * (s.w+1) ≤ allowance A d s :=
    (Nat.mul_le_mul (Nat.le_succ _) (by omega : s.w+1 ≤ grow A s.level+s.w+1)).trans (Nat.le_add_right ..)
  rw [total]
  have expanded := Nat.mul_le_mul_right (2*(s.w+1)) h
  calc
    _ ≤ _ := expanded
    _ = 4*(count A s * (s.w+1)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 4 lower

private theorem header_sizes (ne : i ≠ j) (s : Shape) (pos : 0 < s.level) (d : ℕ) :
    size (packHeader D W i j s) ≤ 16*allowance A d s + 3 ∧
      size (unpackHeader D W i j s) ≤ 16*allowance A d s + 3 := by
  let n := (layout D W i j s).grid.count
  let b := tail D i j s
  let m := 2*(s.w+1)
  have hn : 0 < n := by dsimp only [n]; rw [geometry_count]; positivity
  have hb : 0 < b := Nat.mul_pos (Nat.two_pow_pos _) s.suff_pos
  have hm : 0 < m := by dsimp [m]; omega
  have cap : n*b*m ≤ 4*allowance A d s := payload_bound D W i j ne s pos d
  have n_cap := (Nat.le_mul_of_pos_right n hb).trans ((Nat.le_mul_of_pos_right (n*b) hm).trans cap)
  have packWidth : b*m ≤ (n*b)*m :=
    (Nat.le_mul_of_pos_left (b*m) hn).trans_eq (Nat.mul_assoc n b m).symm
  have cells := Nat.le_mul_of_pos_right (n*b) hm
  have word := Nat.le_mul_of_pos_left m (Nat.mul_pos hn hb)
  change size (tally n,tally (b*m)) ≤ _ ∧ size (tally (n*b),tally m) ≤ _
  simp only [size_prod,size_tally,tally_length]; omega

private theorem mint_bounded {Z I : Type} [Codec Z] {emit : Shape → Z} (mint : Mint (Header.regime A) emit)
    (s : I → Shape) (C : ℕ) (fits : ∀ t d, size (emit (s t)) ≤ C*(allowance A d (s t)+1)) :
    ∃ d, let B t := allowance A d (s t)
      BoundedTask B B (fun t => send (Header.wire A (s t))) (fun t => send (emit (s t))) := by
  obtain ⟨d,K,raw⟩ := mint.bounded
  refine ⟨d,(raw.on s).bound (K+C+1) (K+C+1) ?_ ?_⟩ <;> intro t
  all_goals
    have hp : K*(Header.scale A (s t)+1)^d ≤ K*allowance A d (s t) :=
      Nat.mul_le_mul_left K (Nat.le_add_left ..)
    have := fits t d
    change K*(Header.scale A (s t)+1)^d + size (emit (s t)) + 1 ≤ (K+C+1)*(allowance A d (s t)+1)
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul] at *
    omega

variable {I : Type} (s : I → Shape)

/-- Emit the row count and packed bit width consumed by the packing pass. -/
theorem pack_bounded (ne : i ≠ j) (pos : ∀ t, 0 < (s t).level) : ∃ d,
    let B t := allowance A d (s t)
    BoundedTask B B (fun t => send (Header.wire A (s t))) (fun t => send (packHeader D W i j (s t))) :=
  mint_bounded (packMint D W i j) s 16 (fun t d => by
    have h := (header_sizes D W i j ne (s t) (pos t) d).1; omega)

/-- Emit the three unary geometry widths consumed by the rectangular program. -/
theorem rect_bounded : ∃ d, let B t := allowance A d (s t)
    BoundedTask B B (fun t => send (Header.wire A (s t))) (fun t => send ((geometry W i j (s t) (reserve D A (s t))).header)) := by
  obtain ⟨cost,poly,run⟩ := geometry_has (W:=W) D i j
  obtain ⟨d,C,h⟩ := (Header.regime A).gauge.add poly
  refine ⟨d,((BoundedTask.of_time run).on s).bound (C+1) (C+1) ?_ ?_⟩ <;> intro t
  all_goals
    have small := h (s t)
    change size (Header.wire A (s t))+cost (s t) ≤ C*(Header.scale A (s t)+1)^d at small
    have cap := Nat.mul_le_mul_left C
      (show (Header.scale A (s t)+1)^d ≤ allowance A d (s t) from Nat.le_add_left ..)
  · change cost (s t)+1 ≤ (C+1)*(allowance A d (s t)+1)
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]; omega
  · change size (Header.wire A (s t))+cost (s t)+1 ≤ (C+1)*(allowance A d (s t)+1)
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]; omega

/-- Emit the original record count and bit width consumed by the unpacking pass. -/
theorem unpack_bounded (ne : i ≠ j) (pos : ∀ t, 0 < (s t).level) : ∃ d,
    let B t := allowance A d (s t)
    BoundedTask B B (fun t => send (Header.wire A (s t))) (fun t => send (unpackHeader D W i j (s t))) :=
  mint_bounded (unpackMint D W i j) s 16 (fun t d => by
    have h := (header_sizes D W i j ne (s t) (pos t) d).2; omega)

end PhysicalWalshNode.SlotSwap.Rulers

end NearSquareRoot
end Computability
end OAI
