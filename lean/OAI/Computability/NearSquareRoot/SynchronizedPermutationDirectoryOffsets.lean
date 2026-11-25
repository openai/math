import OAI.Computability.NearSquareRoot.SynchronizedPermutationDirectory
import OAI.Computability.NearSquareRoot.FourierBatchDirectory
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetShape
import Mathlib.Data.Fin.Tuple.Take

/-! # Physical bit positions of the emitted permutation headers

Directory order follows increasing significance of the packed physical blocks.
Within one Beneš word, port zero is the block's most significant bit.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.FieldDirectory

/-- All local most-significant-first ports enumerate the global least-significant-first
bit positions bijectively, for any family of widths with the specified total. -/
def finitePort {d k : ℕ} (w : Fin d → ℕ) (total : ∑ j, w j = k) :
    ((j : Fin d) × Fin (w j)) ≃ Fin k :=
  (Equiv.sigmaCongrRight (fun _ => Fin.revPerm)).trans (finSigmaFinEquiv.trans (finCongr total))

@[simp] theorem finitePort_val {d k : ℕ} (w : Fin d → ℕ) (total : ∑ j, w j = k)
    (j : Fin d) (i : Fin (w j)) : (finitePort w total ⟨j,i⟩).val = position w j i := by
  change (finSigmaFinEquiv (⟨j,i.rev⟩ : (u : Fin d) × Fin (w u))).val = _
  rw [finSigmaFinEquiv_apply]
  change (∑ u : Fin j.val, w (Fin.castLE j.isLt.le u)) + i.rev.val = _
  unfold position
  apply congrArg (_ + ·)
  rw [Fin.val_rev]
  omega

theorem finitePort_injective {d k : ℕ} (w : Fin d → ℕ) (total : ∑ j, w j = k) :
    Function.Injective (finitePort w total) := (finitePort w total).injective

end Benes.FieldDirectory

namespace ShortFourier.BatchWord.PermHeader

open IntegerMultiplication Code Staff Strip Finset BoxFin SynchronizedBlocks

/-- Number of low tape bits preceding a block of the directory. -/
def offsetOf (p : List Block × Tally) : Tally := ((p.1.take p.2.length).map width).flatten

theorem offsetOf_poly : Poly offsetOf := by
  have take : Poly (fun p : List Block × Tally => p.1.take p.2.length) :=
    ((Easy.snd.pair Easy.fst).compose (easy_cut Easy.identity)).fstCompose.poly
  exact (take.compose (Poly.maps _ width_poly)).compose Easy.flatten.poly

/-- Absolute, least-significant-bit-first position of the specified local Beneš port. -/
def portOf (p : (List Block × Tally) × Tally) : Tally :=
  tally ((offsetOf p.1).length + ((width (Iter.pick [] p.1)).length - 1 - p.2.length))

theorem portOf_poly : Poly portOf := by
  let X := (List Block × Tally) × Tally
  let r : Regime X := ⟨Code.size,send,Dom.base _⟩
  have param (f : X → Tally) (h : Poly f) : Realizes r (fun x => (f x).length) := by
    change Poly (fun x : X => tally (f x).length)
    simpa only [recover_tally] using h
  have pos := param _ (Easy.fst.poly.compose offsetOf_poly)
  have wid := param _ ((Easy.fst.compose (Iter.facile ([] : Block))).poly.compose width_poly)
  have idx := param _ Easy.snd.poly
  exact pos.plus ((wid.minused (.fix 1)).minused idx)

variable {k l : ℕ} {b : List (ℕ × ℕ)} (hb : BoxShape.Valid k l b) (hd : 4 ≤ b.length)
  (j : Fin (b.length/4))

private theorem prefixPow {n : ℕ} (w : Fin n → ℕ) (i : Fin n) :
    CRT.«prefix» (fun x => 2^w x) i = 2^(∑ t : Fin i.val, w (Fin.castLE i.isLt.le t)) := by
  rw [FieldSplit.prefix_take, ← Fin.ofFn_take_eq_take_ofFn i.isLt.le, Fin.prod_ofFn]
  change (∏ t : Fin i.val, 2 ^ w (Fin.castLE i.isLt.le t)) = _
  rw [prod_pow_eq_pow_sum]

include hd in
/-- The start determined by the grouped widths agrees with the original low-bit
offset of the first axis. -/
theorem blockOffset_axis :
    blockOffset (box := b) j = BoxFin.offset (axis j (firstAxis j)) := by
  let w (i : Fin b.length) := (b.get i).1
  let r (i : Fin b.length) := 2^w i
  have H := prefix_axis hd r j (firstAxis j)
  have zer : CRT.«prefix» (fun t => r (axis j t)) (firstAxis j) = 1 := by rw [FieldSplit.prefix_take]; rfl
  rw [zer, mul_one] at H
  simp only [r,Finset.prod_pow_eq_pow_sum,prefixPow] at H
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) H.symm

include hb in
theorem offsetOf_eq : offsetOf (List.ofFn (block b),tally j.val) = tally (blockOffset (box := b) j) := by
  apply List.length_injective
  simp only [offsetOf,tally_length,List.length_flatten,List.map_map]
  rw [← Fin.ofFn_take_eq_take_ofFn j.isLt.le,List.map_ofFn,List.sum_ofFn]
  change (∑ i : Fin j.val, (width (block b (Fin.castLE j.isLt.le i))).length) = _
  simp only [width_eq hb,tally_length,blockOffset]

include hb in
theorem portOf_eq (i : ℕ) :
    portOf ((List.ofFn (block b),tally j.val),tally i) =
      tally (blockOffset (box := b) j + (physicalWidth (box := b) j - 1 - i)) := by
  simp only [portOf,Iter.entry,offsetOf_eq hb j,width_eq hb j,tally_length]

include hb hd in
theorem widths_total : (∑ z : Fin (b.length/4), physicalWidth (box := b) z) = k := by
  exact sum_physicalWidth hb hd

include hb hd in
theorem block_interval : blockOffset (box := b) j + physicalWidth (box := b) j ≤ k := by
  rw [← widths_total hb hd]
  have eql : blockOffset (box := b) j = ∑ z ∈ Iio j, physicalWidth (box := b) z := by
    exact (Finset.sum_bij' (fun (z : Fin (b.length/4)) hz => (⟨z.val,show z < j from mem_Iio.mp hz⟩ : Fin j.val))
      (fun z _ => Fin.castLE j.isLt.le z) (fun _ _ => mem_univ _) (fun z _ => mem_Iio.mpr z.isLt)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)).symm
  rw [eql, Nat.add_comm, ← Finset.sum_insert (s := Iio j) (a := j) (by simp)]
  exact Finset.sum_le_sum_of_subset (subset_univ _)

variable [∀ i, NeZero (modulus b i)]

/-- Extracting at the bytecode offset recovers the full local rank, including padding. -/
theorem physicalRank (t : Fin (2^k)) :
    (blockBitRank hb j (regroup hd _ ((recordIndex hb).symm t) j)).val =
      t.val / 2^(offsetOf (List.ofFn (block b),tally j.val)).length %
        2^(width (block b j)).length := by
  rw [offsetOf_eq hb j,width_eq hb j,tally_length,tally_length]
  exact packedRank_extract hb hd t j

/-- Every emitted local port reads exactly the addressed physical bit. -/
theorem physicalPort (t : Fin (2^k)) (i : Fin (physicalWidth (box := b) j)) :
    (packedRecord hb hd t).2 j i =
      t.val.testBit (portOf ((List.ofFn (block b),tally j.val),tally i.val)).length := by
  rw [portOf_eq hb j,tally_length]
  exact packedRecord_port hb hd t j i

include hb hd in
omit [∀ i, NeZero (modulus b i)] in
/-- The port index lies within the global address, even in the longer final group. -/
theorem portOf_lt (i : Fin (physicalWidth (box := b) j)) :
    (portOf ((List.ofFn (block b),tally j.val),tally i.val)).length < k := by
  have hi := i.isLt
  have hbnd := block_interval hb hd j
  rw [portOf_eq hb j,tally_length]
  omega

/-- Local port values also coincide in the global most-significant-first spelling.
The complement reverses the absolute source position for the array's Beneš word. -/
theorem globalWord_port (t : Fin (2^k)) (i : Fin (physicalWidth (box := b) j)) :
    let p : Fin k := ⟨(portOf ((List.ofFn (block b),tally j.val),tally i.val)).length,portOf_lt hb hd j i⟩
    (packedRecord hb hd t).2 j i = CRTTable.wordEquiv k t p.rev := by
  let p := (portOf ((List.ofFn (block b),tally j.val),tally i.val)).length
  have hlt : p < k := portOf_lt hb hd j i
  let u : Fin k := ⟨p,hlt⟩
  change _ = (Bits.phrase k t.val).reverse[u.rev.val]'(by simpa only [List.length_reverse,Bits.phrase_length] using u.rev.isLt)
  rw [physicalPort hb hd j t i, List.getElem_reverse]
  have H := BoxFin.value_bit (Bits.phrase k t.val) p (by simpa [Bits.phrase_length] using hlt)
  rw [Bits.value_phrase t.isLt] at H
  simpa only [Bits.phrase_length, show k-1-u.rev.val = p by rw [Fin.val_rev];change k-1-(k-(p+1)) = p;omega] using H

/-- The widths in the actual directed row's permutation directory are exactly
the bit widths needed by the controlled-switch plan. -/
theorem rowWidths {k L : ℕ} (valid : BoxShape.Valid k L (CoprimeBox.box k)) (dir : Bool) (stage : Tally) :
    (PermDirectory.directory (dir,tally k,stage)).map Prod.fst =
      List.ofFn (fun j => tally (physicalWidth (box := CoprimeBox.box k) j)) := by
  rw [PermDirectory.directory_widths, groups_eq,List.map_ofFn]
  simp only [Function.comp_def,width_eq valid]

/-- Build the target and control port positions for the chosen block numbers
of a directed row and the chosen Beneš switch stage. -/
def rowPorts (p : PermDirectory.Query × Tally × List Tally) : List Benes.FieldDirectory.Row :=
  Benes.FieldDirectory.batch (((PermDirectory.directory p.1).map Prod.fst,p.2.1),p.2.2)

theorem rowPorts_poly : Poly rowPorts := by
  have W := ((Easy.fst (X := PermDirectory.Query) (Y := Tally × List Tally)).poly.compose PermDirectory.directory_poly).compose (Poly.maps _ Easy.fst.poly)
  exact ((W.pair (Easy.snd.compose Easy.fst).poly).pair (Easy.snd.compose Easy.snd).poly).compose
    Benes.FieldDirectory.batch_poly

theorem rowPorts_eq {k L : ℕ} (valid : BoxShape.Valid k L (CoprimeBox.box k))
    (dir : Bool) (stage : Tally) (switch : ℕ) (sel : List (Fin ((CoprimeBox.box k).length/4))) :
    rowPorts ((dir,tally k,stage),tally switch,sel.map (fun b => tally b.val)) =
      sel.map (fun j => Benes.FieldDirectory.split (tally switch,List.ofFn
        (fun i => tally (Benes.FieldDirectory.position (physicalWidth (box := CoprimeBox.box k)) j i)))) := by
  rw [rowPorts,rowWidths valid, Benes.FieldDirectory.batch_eq]

end ShortFourier.BatchWord.PermHeader

end NearSquareRoot
end Computability
end OAI
