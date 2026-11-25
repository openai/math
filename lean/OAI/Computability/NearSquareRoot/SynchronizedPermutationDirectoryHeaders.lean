import OAI.Computability.NearSquareRoot.PrecisionGridInstruction
import OAI.Computability.NearSquareRoot.SynchronizedPhysicalRouting

/-! # Scalar dimensions for the scheduled block permutation tables

Each group is stored in the CRT tape's low-field-first order. The temporary
unary products inspect at most seven fields, including on malformed input.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord.PermHeader

open IntegerMultiplication Code Staff Strip Carry BoxFin SynchronizedBlocks

abbrev Axis := Tally × Tally
abbrev Block := List Axis
abbrev AxisFields := (Tally × Tally) × (Tally × Tally) × (Tally × Tally)

/-- Four through seven axis headers, with any final extra fields in the last block. -/
def groups (u : Tally) : List Block := group (BoxProgram.encoded u)

theorem groups_poly : Poly groups := BoxProgram.encoded_poly.compose group_poly

def block (box : List (ℕ × ℕ)) (j : Fin (box.length / 4)) : Block :=
  List.ofFn fun i : Fin (count j) => (tally (box.get (axis j i)).1, tally (modulus box (axis j i)))

theorem groups_eq (k : ℕ) : groups (tally k) = List.ofFn (block (CoprimeBox.box k)) := by
  let b := CoprimeBox.box k
  have h : BoxProgram.encoded (tally k) = List.ofFn (fun i : Fin b.length =>
      (tally (b.get i).1, tally (modulus b i))) := by
    apply List.ext_getElem <;> simp [BoxProgram.encoded, b, modulus]
  rw [groups, h, group_eq]
  rfl

private def input (X : Type) [Codec X] : Regime X := ⟨Code.size,send,Dom.base _⟩

private theorem param {X : Type} [Codec X] (f : X → Tally) (h : Poly f) :
    Realizes (input X) (fun x => (f x).length) := by
  change Poly (fun x : X => tally (f x).length)
  simpa only [recover_tally] using h

/-- Product of the first seven padded extents. -/
def volume (bs : Block) : Tally := tally ((((bs.map CRTTable.padded).take 7).map List.length).prod)

theorem volume_poly : Poly volume := by
  have hh : (input Block).Has (fun bs => bs.map CRTTable.padded) :=
    Poly.maps _ CRTTable.padded_poly
  exact PhaseTable.boundedProduct 7 hh

def width (bs : Block) : Tally := tally (Nat.clog 2 (volume bs).length)

theorem width_poly : Poly width := (Figure.of_spoken (param volume volume_poly)).short_log

/-- Extent of the fields below the distinguished Walsh bit in the first axis. -/
def low (bs : Block) : Tally := tally ((CRTTable.padded (bs.headD default)).length / 2)

theorem low_poly : Poly low :=
  (param _ ((Iter.leader (default : Axis)).poly.compose CRTTable.padded_poly)).dividing (.fix 2)

private def radius (a : Tally) : Tally := tally (2 ^ paddedLog a.length)

private theorem radius_poly : Poly radius := by
  have a : Realizes (input Tally) (fun t : Tally => t.length) := param id Poly.identity
  have k : Realizes (input Tally) (fun t : Tally => paddedLog t.length) := paddedLog_poly
  have bound := (Realizes.fix 4).times (a.plus (.fix 1))
  apply ((Figure.natural 2).repeated k).pay ((diameter _ bound).mono ?_)
  intro t
  by_cases h : 0 < t.length
  · have := doubled_pad_lt h
    omega
  · have he : t.length = 0 := by omega
    rw [he]
    decide

/-- Occupied order and padded radix, lower-field stride and Fourier exponent,
then Fourier radius and number of spectator rows. -/
def fields (p : Block × Tally) : AxisFields :=
  let a := Iter.pick (default : Axis) p
  let d := CRTTable.padded a
  ((a.2,d),(volume (p.1.take p.2.length), tally (paddedLog a.2.length)),
    (radius a.2, tally ((volume p.1).length / d.length)))

theorem fields_poly : Poly fields := by
  let a := Iter.pick (default : Axis)
  have A : Poly (fun p : Block × Tally => (a p).2) := (Iter.facile _).sndCompose.poly
  have D : Poly (fun p : Block × Tally => CRTTable.padded (a p)) :=
    (Iter.facile _).poly.compose CRTTable.padded_poly
  have take : Poly (fun p : Block × Tally => p.1.take p.2.length) :=
    ((Easy.snd.pair Easy.fst).compose (easy_cut Easy.identity)).fstCompose.poly
  have quot := (param _ (Easy.fst.poly.compose volume_poly)).dividing (param _ D)
  exact (A.pair D).pair (((take.compose volume_poly).pair (A.compose paddedLog_poly)).pair
    ((A.compose radius_poly).pair quot))

variable {k l : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k l box) (j : Fin (box.length/4))

include hb

private theorem radices_eq : (block box j).map CRTTable.padded =
    List.ofFn (fun i : Fin (count j) => tally (blockFieldRadix box j i)) := by
  rw [block, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply, CRTTable.padded, modulus, blockFieldRadix, tally_length,
    min_eq_left (CRTTable.axis_half_full hb (List.get_mem box (axis j i)))]

theorem volume_eq : volume (block box j) = tally (blockRadix box j) := by
  rw [volume,radices_eq hb j,List.take_of_length_le (by simpa using (count_bounds j).2)]
  simp [List.map_ofFn,Function.comp_def,Fin.prod_ofFn,blockFieldRadix,blockRadix]

theorem volume_eq_pow : volume (block box j) = tally (2 ^ physicalWidth (box := box) j) := by
  rw [volume_eq hb, blockRadix, Finset.prod_pow_eq_pow_sum]
  rfl

theorem width_eq : width (block box j) = tally (physicalWidth (box := box) j) := by
  simp [width, volume_eq_pow hb j, Nat.clog_pow 2 _ (by decide)]

theorem low_eq : low (block box j) = tally (lowRadix (box := box) j) := by
  let f := firstAxis j
  have hd : (block box j).headD default = (tally (box.get (axis j f)).1, tally (modulus box (axis j f))) := by
    exact Iter.entry _ f _
  have he := firstRadix_eq hb j
  simp only [low, hd, CRTTable.padded, modulus, tally_length, min_eq_left (CRTTable.axis_half_full hb (List.get_mem box (axis j f)))]
  change tally (blockFieldRadix box j f / 2) = _
  rw [he, Nat.mul_div_cancel _ (by decide)]

variable [∀ i, NeZero (modulus box i)]

theorem fields_eq (i : Fin (count j)) : fields (block box j, tally i.val) =
    ((tally (blockModulus j i), tally (blockFieldRadix box j i)),
      (tally (CRT.«prefix» (blockFieldRadix box j) i), tally (paddedLog (blockModulus j i))),
      (tally (2 ^ paddedLog (blockModulus j i)), tally (fiberCount (blockModulus j) (blockPadding j) i))) := by
  let d := blockFieldRadix box j
  have elt := Iter.entry (fun u : Fin (count j) => (tally (box.get (axis j u)).1,
    tally (modulus box (axis j u)))) i (default : Axis)
  have pd : CRTTable.padded (tally (box.get (axis j i)).1, tally (modulus box (axis j i))) =
      tally (d i) := by
    simp only [CRTTable.padded, d, blockFieldRadix, modulus, tally_length,
      min_eq_left (CRTTable.axis_half_full hb (List.get_mem box (axis j i)))]
  have left : volume ((block box j).take i.val) = tally (CRT.«prefix» d i) := by
    have hlen : (((block box j).take i.val).map CRTTable.padded).length ≤ 7 := by
      rw [List.length_map]
      exact (List.length_take_le ..).trans (i.isLt.le.trans (count_bounds j).2)
    rw [volume, List.take_of_length_le hlen]
    simp only [List.map_take, radices_eq hb j, List.map_ofFn, Function.comp_def, tally_length, FieldSplit.prefix_take, d]
  rw [fields]
  change (let a := Iter.pick default (block box j,tally i.val); _) = _
  rw [show Iter.pick default (block box j,tally i.val) = _ from elt]
  simp only [pd,tally_length,left,volume_eq hb j,radius]
  rw [show fiberCount (blockModulus j) (blockPadding j) i = blockRadix box j / d i from
    PhaseTable.blockSpectatorQuotient hb j i]

end ShortFourier.BatchWord.PermHeader

end NearSquareRoot
end Computability
end OAI
