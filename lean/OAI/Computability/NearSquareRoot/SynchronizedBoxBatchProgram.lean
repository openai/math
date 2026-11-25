import OAI.Computability.NearSquareRoot.SynchronizedBatchWord
import OAI.Computability.NearSquareRoot.SynchronizedShortAxis
import OAI.Computability.NearSquareRoot.SynchronizedBlocks
import OAI.Computability.NearSquareRoot.BoxProgram
import OAI.Computability.NearSquareRoot.BoxFin

/-! # Preparing the actual per-block axis/batch words from a unary box width -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry
open IntegerMultiplication.Staff IntegerMultiplication.Strip
open SynchronizedBlocks

private def regime (X : Type) [Codec X] : Regime X := ⟨size, send, Dom.base _⟩

/-- Physical exponent used for the padded Bluestein convolution of an axis. -/
theorem paddedLog_poly : Poly (fun t : Tally => tally (paddedLog t.length)) := by
  have h : Realizes (regime Tally) (fun t : Tally => t.length) := by
    change Poly (fun t : Tally => tally t.length)
    simpa only [recover_tally] using (Code.Poly.identity (X := Tally))
  exact (Figure.of_spoken (((Realizes.fix 2).times h).minused (Realizes.fix 1))).short_log

variable {X : Type}

private def extract (p : List X × Tally) : List X :=
  let rem := p.1.length - 4 * p.2.length
  (p.1.drop (4 * p.2.length)).take (if rem < 8 then rem else 4)

/-- Group four consecutive axes together, assigning the final zero to three
extra axes to the final group. -/
def group (l : List X) : List (List X) :=
  (Iter.lineup (tally (l.length / 4))).map fun j => extract (l,j)

theorem group_poly [Codec X] : Poly (group (X := X)) := by
  let r := regime (List X × Tally)
  have hlen : Realizes r (fun p => p.1.length) := by
    change Poly (fun p : List X × Tally => tally p.1.length)
    have hr := (Easy.ruler (Easy.fst (X := List X) (Y := Tally))).poly
    convert hr using 1
    funext p
    rw [← recover_tally (ruler p.1), ruler_length]
  have hind : Realizes r (fun p => p.2.length) := by
    change Poly (fun p : List X × Tally => tally p.2.length)
    simpa only [recover_tally] using (Easy.snd (X := List X) (Y := Tally)).poly
  have hbegin := (Realizes.fix 4).times hind
  have hrem := hlen.minused hbegin
  have htake := hrem.select (Realizes.fix 4) (hrem.below (Realizes.fix 8))
  have hdrop := (Code.Poly.pair (show Poly (fun p : List X × Tally => tally (4 * p.2.length)) from hbegin)
    Easy.fst.poly).compose (easy_cut Easy.identity).sndCompose.poly
  have he := (Code.Poly.pair (show Poly (fun p : List X × Tally =>
    tally (if p.1.length - 4 * p.2.length < 8 then p.1.length - 4 * p.2.length else 4)) from htake)
    hdrop).compose (easy_cut Easy.identity).fstCompose.poly
  have hq : Realizes (regime (List X)) (fun l : List X => l.length) := by
    change Poly (fun l : List X => tally l.length)
    convert (Easy.ruler (Easy.identity (X := List X))).poly using 1
    funext l
    change tally l.length = ruler l
    rw [← recover_tally (ruler l), ruler_length]
  have hgroups : Poly (fun l : List X => tally (l.length / 4)) := hq.dividing (Realizes.fix 4)
  change Poly (fun l : List X => polyPush extract (l,Iter.lineup (tally (l.length / 4))))
  exact (Code.Poly.identity.pair (hgroups.compose Iter.poly_line)).compose (Poly.push [] [] (by
    change Poly (fun p : List X × Tally => (p.1.drop (4*p.2.length)).take
      (if p.1.length-4*p.2.length < 8 then p.1.length-4*p.2.length else 4))
    simpa only [cutLists, id_eq, tally_length] using he))

/-- The groups are in physical axis order on every input, including an empty list. -/
theorem group_eq {d : ℕ} (x : Fin d → X) :
    group (List.ofFn x) = List.ofFn (fun j : Fin (d/4) => List.ofFn (fun i : Fin (count j) => x (axis j i))) := by
  simp only [group, List.length_ofFn, Iter.lined, List.map_ofFn, Function.comp_def]
  congr 1
  funext j
  have hc : count j = if d - 4 * j.val < 8 then d - 4 * j.val else 4 := by
    have := j.isLt
    unfold SynchronizedBlocks.count
    split_ifs <;> omega
  apply List.ext_getElem
  · simp only [extract, tally_length, List.length_ofFn, List.length_take, List.length_drop, hc]
    split <;> omega
  · intro i hi h
    simp [extract, axis]

/-- On a unary input width, first build the certified box, then its actual
per-block list of placed short-transform opcodes. -/
def boxWords (u : Tally) : List (List Descriptor) :=
  (group ((BoxProgram.encoded u).map (fun x => tally (paddedLog x.2.length)))).map block

theorem boxWords_poly : Poly boxWords :=
  (((BoxProgram.encoded_poly.compose (Poly.maps _ (Easy.snd.poly.compose paddedLog_poly))).compose
    group_poly).compose (Poly.maps _ block_poly))

theorem boxWords_machine :
    PolyTreeMachine id (fun k : ℕ => send (tally k)) (fun k => send (boxWords (tally k))) := by
  have h : Dom id (fun k : ℕ => size (tally k)) := ⟨1, 2, fun k => by simp [size_tally]⟩
  exact polyTreeMachine_of_BT (boxWords_poly.on h) h

/-- On every input the machine's word is the list of all explicitly indexed
local batches from the computed coprime box. -/
theorem boxWords_eq (k : ℕ) :
    boxWords (tally k) = List.ofFn (fun j : Fin ((CoprimeBox.box k).length / 4) =>
      (typed (fun i : Fin (count j) =>
        paddedLog (BoxFin.modulus (CoprimeBox.box k) (axis j i)))).map encode) := by
  let b := CoprimeBox.box k
  have h : (BoxProgram.encoded (tally k)).map (fun x => tally (paddedLog x.2.length)) =
      List.ofFn (fun i : Fin b.length => tally (paddedLog (BoxFin.modulus b i))) := by
    apply List.ext_getElem
    · simp [BoxProgram.encoded, b]
    · intro i hi hj
      simp [BoxProgram.encoded, BoxFin.modulus, b]
  unfold boxWords
  rw [h, group_eq, List.map_ofFn]
  congr 1
  funext j
  exact block_eq_typed _

end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
