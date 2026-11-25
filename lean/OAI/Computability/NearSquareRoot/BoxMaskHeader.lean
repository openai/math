import OAI.Computability.NearSquareRoot.BoxProgram
import OAI.Computability.NearSquareRoot.BoxOrder

/-! # Physically constructing the local validity counts in tape order

The full axes share the padded ceiling `span k`. A tally cut computes each
unused count. The optional remainder axis is fully occupied. Reversing the
result gives the slowest-first directory consumed by the mask generator.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxMaskHeader

open IntegerMultiplication.Code BoxScale BoxParameterTask CoprimeBox

/-- Directory with a pair of unary counts `(valid, unused)` for each axis. -/
def encoded (t : Tally) : List (Tally × Tally) :=
  (BoxOrder.shape (box t.length)).map fun p => (tally p.1, tally p.2)

private theorem full_counts : Poly (fun t : Tally => (fullAxes t.length (count t.length)).map
    fun a => (tally a, tally (span t.length - a))) := by
  let f (p : Tally × Tally) := (p.2, (cutLists p.swap).2)
  have ef : Easy f := Easy.snd.pair (easy_cut Easy.exchange).sndCompose
  have h := (span_poly.pair BoxProgram.full_poly).compose (Poly.push [] [] (f := f) ef.poly)
  simpa only [polyPush, List.map_map, Function.comp_def, f, Prod.swap_prod_mk,
    cutLists, tally_length, tally, List.length_replicate, List.drop_replicate] using h

private theorem tail_counts : Poly (fun t : Tally =>
    if t.length % width t.length = 0 then ([] : List (Tally × Tally))
    else [(tally (2 ^ (t.length % width t.length)), [])]) := by
  let empty : Tally → Bool := List.isEmpty
  have he : Easy empty := by
    have eq : empty = (fun t : Tally => List.casesOn t true (fun _ _ => false)) := by
      funext t; cases t <;> rfl
    rw [eq]; exact Easy.listCase true (Easy.const false)
  have hsing := (remainderSpan_poly.pair (IntegerMultiplication.Code.Poly.const ([] : Tally))).pair
    (IntegerMultiplication.Code.Poly.const ([] : List (Tally × Tally))) |>.compose Poly.cons
  have h := Poly.choose (remainder_poly.compose he.poly) (IntegerMultiplication.Code.Poly.const []) hsing
  convert h using 1
  funext t
  by_cases hz : t.length % width t.length = 0 <;> simp [empty, tally, hz]

theorem encoded_poly : Poly encoded := by
  convert (full_counts.app tail_counts).rev using 1
  funext t
  simp only [encoded, BoxOrder.shape, box, BoxShape.axes, List.map_append, List.map_map,
    List.map_reverse, Function.comp_def, List.reverse_append, span]
  split <;> simp [tally]

end BoxMaskHeader

end NearSquareRoot
end Computability
end OAI
