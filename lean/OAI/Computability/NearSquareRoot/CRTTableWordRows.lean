import OAI.Computability.NearSquareRoot.CRTControlledBenesRaw
import OAI.Computability.IntegerMultiplication.Carry.Shrink

/-! # Converting a unary axis table into a raw Beneš word table -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication IntegerMultiplication.Code

/-- A fixed-width, big-endian bit field produced directly from a unary index. -/
def wordField (q : Tally × Tally) : List Bool :=
  (Bits.resize (q.1, Carry.born q.2.length)).reverse

theorem wordField_easy : Easy wordField := by
  have v := (Easy.snd (X := Tally)).compose Carry.easy_chart
  exact (Bits.easy_resize (Easy.fst.pair v)).compose Easy.reverse

theorem wordField_eq (w n : ℕ) :
    wordField (tally w,tally n) = (Bits.short w n).reverse := by
  apply congrArg List.reverse
  change Bits.sized w (Carry.born (tally n).length) = _
  apply Bits.word_inject
  · simp
  · simp [Bits.sized_low, Carry.birthValue]

private def wordRow (s : (Tally × List Tally) × Tally) : List Bool × List Bool :=
  (wordField (s.1.1,s.2), wordField (s.1.1,Iter.pick [] (s.1.2,s.2)))

private theorem wordRow_easy : Easy wordRow := by
  have h := (show Easy (fun s : (Tally × List Tally) × Tally => (s.1.2,s.2)) by fun_prop).compose
    (Iter.facile ([] : Tally))
  exact ((show Easy (fun s : (Tally × List Tally) × Tally => (s.1.1,s.2)) by fun_prop).compose
    wordField_easy).pair (((show Easy (fun s : (Tally × List Tally) × Tally => s.1.1) by fun_prop).pair h).compose wordField_easy)

/-- The stage compiler consumes a pair of bit addresses for every switch
port. The first member is the input address and the second is the destination
stored at that index by the CRT table generator. -/
def wordRows (q : Tally × List Tally) : Benes.RawTable :=
  polyPush wordRow (q,Iter.lineup (ruler q.2))

theorem wordRows_poly : Poly wordRows := by
  have hs := (Easy.ruler (Easy.snd (X := Tally) (Y := List Tally))).poly.compose Iter.poly_line
  exact (Poly.identity.pair hs).compose (Poly.push ([],[]) [] wordRow_easy.poly)

theorem wordRows_eq (w : ℕ) (t : List Tally) :
    wordRows (tally w,t) = List.ofFn (fun j : Fin t.length =>
      ((Bits.short w j.val).reverse, (Bits.short w (t[j.val]).length).reverse)) := by
  have line : Iter.lineup (ruler t) = List.ofFn fun j : Fin t.length => tally j.val := by
    rw [← recover_tally (ruler t), ruler_length, Iter.lined]
  simp only [wordRows, line, polyPush, List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply, wordRow, Iter.search t [] j.val j.isLt, wordField_eq]
  rw [← recover_tally (t[j.val]), wordField_eq, tally_length]

end CRTTable

end NearSquareRoot
end Computability
end OAI
