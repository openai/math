import OAI.Computability.NearSquareRoot.PrecisionBlockPhaseRank
import OAI.Computability.NearSquareRoot.SynchronizedBoxBatchProgram
import OAI.Computability.NearSquareRoot.CRTTablePadded

/-! # Extracting a local block field from a phase-table rank

The box header contains unary axis widths and cyclic orders. Its density
bounds each unary padded axis size by twice its order, and every synchronized
block has at most seven axes. Thus local radix products below are produced in
polynomial setup time on these headers.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Carry Staff Strip SynchronizedBlocks BoxFin

variable {I : Type} {s : Regime I}

theorem boundedProduct {xs : I → List Tally} (n : ℕ) (known : s.Has xs) :
    Realizes s (fun i => (((xs i).take n).map List.length).prod) := by
  induction n generalizing xs with
  | zero => simpa using (Realizes.fix (r := s) 1)
  | succ n ih =>
    have head : Realizes s (fun i => ((xs i).headD (tally 1)).length) := by
      simpa only [Realizes, Function.comp_def, Staff.box, recover_tally] using
        known.ez (Iter.leader (tally 1))
    have e : Easy (fun y : List Tally => y.tail) := by
      have h := Easy.listCase (X := Tally) (Y := List Tally) [] Easy.snd
      convert h using 1
      funext y
      cases y <;> rfl
    have tail := ih (xs := fun i => (xs i).tail) (known.ez e)
    convert head.times tail using 1
    funext i
    cases h : xs i <;> simp

/-- Compute the actual padded radix of every field, grouped into the precise
four-to-seven-axis blocks in the synchronized descriptor. -/
theorem groupedRadices {k l : I → ℕ} {b : I → List (ℕ × ℕ)} (hb : ∀ i, BoxShape.Valid (k i) (l i) (b i))
    (header : s.Has (fun i => (b i).map (fun p => (tally p.1, tally p.2)))) :
    s.Has (fun i => List.ofFn (fun j : Fin ((b i).length/4) => List.ofFn
      (fun t : Fin (count j) => tally (2^((b i).get (axis j t)).1)))) := by
  have cells := header.thenDo (Poly.maps _ CRTTable.padded_poly)
  have rows := cells.thenDo (ShortFourier.BatchWord.group_poly (X := Tally))
  convert rows using 1
  funext i
  have cellEq : List.map CRTTable.padded ((b i).map (fun p => (tally p.1, tally p.2))) =
      List.ofFn (fun j => tally (2^((b i).get j).1)) := by
    apply List.ext_getElem
    · simp
    · intro j hj _
      simp only [List.getElem_map, List.getElem_ofFn, List.get_eq_getElem, CRTTable.padded, tally_length]
      rw [min_eq_left (CRTTable.axis_half_full (hb i) (List.getElem_mem (l := b i) (n := j) (by simpa using hj)))]
  rw [cellEq, ShortFourier.BatchWord.group_eq]

/-- Select the active block, compute the product of all preceding local
radices, and read its selected axis radix. The prefix product is the
place value used when extracting the selected field in LSF tape order. -/
theorem blockExtractionRulers {k l : I → ℕ} {b : I → List (ℕ × ℕ)}
    (hb : ∀ i, BoxShape.Valid (k i) (l i) (b i))
    (header : s.Has (fun i => (b i).map (fun p => (tally p.1,tally p.2))))
    (j : ∀ i, Fin ((b i).length/4)) (t : ∀ i, Fin (count (j i)))
    (J : Realizes s (fun i => (j i).val)) (T : Realizes s (fun i => (t i).val)) :
    let rad i (u : Fin (count (j i))) := 2^((b i).get (axis (j i) u)).1
    Realizes s (fun i => ((List.ofFn (rad i)).take (t i).val).prod) ∧
      Realizes s (fun i => rad i (t i)) ∧ Realizes s (fun i => blockRadix (b i) (j i)) := by
  let rad i (u : Fin (count (j i))) := 2^((b i).get (axis (j i) u)).1
  let row i := List.ofFn (fun u => tally (rad i u))
  have rows := groupedRadices hb header
  have block : s.Has row := by
    have h := (Regime.Has.pair rows J).ez (Iter.facile ([] : List Tally))
    simpa only [Realizes, Function.comp_apply, Staff.box, Iter.entry] using h
  have pre : s.Has (fun i => (row i).take (t i).val) := by
    have h := (Regime.Has.pair T block).ez (easy_cut Easy.identity).fstCompose
    simpa [cutLists,Staff.box] using h
  have bound i : (row i).length ≤ 7 := by simpa [row] using (count_bounds (j i)).2
  have all_eq i : (row i).map List.length = List.ofFn (rad i) := by
    simp [row,List.map_ofFn,Function.comp_def]
  refine ⟨?_, ?_, ?_⟩
  · have h := boundedProduct 7 pre
    convert h using 1
    funext i
    have hlen : ((row i).take (t i).val).length ≤ 7 :=
      (List.length_take_le ..).trans ((t i).isLt.le.trans (count_bounds (j i)).2)
    rw [List.take_of_length_le hlen, List.map_take, all_eq]
  · have h := (Regime.Has.pair block T).ez (Iter.facile ([] : Tally))
    change s.Has (fun i => tally (rad i (t i)))
    simpa only [Function.comp_apply, Staff.box, row, Iter.entry] using h
  · have h := boundedProduct 7 block
    convert h using 1
    funext i
    simp [List.take_of_length_le (bound i), all_eq, Fin.prod_ofFn, rad, blockRadix]

/-- The cyclic order read from the same field is the occupied range used by
the borrowing lookup and the short-transform opcode. -/
theorem selectedAxisOrder {b : I → List (ℕ × ℕ)}
    (header : s.Has (fun i => (b i).map (fun p => (tally p.1,tally p.2))))
    (j : ∀ i, Fin ((b i).length/4)) (t : ∀ i, Fin (count (j i)))
    (J : Realizes s (fun i => (j i).val)) (T : Realizes s (fun i => (t i).val)) :
    Realizes s (fun i => ((b i).get (axis (j i) (t i))).2) := by
  have a : Realizes s (fun i => (axis (j i) (t i)).val) := ((Realizes.fix 4).times J).plus T
  have read := (Regime.Has.pair header a).ez (Iter.facile (([],[]) : Tally × Tally))
  have lookup := read.ez Easy.snd
  change s.Has (fun i => tally ((b i).get (axis (j i) (t i))).2)
  convert lookup using 1
  funext i
  change tally ((b i).get (axis (j i) (t i))).2 =
    (Iter.pick (([],[]) : Tally × Tally) ((b i).map (fun p => (tally p.1,tally p.2)), tally (axis (j i) (t i)).val)).2
  rw [Iter.search _ _ _ (by simp), List.getElem_map]
  rfl

/-- The natural row number erases the selected field of radix `a`, and the
column number consists of that field alone. Division, remainder and the
final two arithmetic operations use P192's unary setup routines. -/
theorem splitRankRulers {q p a : I → ℕ} (Q : Realizes s q) (P : Realizes s p)
    (A : Realizes s a) : Realizes s (fun i => q i % p i + p i * (q i / (p i * a i))) ∧
      Realizes s (fun i => (q i / p i) % a i) :=
  ⟨(Q.rem P).plus (P.times (Q.dividing (P.times A))), (Q.dividing P).rem A⟩

end PhaseTable

end NearSquareRoot
end Computability
end OAI
