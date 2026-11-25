import OAI.Computability.NearSquareRoot.CRTTableField
import OAI.Computability.NearSquareRoot.CRTTableInputRows
import OAI.Computability.IntegerMultiplication.Bits.Word
import OAI.Computability.IntegerMultiplication.Code.Iter

/-! # Parsing the control setting for a triangular CRT table

Each axis descriptor contains a bit width and an actual modulus, both in
unary. A control setting concatenates MSF fields in decreasing axis order.
The polynomial-time parser splits these fields, bounds every decoded tally by
its modulus, and reports whether all fields are occupied. All program bounds
include the cost of constructing the unary coordinates.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication IntegerMultiplication.Code

abbrev ControlAxis := Tally × Tally
private abbrev ParseState := List Bool × Bool × List Tally

private def fieldStep (p : ParseState × ControlAxis) : ParseState :=
  let parts := cutLists (p.2.1, p.1.1)
  let v := fieldDecode (p.2.2, parts.1)
  (parts.2, (p.1.2.1 && decide (parts.1.length = p.2.1.length)) &&
    Iter.small (v, p.2.2), v :: p.1.2.2)

private theorem fieldStep_poly : Poly fieldStep := by
  let W := ParseState × ControlAxis
  let cut (p : W) := cutLists (p.2.1, p.1.1)
  have hc : Poly cut := (easy_cut (g := fun p : W => (p.2.1, p.1.1)) (by fun_prop)).poly
  let val (p : W) := fieldDecode (p.2.2, (cut p).1)
  have hv : Poly val := ((show Poly (fun p : W => p.2.2) by fun_prop).pair hc.fstCompose).compose
    fieldDecode_poly
  have hfull := (hc.fstCompose.pair (show Poly (fun p : W => p.2.1) by fun_prop)).compose
    (Iter.linked (X := Bool) (Y := Unit)).poly
  have hin := (hv.pair (show Poly (fun p : W => p.2.2) by fun_prop)).compose Iter.small_easy.poly
  have both : Poly (fun q : Bool × Bool => q.1 && q.2) := (Easy.finite _).poly
  have ho := (((show Poly (fun p : W => p.1.2.1) by fun_prop).pair hfull).compose both).pair hin
  exact hc.sndCompose.pair ((ho.compose both).pair
    ((hv.pair (show Poly (fun p : W => p.1.2.2) by fun_prop)).compose Poly.cons))

private theorem fieldStep_size (s : ParseState) (a : ControlAxis) :
    size (fieldStep (s, a)) ≤ size s + size a := by
  simp only [fieldStep, cutLists, size_prod, size_cons, size_bit, size_tally, Bits.size_word,
    List.length_drop, fieldDecode_length]
  omega

private theorem fieldsFold_poly :
    Poly (fun i : List ControlAxis × ParseState =>
      i.1.foldl (fun s a => fieldStep (s, a)) i.2) := by
  apply Poly.fold_left fieldStep_poly 1 1
  intro i l h
  have bound (s : ParseState) (axes : List ControlAxis) :
      size (axes.foldl (fun s a => fieldStep (s, a)) s) ≤ size s + size axes := by
    induction axes generalizing s with
    | nil => simp
    | cons a axes ih =>
      simp only [List.foldl_cons, size_cons]
      exact (ih _).trans (by have := fieldStep_size s a; omega)
  have hp := bound i.2 l
  obtain ⟨r,hr⟩ := h
  have hs := size_append_right l r
  rw [hr] at hs
  have hn := size_pos r
  change _ ≤ 1 * ((size i.1 + size i.2 + 1) + 1)^1
  simp only [one_mul, pow_one]
  omega

/-- Descriptors in stream order. The second output stores coordinates in that order. -/
def parseControl (i : List ControlAxis × List Bool) : Bool × List Tally :=
  let s := i.1.foldl (fun s a => fieldStep (s, a)) (i.2, true, [])
  (s.2.1 && decide (s.1.length = 0), s.2.2.reverse)

theorem parseControl_poly : Poly parseControl := by
  have hinit : Poly (fun i : List ControlAxis × List Bool => (i.1, i.2, true, ([] : List Tally))) := by
    fun_prop
  have h := hinit.compose fieldsFold_poly
  have he := (h.fstCompose.pair (IntegerMultiplication.Code.Poly.const (X := List ControlAxis × List Bool) ([] : Tally))).compose (Iter.linked (X := Bool) (Y := Unit)).poly
  exact ((h.sndCompose.fstCompose.pair he).compose (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly).pair
    (Poly.rev h.sndCompose.sndCompose)

private theorem fieldsFold_correct
    (fs : List (ControlAxis × List Bool)) (width : ∀ x ∈ fs, x.2.length = x.1.1.length)
    (suffix : List Bool) (ok : Bool) (out : List Tally) :
    (fs.map Prod.fst).foldl (fun s a => fieldStep (s, a))
        ((fs.map Prod.snd).flatten ++ suffix, ok, out) =
      (suffix, ok && fs.all (fun x => decide (bitValue x.2 < x.1.2.length)),
        (fs.map (fun x => fieldDecode (x.1.2, x.2))).reverse ++ out) := by
  induction fs generalizing ok out with
  | nil => simp
  | cons x fs ih =>
    have hx := width x (by simp)
    have ht := ih (fun z hz => width z (by simp [hz]))
    have e : Iter.small (fieldDecode (x.1.2, x.2), x.1.2) = decide (bitValue x.2 < x.1.2.length) := by
      simp [Iter.small, min_lt_iff]
    have hstep : fieldStep ((x.2 ++ ((fs.map Prod.snd).flatten ++ suffix), ok, out), x.1) =
        ((fs.map Prod.snd).flatten ++ suffix, ok && decide (bitValue x.2 < x.1.2.length),
          fieldDecode (x.1.2, x.2) :: out) := by
      simp [fieldStep, cutLists, ← hx, e]
    simp only [List.map_cons, List.flatten_cons, List.append_assoc, List.foldl_cons, hstep, ht,
      List.all_cons, Bool.and_assoc, List.reverse_cons, List.singleton_append]

/-- On an actual concatenation of whole fields the flag tests every modulus.
The parser returns the exact coordinate whenever that field is valid. -/
theorem parseControl_correct (fs : List (ControlAxis × List Bool))
    (width : ∀ x ∈ fs, x.2.length = x.1.1.length) :
    parseControl (fs.map Prod.fst, (fs.map Prod.snd).flatten) =
      (fs.all (fun x => decide (bitValue x.2 < x.1.2.length)),
        fs.map (fun x => fieldDecode (x.1.2, x.2))) := by
  simpa [parseControl] using congrArg
    (fun s : ParseState => (s.2.1 && decide (s.1.length = 0), s.2.2.reverse))
    (fieldsFold_correct fs width [] true [])

/-- Ascending axis order for the triangular solve. Axis 1 varies fastest in
the address, so its field is at the low end of the MSF stream. -/
def ascendingControl (i : List ControlAxis × List Bool) : Bool × List Tally :=
  let z := parseControl (i.1.reverse, i.2)
  (z.1, z.2.reverse)

theorem ascendingControl_poly : Poly ascendingControl := by
  have h := (show Poly (fun i : List ControlAxis × List Bool => (i.1.reverse, i.2)) by fun_prop).compose
    parseControl_poly
  exact h.fstCompose.pair (Poly.rev h.sndCompose)

theorem ascendingControl_correct (fs : List (ControlAxis × List Bool))
    (width : ∀ x ∈ fs, x.2.length = x.1.1.length) :
    ascendingControl (fs.map Prod.fst, (fs.reverse.map Prod.snd).flatten) =
      (fs.all (fun x => decide (bitValue x.2 < x.1.2.length)),
        fs.map (fun x => fieldDecode (x.1.2, x.2))) := by
  have h := parseControl_correct fs.reverse (fun x hx => width x (by simpa using hx))
  unfold ascendingControl
  rw [← List.map_reverse, h]
  simp

/-- Left and right descriptors in ascending axis order, one coefficient queue
per axis, and the raw MSF string for this node's complete control setting. -/
abbrev ControlPacket :=
  List ControlAxis × List ControlAxis × List (List Tally) × List Bool

/-- Prepare the rows for triangular substitution. The flag is false for an
invalid control; the target-table generator then selects identity rotations. -/
def prepareRows (i : ControlPacket) : Bool × List (Tally × Tally × List Tally) :=
  let parsed := ascendingControl (i.1, i.2.2.2)
  (parsed.1, rawRows (i.1, i.2.1, parsed.2, i.2.2.1))

theorem prepareRows_poly : Poly prepareRows := by
  have h := (show Poly (fun i : ControlPacket => (i.1, i.2.2.2)) by fun_prop).compose ascendingControl_poly
  have hrow := (show Poly (fun i : ControlPacket => (i.1,i.2.1,
      (ascendingControl (i.1,i.2.2.2)).2,i.2.2.1)) from
    Poly.pair (by fun_prop) (Poly.pair (by fun_prop) (h.sndCompose.pair (by fun_prop))))
  exact h.fstCompose.pair (hrow.compose rawRows_poly)

/-- The exact rows and flag for a control setting encoded by whole fields.
This also identifies the clipped residuals produced on out-of-range settings. -/
theorem prepareRows_correct (fs : List (ControlAxis × List Bool)) (targets : List ControlAxis)
    (cs : List (List Tally)) (width : ∀ x ∈ fs, x.2.length = x.1.1.length) :
    prepareRows (fs.map Prod.fst, targets, cs, (fs.reverse.map Prod.snd).flatten) =
      (fs.all (fun x => decide (bitValue x.2 < x.1.2.length)),
        rawRows (fs.map Prod.fst, targets, fs.map (fun x => fieldDecode (x.1.2,x.2)), cs)) := by
  simp only [prepareRows, ascendingControl_correct fs width]

/-- On the occupied part of the control cube, every initial residual is the
exact decoded coordinate and all target residuals are zero. -/
theorem prepareRows_valid (fs : List (ControlAxis × List Bool)) (targets : List ControlAxis)
    (cs : List (List Tally)) (width : ∀ x ∈ fs, x.2.length = x.1.1.length)
    (valid : ∀ x ∈ fs, bitValue x.2 < x.1.2.length) :
    prepareRows (fs.map Prod.fst, targets, cs, (fs.reverse.map Prod.snd).flatten) =
      (true, rawRows (fs.map Prod.fst, targets, fs.map (fun x => tally (bitValue x.2)), cs)) := by
  rw [prepareRows_correct _ _ _ width]
  have h : fs.all (fun x => decide (bitValue x.2 < x.1.2.length)) = true := by
    simpa using valid
  rw [h]
  have hm : fs.map (fun x => fieldDecode (x.1.2,x.2)) = fs.map (fun x => tally (bitValue x.2)) := by
    apply List.map_congr_left
    intro x hx
    simp [fieldDecode, Nat.min_eq_right (valid x hx).le]
  rw [hm]

end CRTTable

end NearSquareRoot
end Computability
end OAI
