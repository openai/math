import OAI.Computability.NearSquareRoot.BoxScanTask
import OAI.Computability.NearSquareRoot.BoxParameterTask
import OAI.Computability.NearSquareRoot.BoxCoprimeTest
import OAI.Computability.NearSquareRoot.PhaseProgramRelease

/-! # Fixed polynomial-time program producing the densely occupied coprime box

The P192 tree-stack task reads the unary address width and returns a list of
pairs of unary words `(padded width, modulus)`. Polynomial setup time allows this
temporary representation even though the data array uses binary addresses.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxProgram

open IntegerMultiplication.Code BoxParameterTask BoxScale CoprimeBox BoxScanTask

/-- Serialize each width and modulus separately, preserving the order of the CRT axes. -/
def encoded (t : Tally) : List (Tally × Tally) :=
  (box t.length).map fun p => (tally p.1, tally p.2)

private theorem lower_poly : Poly (fun t : Tally => tally (span t.length - window t.length)) := by
  have cut := (easy_cut (Easy.identity (X := Tally × Tally))).sndCompose.poly
  have h := (Poly.pair window_poly span_poly).compose cut
  simpa only [cutLists, id_eq, tally_length, window, tally, List.length_replicate, List.drop_replicate] using h

theorem full_poly : Poly (fun t : Tally => (fullAxes t.length (count t.length)).map tally) := by
  have init := count_poly.pair (lower_poly.pair window_poly)
  have h := init.compose (axesFrom_poly BoxCoprimeTest.test_poly)
  change Poly (fun t : Tally => axesFrom (tally (count t.length), tally (span t.length - window t.length), tally (window t.length))) at h
  simpa only [axesFrom_fullAxes] using h

private theorem padded_poly : Poly (fun t : Tally =>
    ((fullAxes t.length (count t.length)).map tally).map (fun a => (tally (width t.length),a))) := by
  exact (width_poly.pair full_poly).compose (Poly.push ([] : Tally) ([] : Tally) (f := id) Poly.identity)

private theorem tail_poly : Poly (fun t : Tally =>
    if t.length % width t.length = 0 then ([] : List (Tally × Tally))
    else [(tally (t.length % width t.length), tally (2 ^ (t.length % width t.length)))]) := by
  let empty : Tally → Bool := List.isEmpty
  have he : Easy empty := by
    have eq : empty = (fun t : Tally => List.casesOn t true (fun _ _ => false)) := by
      funext t; cases t <;> rfl
    rw [eq]; exact Easy.listCase true (Easy.const false)
  have hrem := remainder_poly.compose he.poly
  have hsing : Poly (fun t : Tally => [(tally (t.length % width t.length), tally (2 ^ (t.length % width t.length)))]) :=
    (Poly.pair (remainder_poly.pair remainderSpan_poly) ((Easy.const []).poly)).compose Poly.cons
  have h := Poly.choose hrem ((Easy.const ([] : List (Tally × Tally))).poly) hsing
  convert h using 1
  funext t
  by_cases hz : t.length % width t.length = 0 <;> simp [empty, tally, hz]

/-- Uniform polynomial-time box setup. All search operations, including on failing small
inputs, have a polynomial bound on the coded stack machine. -/
theorem encoded_poly : Poly encoded := by
  convert padded_poly.app tail_poly using 1
  funext t
  simp only [encoded, box, BoxShape.axes, List.map_append, List.map_map, Function.comp_def]
  split <;> simp

/-- A single deterministic multitape machine computes the box from the unary
address width, with polynomially many actual steps and visited cells. -/
theorem machine : PolyTreeMachine (fun k : ℕ => k) (fun k => send (tally k))
    (fun k => send (encoded (tally k))) := by
  have hw : Dom (fun k : ℕ => k) (fun k => size (tally k)) := by
    refine ⟨1, 2, fun k => ?_⟩
    simp [size_tally]
  exact polyTreeMachine_of_BT (encoded_poly.on hw) hw

end BoxProgram

end NearSquareRoot
end Computability
end OAI
