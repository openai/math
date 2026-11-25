import OAI.Computability.IntegerMultiplication.Code.Pace

/-! # Preparing CRT substitution rows

The two consecutive axis lists are in ascending axis order. Each descriptor
holds a width and a modulus. A control contributes its decoded coordinate to
the substitution system, and each target starts with the unary value zero.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication.Code

/-- The two descriptor lists, control values, and triangular coefficient lists. -/
abbrev RowInput :=
  List (Tally × Tally) × List (Tally × Tally) × List Tally × List (List Tally)

private def starts (p : RowInput) : List (Tally × Tally) :=
  zipFair [] [] ((p.1 ++ p.2.1).map Prod.snd,
    p.2.2.1 ++ p.2.1.map (fun _ => ([] : Tally)))

/-- Align the initial residues with their coefficient queues. -/
def rawRows (p : RowInput) : List (Tally × Tally × List Tally) :=
  lock (fun s => (s.1.1, s.1.2, s.2)) ([], []) [] (starts p, p.2.2.2)

private theorem starts_easy : Easy starts := by
  apply Easy.compose _ (easy_zip [] [])
  fun_prop

theorem rawRows_easy : Easy rawRows := by
  apply Easy.compose (starts_easy.pair (by fun_prop))
    (easy_lock _ (by fun_prop) ([], []) [])

theorem rawRows_poly : Poly rawRows := rawRows_easy.poly

theorem zipFair_eq_zip {A B : Type} (a : A) (b : B) (xs : List A) (ys : List B)
    (h : xs.length = ys.length) :
    zipFair a b (xs, ys) = xs.zip ys := by
  have z (u : List A) (v : List B) (hv : u.length = v.length)
      (x : List A) (y : List B) :
      ((u ++ x).zip (v ++ y)).take u.length = u.zip v := by
    induction u generalizing v with
    | nil => simp
    | cons k ks ih =>
      cases v with
      | nil => simp at hv
      | cons l ls => simp [ih ls (by simpa using hv)]
  simpa [zipFair, zipSafe, cutLists] using
    z xs ys h (List.replicate ys.length a) (List.replicate xs.length b)

/-- On well-formed packets, all three fields of every emitted row are obtained
from the same axis index. -/
theorem rawRows_eq (controls targets : List (Tally × Tally)) (v : List Tally)
    (cs : List (List Tally)) (hv : v.length = controls.length)
    (hc : cs.length = controls.length + targets.length) :
    rawRows (controls, targets, v, cs) =
      ((((controls ++ targets).map Prod.snd).zip
        (v ++ List.replicate targets.length ([] : Tally))).zip cs).map
          (fun s => (s.1.1, s.1.2, s.2)) := by
  simp only [rawRows, starts, lock]
  rw [zipFair_eq_zip [] [] _ _ (by simp [hv])]
  rw [zipFair_eq_zip ([], []) [] _ _ (by simp [hv, hc])]
  simp

theorem rawRows_length (controls targets : List (Tally × Tally)) (v : List Tally)
    (cs : List (List Tally)) (hv : v.length = controls.length)
    (hc : cs.length = controls.length + targets.length) :
    (rawRows (controls, targets, v, cs)).length = controls.length + targets.length := by
  rw [rawRows_eq _ _ _ _ hv hc]
  simp [hv, hc]

theorem rawRows_get_control (controls targets : List (Tally × Tally)) (v : List Tally)
    (cs : List (List Tally)) (hv : v.length = controls.length)
    (hc : cs.length = controls.length + targets.length) (i : Fin controls.length) :
    (rawRows (controls, targets, v, cs))[i.val]'(by
      rw [rawRows_length _ _ _ _ hv hc]; omega) =
      (controls[i.val].2, v[i.val]'(by omega), cs[i.val]'(by omega)) := by
  simp only [rawRows_eq _ _ _ _ hv hc, List.getElem_map, List.getElem_zip]
  rw [List.getElem_append_left i.isLt, List.getElem_append_left (by omega : i.val < v.length)]

theorem rawRows_get_target (controls targets : List (Tally × Tally)) (v : List Tally)
    (cs : List (List Tally)) (hv : v.length = controls.length)
    (hc : cs.length = controls.length + targets.length) (i : Fin targets.length) :
    (rawRows (controls, targets, v, cs))[controls.length + i.val]'(by
      rw [rawRows_length _ _ _ _ hv hc]; omega) =
      (targets[i.val].2, [], cs[controls.length + i.val]'(by omega)) := by
  simp only [rawRows_eq _ _ _ _ hv hc, List.getElem_map, List.getElem_zip]
  rw [List.getElem_append_right (by omega : controls.length ≤ controls.length + i.val),
    List.getElem_append_right (by omega : v.length ≤ controls.length + i.val)]
  simp

end CRTTable

end NearSquareRoot
end Computability
end OAI
