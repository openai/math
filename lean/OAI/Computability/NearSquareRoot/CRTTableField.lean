import OAI.Computability.IntegerMultiplication.Code.Loop
import OAI.Computability.IntegerMultiplication.Goal

/-! # Reading one bounded CRT control field

The stack program reads bits most significant first and keeps the minimum of the
decoded prefix and the supplied unary modulus. Thus even a malformed long field
uses a tally bounded by the modulus after every bit.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication IntegerMultiplication.Code

/-- Read a field as a unary coordinate, using the cap itself for out-of-range values. -/
def fieldDecode (p : Tally × List Bool) : Tally :=
  tally (min p.1.length (bitValue p.2))

@[simp] theorem fieldDecode_length (cap : Tally) (w : List Bool) :
    (fieldDecode (cap,w)).length = min cap.length (bitValue w) := by
  simp [fieldDecode]

private def nextField (s : (Tally × Tally) × Bool) : Tally × Tally :=
  let twice := s.1.2 ++ s.1.2
  (s.1.1, (cutLists (s.1.1, bif s.2 then () :: twice else twice)).1)

private theorem nextField_poly : Poly nextField := by
  have h : Poly (fun s : (Tally × Tally) × Bool =>
      (s.1.1, bif s.2 then () :: (s.1.2 ++ s.1.2) else s.1.2 ++ s.1.2)) := by fun_prop
  have hc := (easy_cut (X := Unit) (Z := Tally × Tally) Easy.identity).fstCompose.poly
  exact Poly.pair (by fun_prop) (h.compose hc)

private def readField (w : List Bool) (c a : Tally) : Tally × Tally :=
  w.foldl (fun s b => nextField (s,b)) (c,a)

private theorem readField_bound (w : List Bool) (c a : Tally) :
    (readField w c a).1 = c ∧ (readField w c a).2.length ≤ max c.length a.length := by
  induction w generalizing a with
  | nil => exact ⟨rfl, Nat.le_max_right ..⟩
  | cons b w ih =>
    change (readField w c _).1 = c ∧ (readField w c _).2.length ≤ _
    obtain ⟨hc,hl⟩ := ih (nextField ((c,a),b)).2
    have ht : (nextField ((c,a),b)).2.length ≤ c.length := by
      simp [nextField,cutLists]
    exact ⟨hc, hl.trans ((max_le (Nat.le_refl _) ht).trans (Nat.le_max_left ..))⟩

private theorem readField_correct (w : List Bool) (c a : Tally) (n : ℕ)
    (ha : a.length = min c.length n) :
    (readField w c a).2.length = min c.length (w.foldl (fun v b => 2*v + b.toNat) n) := by
  induction w generalizing a n with
  | nil => exact ha
  | cons b w ih =>
    change (readField w c _).2.length = min c.length (w.foldl _ _)
    apply ih
    change (nextField ((c,a),b)).2.length = min c.length (2 * n + b.toNat)
    cases b <;> simp [nextField,cutLists,ha] <;> omega

/-- One fixed polynomial-time stack program handles every modulus and every
field width, including leading zeroes. -/
@[fun_prop] theorem fieldDecode_poly : Poly fieldDecode := by
  have fold := Poly.fold_left nextField_poly 2 1 (by
    rintro ⟨w,c,a⟩ l _
    obtain ⟨hc,ha⟩ := readField_bound l c a
    change size (readField l c a) ≤ _
    simp only [size_prod, size_tally, hc, pow_one]
    omega)
  have hinit : Poly (fun p : Tally × List Bool => (p.2, p.1, ([] : Tally))) := by fun_prop
  have hh := hinit.compose fold.sndCompose
  suffices e : fieldDecode = fun p : Tally × List Bool => (readField p.2 p.1 []).2 by
    rw [e]
    exact hh
  funext ⟨c,w⟩
  have h := readField_correct w c [] 0 (by simp)
  change List.replicate (min c.length (w.foldl _ 0)) () = (readField w c []).2
  rw [← h]
  exact (List.eq_replicate_length.mpr (by simp)).symm

end CRTTable

end NearSquareRoot
end Computability
end OAI
