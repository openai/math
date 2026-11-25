import OAI.Computability.NearSquareRoot.BoxShape
import OAI.Computability.IntegerMultiplication.Carry.Figure

/-! # Computing padded axis sizes for the routing tables -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry
open IntegerMultiplication.Staff IntegerMultiplication.Strip

abbrev Descriptor := Tally × Tally

/-- The cap makes unary output polynomial on every input. Density of the
selected box implies that this cap never removes a padded address. -/
def padded (d : Descriptor) : Tally :=
  tally (min (2 ^ d.1.length) (2 * d.2.length))

theorem padded_poly : Poly padded := by
  let r : Regime Descriptor := ⟨size, send, Dom.base _⟩
  have w : Realizes r (fun d : Descriptor => d.1.length) := by
    change Poly (fun d : Descriptor => tally d.1.length)
    simpa only [recover_tally] using (Easy.fst (X := Tally) (Y := Tally)).poly
  have a : Realizes r (fun d : Descriptor => d.2.length) := by
    change Poly (fun d : Descriptor => tally d.2.length)
    simpa only [recover_tally] using (Easy.snd (X := Tally) (Y := Tally)).poly
  have pow := (Figure.natural 2).repeated w
  have cap := (Figure.natural 2).multiplied (Figure.of_spoken a)
  have hmin : Figure r (fun d : Descriptor => min (2^d.1.length) (2*d.2.length)) := by
    simpa only [min_def_lt] using pow.variant cap (pow.compare_ cap)
  apply hmin.pay
  refine ((Dom.const r.scale 2).mul (Dom.base r.scale)).mono ?_
  intro d
  refine (min_le_right ..).trans (Nat.mul_le_mul_left 2 ?_)
  change d.2.length ≤ size d
  simp only [size_prod, size_tally]
  omega

theorem padded_length_of_le (d : Descriptor) (h : 2^d.1.length ≤ 2*d.2.length) :
    (padded d).length = 2^d.1.length := by simp [padded, min_eq_left h]

private theorem occupied_le_padded (xs : List (ℕ × ℕ))
    (h : ∀ p ∈ xs, p.2 ≤ 2^p.1) :
    (xs.map Prod.snd).prod ≤ 2^(xs.map Prod.fst).sum := by
  induction xs with
  | nil => simp
  | cons q xs ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add]
    exact Nat.mul_le_mul (h q List.mem_cons_self) (ih (by intro p hp; exact h p (by simp [hp])))

/-- Occupancy of at least one half in the Cartesian product forces at least
half occupancy in each axis, since every other axis fits its own padding. -/
theorem axis_half_full {k l : ℕ} {box : List (ℕ × ℕ)} (hbox : BoxShape.Valid k l box)
    {p : ℕ × ℕ} (hp : p ∈ box) : 2^p.1 ≤ 2*p.2 := by
  obtain ⟨left, right, rfl⟩ := List.append_of_mem hp
  have hl := occupied_le_padded left (fun q hq => (hbox.axisBounds q (by simp [hq])).2.2.2)
  have hr := occupied_le_padded right (fun q hq => (hbox.axisBounds q (by simp [hq])).2.2.2)
  have dens := hbox.density
  rw [← hbox.widthSum] at dens
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons, List.sum_append,
    List.sum_cons, pow_add] at dens
  let u := 2^(left.map Prod.fst).sum * 2^(right.map Prod.fst).sum
  have hu : 0 < u := by dsimp [u]; positivity
  apply Nat.le_of_mul_le_mul_left _ hu
  calc
    u * 2^p.1 = 2^(left.map Prod.fst).sum * (2^p.1 * 2^(right.map Prod.fst).sum) := by
      dsimp [u]; ring
    _ ≤ _ := dens
    _ ≤ 2 * (2^(left.map Prod.fst).sum * (p.2 * 2^(right.map Prod.fst).sum)) := by gcongr
    _ = u * (2*p.2) := by dsimp [u]; ring

end CRTTable

end NearSquareRoot
end Computability
end OAI
