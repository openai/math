import OAI.Computability.IntegerMultiplication.Code.Iter

/-! # Forward substitution for a CRT control setting

A row holds one modulus, its current residue, and the coefficients for
unprocessed control digits. Removing one pivot subtracts that digit's
contribution from every later row. Right-child rows start with residue zero,
so their final residues give the negative rotation offsets.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication.Code

abbrev Row := Tally × Tally × List Tally

def residualStep (q : Tally × Tally × Tally × Tally) : Tally :=
  let (v, c, t, a) := q
  tally ((v.length % a.length + a.length - (c.length * t.length) % a.length) % a.length)

def advanceRow (p : Tally × Row) : Row :=
  (p.2.1, residualStep (p.2.2.1, p.2.2.2.headD [], p.1, p.2.1), p.2.2.2.tail)

def eliminate (rows : List Row) : List Row :=
  rows.tail.map (fun r => advanceRow ((rows.headD ([],[],[])).2.1, r))

def residuals (p : Tally × List Row) : List Row := ride eliminate p

private theorem tail_easy {X : Type} [Codec X] : Easy (List.tail (α := X)) := by
  have h : List.tail (α := X) = (fun xs => List.casesOn (motive := fun _ => List X)
    xs [] fun _ rest => rest) := by funext xs; cases xs <;> rfl
  rw [h]
  exact Easy.listCase [] Easy.snd

private theorem advanceRow_poly (h : Poly residualStep) : Poly advanceRow := by
  have coeffs : Poly (fun p : Tally × Row => p.2.2.2) := by fun_prop
  have head := coeffs.compose (Iter.leader ([] : Tally)).poly
  have params : Poly (fun p : Tally × Row =>
      (p.2.2.1, p.2.2.2.headD [], p.1, p.2.1)) :=
    (by fun_prop : Poly (fun p : Tally × Row => p.2.2.1)).pair
      (head.pair (by fun_prop))
  exact (by fun_prop : Poly (fun p : Tally × Row => p.2.1)).pair
    ((params.compose h).pair (coeffs.compose tail_easy.poly))

private theorem eliminate_poly (h : Poly residualStep) : Poly eliminate := by
  have pivot := ((Iter.leader (([],[],[]) : Row)).poly).sndCompose.fstCompose
  exact (pivot.pair tail_easy.poly).compose
    (Poly.push ([] : Tally) (([],[],[]) : Row) (advanceRow_poly h))

/-- Potential reserves room for an arbitrary valid residue at each row,
including rows whose current residue is zero. -/
private def capacity (r : Row) : ℕ :=
  size r.1 + max (size r.2.1) (size r.1) + size r.2.2 + 2

private def volume : List Row → ℕ
  | [] => 1
  | r :: rs => capacity r + volume rs + 1

private theorem size_le_volume (rs : List Row) : size rs ≤ volume rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [size_cons, size_prod, volume, capacity]
    omega

private theorem volume_le_size (rs : List Row) : volume rs ≤ 2 * size rs := by
  induction rs with
  | nil => decide
  | cons r rs ih =>
    simp only [size_cons, size_prod, volume, capacity]
    omega

private theorem tail_size_le {X : Type} [Codec X] (xs : List X) :
    size xs.tail ≤ size xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp; omega

private theorem advanceRow_capacity (t : Tally) (r : Row) :
    capacity (advanceRow (t,r)) ≤ capacity r := by
  have hv : (residualStep (r.2.1, r.2.2.headD [], t, r.1)).length ≤
      max r.2.1.length r.1.length := by
    simp only [residualStep, tally_length]
    by_cases ha : r.1.length = 0
    · simp [ha]
    · exact (Nat.mod_lt _ (Nat.pos_of_ne_zero ha)).le.trans (Nat.le_max_right ..)
  simp only [advanceRow, capacity, size_tally]
  have ht := tail_size_le r.2.2
  omega

private theorem eliminate_volume (rs : List Row) : volume (eliminate rs) ≤ volume rs := by
  have map_le (t : Tally) (xs : List Row) :
      volume (xs.map (fun r => advanceRow (t,r))) ≤ volume xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, volume]
      have hc := advanceRow_capacity t x
      omega
  cases rs with
  | nil => rfl
  | cons r rs =>
    exact (map_le r.2.1 rs).trans (by simp only [volume]; omega)

/-- Every intermediate table has encoded size at most twice the initial
one, even when the rows presented to the program are malformed. -/
theorem residuals_size (p : Tally × List Row) : size (residuals p) ≤ 2 * size p.2 := by
  have nonincreasing (τ : Tally) (rs : List Row) :
      volume (residuals (τ,rs)) ≤ volume rs := by
    induction τ generalizing rs with
    | nil => rfl
    | cons u τ ih => exact (ih (eliminate rs)).trans (eliminate_volume rs)
  exact ((size_le_volume _).trans (nonincreasing ..)).trans (volume_le_size _)

theorem residuals_poly_of (h : Poly residualStep) : Poly residuals := by
  apply Poly.fold_left (f := fun p : List Row × Unit => eliminate p.1)
    (Easy.fst.poly.compose (eliminate_poly h)) 2 1
  intro s τ _
  refine (residuals_size (τ,s.2)).trans ?_
  simp only [size_prod, pow_one]
  omega

end CRTTable

end NearSquareRoot
end Computability
end OAI
