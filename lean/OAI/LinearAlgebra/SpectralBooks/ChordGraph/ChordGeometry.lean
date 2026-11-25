import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-! # Uncrossing chords of a polygon

For four cyclically ordered vertices, each adjacent matching preserves all
incident widths. Replacing the crossing by either adjacent matching strictly
decreases the sum of the chord potentials, weighted by their bit widths.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace ChordGraph

noncomputable section

/-- A chord is named in increasing order of its two vertices. -/
abbrev Chord (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}

/-- A width of zero indicates the absence of the chord. -/
abbrev Widths (k : ℕ) := Chord k →₀ ℕ

variable {k : ℕ}

def edge (i j : Fin k) (h : i < j) : Chord k := ⟨(i, j), h⟩

def unitChord (e : Chord k) : Widths k := Finsupp.single e 1

private def weightedSum (weight : Chord k → ℕ) : Widths k →+ ℕ :=
  Finsupp.liftAddHom fun e =>
    { toFun := fun w => weight e * w
      map_zero' := Nat.mul_zero _
      map_add' := Nat.mul_add _ }

private theorem weightedSum_apply (weight : Chord k → ℕ) (g : Widths k) :
    weightedSum weight g = ∑ e ∈ g.support, weight e * g e := rfl

@[simp] private theorem weightedSum_single (weight : Chord k → ℕ) (e : Chord k) (w : ℕ) :
    weightedSum weight (Finsupp.single e w) = weight e * w := by
  simp [weightedSum]

/-- The number of bit wires, counted with multiplicity. -/
def total : Widths k →+ ℕ := weightedSum (fun _ => 1)

/-- Incident width at a vertex, counting each endpoint of each chord. -/
def load (i : Fin k) : Widths k →+ ℕ :=
  weightedSum fun e => (if i = e.1.1 then 1 else 0) + (if i = e.1.2 then 1 else 0)

/-- The product of the two cyclic arc lengths between the endpoints. -/
def chordPotential (e : Chord k) : ℕ :=
  let s := e.1.2.val - e.1.1.val
  s * (k - s)

/-- The sum of the potentials of all bit wires. -/
def potential : Widths k →+ ℕ := weightedSum chordPotential

@[simp] theorem total_single (e : Chord k) (w : ℕ) :
    total (Finsupp.single e w) = w := by simp [total]

@[simp] theorem load_single (i : Fin k) (e : Chord k) (w : ℕ) :
    load i (Finsupp.single e w) =
      ((if i = e.1.1 then 1 else 0) + (if i = e.1.2 then 1 else 0)) * w := by simp [load]

@[simp] theorem potential_single (e : Chord k) (w : ℕ) :
    potential (Finsupp.single e w) = chordPotential e * w := by simp [potential]

theorem potential_le_total (g : Widths k) : potential g ≤ k * k * total g := by
  classical
  simp only [total, potential, weightedSum_apply, one_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => Nat.mul_le_mul_right _ ?_
  exact Nat.mul_le_mul (le_trans (Nat.sub_le _ _) e.1.2.isLt.le) (Nat.sub_le _ _)

variable {a b c d : Fin k}

def crossing (hab : a < b) (hbc : b < c) (hcd : c < d) : Widths k :=
  unitChord (edge a c (hab.trans hbc)) + unitChord (edge b d (hbc.trans hcd))

def parallel (hab : a < b) (_hbc : b < c) (hcd : c < d) : Widths k :=
  unitChord (edge a b hab) + unitChord (edge c d hcd)

def nested (hab : a < b) (hbc : b < c) (hcd : c < d) : Widths k :=
  unitChord (edge a d (hab.trans (hbc.trans hcd))) + unitChord (edge b c hbc)

variable (hab : a < b) (hbc : b < c) (hcd : c < d)

@[simp] theorem total_crossing : total (crossing hab hbc hcd) = 2 := by
  simp [crossing, unitChord]

@[simp] theorem total_parallel : total (parallel hab hbc hcd) = 2 := by
  simp [parallel, unitChord]

@[simp] theorem total_nested : total (nested hab hbc hcd) = 2 := by
  simp [nested, unitChord]

theorem load_parallel_eq_crossing (i : Fin k) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    load i (parallel hab hbc hcd) = load i (crossing hab hbc hcd) := by
  simp only [parallel, crossing, unitChord, map_add, load_single, edge, mul_one]
  ac_rfl

theorem load_nested_eq_crossing (i : Fin k) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    load i (nested hab hbc hcd) = load i (crossing hab hbc hcd) := by
  simp only [nested, crossing, unitChord, map_add, load_single, edge, mul_one]
  ac_rfl

/-- Both potential differences, in terms of the four cyclic gaps. -/
theorem potential_uncrossing_gaps :
    potential (crossing hab hbc hcd) = potential (parallel hab hbc hcd) +
      2 * (c.val - b.val) * (k - (d.val - a.val)) ∧
    potential (crossing hab hbc hcd) = potential (nested hab hbc hcd) +
      2 * (b.val - a.val) * (d.val - c.val) := by
  let x := b.val - a.val
  let y := c.val - b.val
  let z := d.val - c.val
  let t := k - (d.val - a.val)
  have hab' := show a.val < b.val from hab
  have hbc' := show b.val < c.val from hbc
  have hcd' := show c.val < d.val from hcd
  have hdk := d.isLt
  simp only [crossing, parallel, nested, map_add, unitChord, potential_single, mul_one,
    chordPotential, edge]
  rw [show c.val - a.val = x + y by dsimp [x, y]; omega,
      show d.val - b.val = y + z by dsimp [y, z]; omega,
      show k - (x + y) = z + t by dsimp [x, y, z, t]; omega,
      show k - (y + z) = t + x by dsimp [x, y, z, t]; omega,
      show k - (b.val - a.val) = y + z + t by dsimp [y, z, t]; omega,
      show k - (d.val - c.val) = t + x + y by dsimp [t, x, y]; omega,
      show k - (c.val - b.val) = z + t + x by dsimp [z, t, x]; omega]
  change (x + y) * (z + t) + (y + z) * (t + x) =
      x * (y + z + t) + z * (t + x + y) + 2 * y * t ∧
    (x + y) * (z + t) + (y + z) * (t + x) =
      (d.val - a.val) * t + y * (z + t + x) + 2 * x * z
  rw [show d.val - a.val = x + y + z by dsimp [x, y, z]; omega]
  constructor <;> ring

theorem potential_parallel_lt_crossing :
    potential (parallel hab hbc hcd) < potential (crossing hab hbc hcd) := by
  rw [(potential_uncrossing_gaps hab hbc hcd).1]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos
    (Nat.mul_pos (by decide) (Nat.sub_pos_of_lt (show b.val < c.val from hbc)))
    (Nat.sub_pos_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) d.isLt)))

theorem potential_nested_lt_crossing :
    potential (nested hab hbc hcd) < potential (crossing hab hbc hcd) := by
  rw [(potential_uncrossing_gaps hab hbc hcd).2]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos
    (Nat.mul_pos (by decide) (Nat.sub_pos_of_lt (show a.val < b.val from hab)))
    (Nat.sub_pos_of_lt (show c.val < d.val from hcd)))

end
end ChordGraph

end SpectralBooks
end LinearAlgebra
end OAI
