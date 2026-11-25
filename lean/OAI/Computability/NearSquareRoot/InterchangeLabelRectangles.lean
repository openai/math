import OAI.Computability.NearSquareRoot.InterchangeFar
import OAI.Computability.NearSquareRoot.InterchangeLabels
import OAI.Computability.NearSquareRoot.InterchangeRectangle
import Mathlib.Algebra.BigOperators.Fin

/-!
# The rectangle partition of the two-level Hamming matrix

The alphabet `Fin (2^k)` used in the rank proof is identified with its binary
digits. Each directed rectangle of bit-string labels then determines finite
source and destination sets in the label space of `hammingLabelMatrix`.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open scoped Classical

variable {p k : ℕ}

private def binaryLetter (k : ℕ) : Fin (2 ^ k) ≃ LetterRectangles.Letter k :=
  finFunctionFinEquiv.symm.trans (Equiv.piCongrRight fun _ => finTwoEquiv)

private def binaryWord (p k : ℕ) : Word p (2 ^ k) ≃ FarRectangles.Word (2 * p - 1) k :=
  Equiv.piCongrRight fun _ => binaryLetter k

private def binaryLabel (p k : ℕ) : Label p (2 ^ k) ≃ FarRectangles.Label (2 * p - 1) k :=
  Equiv.piCongrRight fun _ => binaryWord p k

private theorem word_dist (x y : Word p (2 ^ k)) :
    hammingDist (binaryWord p k x) (binaryWord p k y) = hammingDist x y :=
  hammingDist_comp (fun _ => binaryLetter k) (fun _ => (binaryLetter k).injective)

private theorem label_dist (x y : Label p (2 ^ k)) :
    hammingDist (binaryLabel p k x) (binaryLabel p k y) = hammingDist x y :=
  hammingDist_comp (fun _ => binaryWord p k) (fun _ => (binaryWord p k).injective)

/-- Index of a directed rectangle of the `hammingLabelMatrix` label space. -/
abbrev HammingRectangleKey (p k : ℕ) (hp : 0 < p) := FarRectangles.LabelKey (2 * p - 1) p k hp

private def Edges (p : ℕ) (x y : Label p (2 ^ k)) : Prop :=
  hammingDist x y = p ∧ ∀ i, x i ≠ y i → hammingDist (x i) (y i) = p

private theorem edges_symm {x y : Label p (2 ^ k)} (h : Edges p x y) : Edges p y x := by
  refine ⟨(hammingDist_comm _ _).trans h.1, fun i hi => ?_⟩
  exact (hammingDist_comm _ _).trans (h.2 i hi.symm)

private theorem edges_binary_iff (x y : Label p (2 ^ k)) :
    (hammingDist (binaryLabel p k x) (binaryLabel p k y) = p ∧
      ∀ i, (binaryLabel p k x) i ≠ (binaryLabel p k y) i →
        hammingDist ((binaryLabel p k x) i) ((binaryLabel p k y) i) = p) ↔ Edges p x y := by
  change (_ ∧ ∀ i, binaryWord p k (x i) ≠ binaryWord p k (y i) →
    hammingDist (binaryWord p k (x i)) (binaryWord p k (y i)) = p) ↔ _
  simp only [label_dist, word_dist, ne_eq, Equiv.apply_eq_iff_eq, Edges]

/-- Actual labels on a given side of a rectangle. -/
noncomputable def labelsOn {hp : 0 < p} (side : Bool) (r : HammingRectangleKey p k hp) :
    Finset (Label p (2 ^ k)) :=
  Finset.univ.filter fun x => FarRectangles.LabelIncident side r (binaryLabel p k x)

private theorem labelsOn_iff {hp : 0 < p} {r : HammingRectangleKey p k hp}
    {side : Bool} {x : Label p (2 ^ k)} :
    x ∈ labelsOn side r ↔ FarRectangles.LabelIncident side r (binaryLabel p k x) := by
  simp only [labelsOn, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The same rectangle index is used for the source and destination sets. -/
noncomputable def hammingRectangle {hp : 0 < p} (r : HammingRectangleKey p k hp) :
    Rectangle (Label p (2 ^ k)) := ⟨labelsOn false r, labelsOn true r⟩

private theorem edges_unique (hp : 0 < p) (x y : Label p (2 ^ k)) :
    Edges p x y ↔ ∃! r : HammingRectangleKey p k hp, x ∈ labelsOn false r ∧ y ∈ labelsOn true r := by
  rw [← edges_binary_iff]
  simpa only [labelsOn_iff] using
    FarRectangles.label_supported_iff_unique hp (binaryLabel p k x) (binaryLabel p k y)

private theorem edges_of_cross {hp : 0 < p} {r : HammingRectangleKey p k hp}
    {x y : Label p (2 ^ k)} (hx : x ∈ labelsOn false r) (hy : y ∈ labelsOn true r) :
    Edges p x y := (edges_binary_iff x y).mp
      (FarRectangles.label_supported_of_incident (labelsOn_iff.mp hx) (labelsOn_iff.mp hy))

/-- Each nonzero off-diagonal matrix entry selects precisely one rectangle, with
the column label as its source and the row label as its destination. -/
theorem hammingLabelMatrix_offDiag_iff_unique [Fact p.Prime] {w v : Label p (2 ^ k)}
    (hne : w ≠ v) :
    hammingLabelMatrix p (2 ^ k) w v ≠ 0 ↔
      ∃! r : HammingRectangleKey p k (Fact.out : p.Prime).pos,
        w ∈ (hammingRectangle r).destinations ∧ v ∈ (hammingRectangle r).sources := by
  have he : hammingLabelMatrix p (2 ^ k) w v ≠ 0 ↔ Edges p w v := by
    simp [hammingLabelMatrix, hne, Edges]
  rw [he, show Edges p w v ↔ Edges p v w from ⟨edges_symm, edges_symm⟩, edges_unique]
  apply existsUnique_congr
  intro r
  exact and_comm

/-- Exact matrix identity over the same field and the same label set as the rank
bound. The rows index destinations and the columns index sources. -/
theorem rectangleMatrix_hammingRectangle (p k : ℕ) [Fact p.Prime] :
    rectangleMatrix (hammingRectangle (p := p) (k := k) (hp := (Fact.out : p.Prime).pos)) =
      hammingLabelMatrix p (2 ^ k) := by
  let hp := (Fact.out : p.Prime).pos
  calc
    rectangleMatrix (K := ZMod p) (hammingRectangle (hp := hp) (k := k)) =
        Matrix.of (fun w v : Label p (2 ^ k) => if w = v ∨ Edges p w v then 1 else 0) := by
      apply rectangleMatrix_of_partition (K := ZMod p) (hammingRectangle (hp := hp) (k := k)) (Edges (k := k) p)
      · intro w v
        constructor
        · intro h
          have h' := ((edges_unique hp v w).mp (edges_symm h)).exists
          exact h'.imp fun _ h => h.symm
        · rintro ⟨r, hwr, hvr⟩
          exact edges_symm (edges_of_cross hvr hwr)
      · intro w h
        have hn := h.1
        exact hp.ne (by simpa using hn)
      · intro w v b c hwb hvb hwc hvc
        have hu := (edges_unique hp v w).mp (edges_of_cross hvb hwb)
        exact hu.unique ⟨hvb, hwb⟩ ⟨hvc, hwc⟩
    _ = hammingLabelMatrix p (2 ^ k) := by
      ext w v
      simp only [hammingLabelMatrix, Edges, Matrix.of_apply]
      split_ifs with h <;> simp [h]


/-- Crossing a rectangle supplies exactly `p` far coordinates. -/
theorem count_hammingRectangle_cross {hp : 0 < p} {r : HammingRectangleKey p k hp}
    {x y : Label p (2 ^ k)} (hx : x ∈ (hammingRectangle r).sources)
    (hy : y ∈ (hammingRectangle r).destinations) :
    (Finset.univ.filter fun i => hammingDist (x i) (y i) = p).card = p := by
  have h := FarRectangles.count_far_across (labelsOn_iff.mp hx) (labelsOn_iff.mp hy)
  simpa only [binaryLabel, Equiv.piCongrRight_apply, Pi.map_apply, word_dist] using h

/-- Within either side all inner pairs avoid Hamming distance `p`. -/
theorem count_hammingRectangle_same {hp : 0 < p} {r : HammingRectangleKey p k hp}
    {x y : Label p (2 ^ k)} {side : Bool} (hx : x ∈ labelsOn side r) (hy : y ∈ labelsOn side r) :
    (Finset.univ.filter fun i => hammingDist (x i) (y i) = p).card = 0 := by
  have h := FarRectangles.count_far_same_side (labelsOn_iff.mp hx) (labelsOn_iff.mp hy)
  simpa only [binaryLabel, Equiv.piCongrRight_apply, Pi.map_apply, word_dist] using h

/-- The number of incident rectangles for a numerical label on either side. -/
theorem card_hammingRectangle_incident_le (hp : 0 < p) (side : Bool) (x : Label p (2 ^ k)) :
    Fintype.card {r : HammingRectangleKey p k hp // x ∈ labelsOn side r} ≤
      (2 * p - 1).choose p * ((2 * p - 1).choose p * (2 ^ k * k ^ (p - 1))) ^ p := by
  refine (Fintype.card_congr (Equiv.subtypeEquivRight fun _ => labelsOn_iff)).le.trans ?_
  exact FarRectangles.card_label_incident_le hp side (binaryLabel p k x)

/-- The rank-sized gather, mix and distribute stage on the original numerical
labels. For any initial layout and any destination layout, subtracting the
rectangle contributions leaves exactly the required independent transfer.
The selected row and column labels do not depend on the address or inputs. -/
theorem hamming_shared_transfer (p k : ℕ) [Fact p.Prime] {Addr E : Type*}
    [AddCommGroup E] [Module (ZMod p) E] :
    let P := hammingLabelMatrix p (2 ^ k)
    let r := hammingRectangle (p := p) (k := k) (hp := (Fact.out : p.Prime).pos)
    ∃ I J : Fin P.rank → Label p (2 ^ k), Function.Injective I ∧ Function.Injective J ∧
      IsUnit (P.submatrix I J) ∧ ∀ (S T : Label p (2 ^ k) → Equiv.Perm Addr)
        (X : Label p (2 ^ k) → Addr → E) (w : Label p (2 ^ k)) (d : Addr),
        let x := fun v => X v ((S v).symm (T w d))
        let gathered := fun i => x (I i) + rectangleSum r x (I i)
        let mixed := applyRows (P.submatrix I J)⁻¹ gathered
        applyRows (P.submatrix id J) mixed w - rectangleSum r x w =
          X w ((S w).symm (T w d)) := by
  rw [← rectangleMatrix_hammingRectangle p k]
  exact
    shared_transfer (K := ZMod p) (E := E) (Addr := Addr)
      (hammingRectangle (p := p) (k := k) (hp := (Fact.out : p.Prime).pos))

end Interchange

end NearSquareRoot
end Computability
end OAI
