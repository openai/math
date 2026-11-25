import OAI.LinearAlgebra.SpectralBooks.MovingNode
import OAI.LinearAlgebra.SpectralBooks.CubeTable.ManyRelocationPricing
import OAI.LinearAlgebra.SpectralBooks.Levels
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.EndpointPrices
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Select

/-! # One actual tensor step of the many-index relocation tree

At a chosen interior placement, one of the two exterior children retains the
parent price up to the ordinary sum loss. At every endpoint placement the same
child obeys both its unchanged-endpoint bound and its opposite-endpoint bound.
Subtracting the middle exterior wire cost implements the clipping of the table.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open scoped Classical
open Function Real

namespace SiteTensor.Relocation

open Exterior

variable {r : ℕ} {J : Type} {K : Type*} [Fintype J] [Nonempty J] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))

private abbrev value {q : Fin r → ℕ} (scale : ℝ) (s : MovingTensor J K q) (p : Fin r → J) :=
  rawLogPrice φ scale (s.grouped p)

private theorem value_marked {q : Fin r → ℕ} (scale : ℝ) (s : MovingTensor J K q)
    (i : Fin r) (p : Fin r → J) :
    value φ scale s p = rawLogPrice φ scale ((marked (s.backgroundLeg i) _ (s.markedCoeff i)).group
      (placeMark (s.background i p) (p i))) := by
  simp only [value, rawLogPrice, s.ofRaw_grouped_eq_marked i p]

/-- The selected-branch property used in the finite Boolean-cube recursion,
with a real tensor at every node and the accumulated wire cost in its account. -/
theorem moving_selectedSplit {scale : ℝ} (hs : 0 ≤ scale) {n : ℕ} (hn : 0 < n)
    (a b z : Fin r → J) (N : CubeTable r) (i : Fin r)
    (hmid : |CubeTable.midpoint N i| ≤ n * rawWireDistance φ scale (a i) (b i))
    {ε : ℝ} (hε : scale ≤ ε) :
    CubeTable.SelectedSplit
      (fun (x : MovingNode J K (fun _ : Fin r ↦ 2 ^ n)) k ↦
        movingNodePrice φ scale x (cornerAt a b k))
      (fun x ↦ movingNodePrice φ scale x z) ε N i := by
  let d := rawWireDistance φ scale (a i) (b i)
  have hd : 0 ≤ d := rawLogPrice_nonneg φ hs _
  obtain ⟨l, hl, hhi, hlo⟩ := relocation_level_bounds_for_threshold hn hd hmid
  let Q := 2 ^ n
  let L (j : ℕ) := Level Q j
  let hlev (j : ℕ) (hj : j ≤ Q) : Nonempty (Level Q j) := by
    apply Fintype.card_pos_iff.mp
    rw [card_level]
    exact Nat.choose_pos hj
  have hQ : l + 2 ≤ Q := hl
  let : Nonempty (Level Q l) := hlev l (by omega)
  let : Nonempty (Level Q (l+1)) := hlev _ (by omega)
  let : Nonempty (Level Q (l+2)) := hlev _ hQ
  let cost (j : ℕ) := d * logb 2 (Fintype.card (L j))
  have hposcost : cost (l+2) - cost (l+1) ≤ CubeTable.midpoint N i := by
    simpa only [cost, L, card_level, Q, ← mul_sub] using hhi
  have hnegcost : cost l - cost (l+1) ≤ -CubeTable.midpoint N i := by
    simpa only [cost, L, card_level, Q, ← mul_sub] using hlo
  intro x σ _ hbound
  let s := x.1.val
  let T := s.markedCoeff i
  let upper := s.child i (L (l+1)) (a i) (b i)
    (plusCoeff T (create (b := l+1) K) (contract K))
  let lower := s.child i (L (l+1)) (a i) (b i)
    (minusCoeff T (contract (b := l) K) (create K))
  let childState (v : Bool) := if v then lower else upper
  let site (v : Bool) := if v then b i else a i
  have parent (p : Fin r → J) (t : J) :
      value φ scale s (update p i t) = rawLogPrice φ scale
        ((marked (s.backgroundLeg i) _ T).group (placeMark (s.background i p) t)) := by
    rw [value_marked φ scale s i, s.background_update_same, update_self]
  have upperBounds (p : Fin r → J) :
      value φ scale upper (update p i (a i)) ≤ value φ scale s (update p i (a i)) + cost (l+1) ∧
      value φ scale upper (update p i (b i)) ≤ value φ scale s (update p i (b i)) + cost (l+1) ∧
      value φ scale upper (update p i (a i)) ≤ value φ scale s (update p i (b i)) + cost (l+2) := by
    simp only [parent, upper, value, s.grouped_child, update_self, s.background_update_same]
    exact plus_endpoint_prices φ hs T (create (b := l+1) K) (contract K)
      (s.background i p) (a i) (b i)
  have lowerBounds (p : Fin r → J) :
      value φ scale lower (update p i (a i)) ≤ value φ scale s (update p i (a i)) + cost (l+1) ∧
      value φ scale lower (update p i (b i)) ≤ value φ scale s (update p i (b i)) + cost (l+1) ∧
      value φ scale lower (update p i (b i)) ≤ value φ scale s (update p i (a i)) + cost l := by
    simp only [parent, lower, value, s.grouped_child, update_self, s.background_update_same]
    exact minus_endpoint_prices φ hs T (contract (b := l) K) (create K)
      (s.background i p) (a i) (b i)
  have endpoints (v : Bool) (p : Fin r → J) (k : Bool) :
      value φ scale (childState v) (update p i (site k)) ≤ value φ scale s (update p i (site k)) + cost (l+1) := by
    cases v <;> cases k
    · exact (upperBounds p).1
    · exact (upperBounds p).2.1
    · exact (lowerBounds p).1
    · exact (lowerBounds p).2.1
  have opposite (v : Bool) (p : Fin r → J) :
      value φ scale (childState v) (update p i (site v)) ≤
        value φ scale s (update p i (site (!v))) + cost (l+1) +
          (if v then -CubeTable.midpoint N i else CubeTable.midpoint N i) := by
    cases v
    · change value φ scale upper (update p i (a i)) ≤
        value φ scale s (update p i (b i)) + cost (l+1) + CubeTable.midpoint N i
      linarith only [(upperBounds p).2.2, hposcost]
    · change value φ scale lower (update p i (b i)) ≤
        value φ scale s (update p i (a i)) + cost (l+1) + -CubeTable.midpoint N i
      linarith only [(lowerBounds p).2.2, hnegcost]
  have hsel := select_split (b := l) φ hs T (s.marked_ne_zero i x.1.property) (s.background i z)
    (z i) (a i) (b i)
  have hw : rawLogPrice φ scale (wire K (Level (2^n) (l+1)) (a i) (b i)) = cost (l+1) :=
    rawLogPrice_group_diagonal φ ![a i,b i] scale
  have winner : ∃ v : Bool, (childState v).T.coeff ≠ 0 ∧
      value φ scale s z + cost (l+1) ≤ value φ scale (childState v) z + scale := by
    rcases hsel with ⟨hnz, hb⟩ | ⟨hnz, hb⟩
    · refine ⟨false, hnz, ?_⟩
      simpa only [childState, Bool.false_eq_true, ite_false, upper, value_marked φ scale s i z,
        value, s.grouped_child, ← hw] using hb
    · refine ⟨true, hnz, ?_⟩
      simpa only [childState, ite_true, lower, value_marked φ scale s i z,
        value, s.grouped_child, ← hw] using hb
  obtain ⟨v, hnz, hv⟩ := winner
  let y : MovingNode J K (fun _ : Fin r ↦ 2^n) := (⟨childState v, hnz⟩, x.2 + cost (l+1))
  refine ⟨y, v, ?_, ?_⟩
  · change value φ scale s z - x.2 ≤ value φ scale (childState v) z - (x.2 + cost (l+1)) + ε
    linarith
  · intro k
    let p := cornerAt a b k
    have hp : update p i (site (k i)) = p := update_eq_self ..
    have h₁ := endpoints v p (k i)
    rw [hp] at h₁
    have hold := hbound k
    change value φ scale s p - x.2 ≤ N k + σ at hold
    change value φ scale (childState v) p - (x.2 + cost (l+1)) ≤ CubeTable.child N i v k + (σ+ε)
    have he : 0 ≤ ε := hs.trans hε
    simp only [CubeTable.child]
    split <;> rename_i hk
    · rw [← min_add_add_right]
      apply le_min
      · linarith
      · have h₂ := opposite v p
        rw [← hk, hp] at h₂
        have hm := hbound (update k i (!v))
        change value φ scale s (cornerAt a b (update k i (!v))) - x.2 ≤ N (update k i (!v)) + σ at hm
        rw [cornerAt_update] at hm
        change value φ scale s (update p i (site (!v))) - x.2 ≤ _ at hm
        rw [hk] at h₂
        linarith
    · linarith

end SiteTensor.Relocation

end

end SpectralBooks
end LinearAlgebra
end OAI
