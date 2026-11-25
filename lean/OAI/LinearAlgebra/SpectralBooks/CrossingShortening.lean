import OAI.LinearAlgebra.SpectralBooks.Alternative
import OAI.LinearAlgebra.SpectralBooks.Crossing
import OAI.LinearAlgebra.SpectralBooks.CrossingTensor
import OAI.LinearAlgebra.SpectralBooks.AxisSites

/-!
# A fixed-format shortening from strict spectral comparison

The terminals and pair costs here are concrete. The only spectral inputs to the
final theorem are the price gap and its implication, by strict spectral comparison,
for restrictions of tensor powers.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace Crossing

noncomputable section

/-- The center's coordinate is trivial; each signed endpoint carries a bit string. -/
def AxisLeg {D : ℕ} (m : ℕ) : AxisSite D → Type
  | none => Unit
  | some _ => BitString m

/-- `C_{D,m}` as a tensor with a separate coordinate at every site. -/
def crossingTensor (F : Type*) [CommSemiring F] (D m : ℕ)
    (x : ∀ i : AxisSite D, AxisLeg m i) : F :=
  crossingEntry F (x none) (fun i => x (some (i, false))) (fun i => x (some (i, true)))

/-- A wire on the given pair. Its order only names its two ends. -/
def axisWire {D : ℕ} (e : AxisPair D) (width : ℕ) : Wire (AxisSite D) :=
  ⟨e.val.out.1, e.val.out.2, endpoints_ne e, width⟩

/-- The fixed-format hypothesis of the shortening criterion, witnessed by networks all
of whose wires join marked positions. Arbitrary local tables are allowed. -/
def ShortenedCrossing (F : Type*) [CommSemiring F] (D m : ℕ) : Prop :=
  ∃ (A : ℕ) (budget : ℝ) (count : Fin A → ℕ)
      (wires : (a : Fin A) → Fin (count a) → Wire (AxisSite D))
      (T : (a : Fin A) → LocalTables (B := AxisLeg m) (wires a) F),
    0 < A ∧
    (∀ x, crossingTensor F D m x = ∑ a, network (wires a) (T a) x) ∧
    (∀ a, ∑ t, wireCost (fun p q => dist (axisPoint p) (axisPoint q)) (wires a t) ≤ budget) ∧
    budget + 2 * D * Real.logb 2 A < 2 * D * m

/-- A strict spectral comparison giving the stated repeated restrictions supplies
a concrete shortening, after paying for selection among all powers of the wires. -/
theorem exists_shortenedCrossing {F X : Type*} [CommSemiring F] [TopologicalSpace X]
    [CompactSpace X] {D : ℕ} (hD : 2 ≤ D)
    (price : AxisPair D → X → ℝ) (crossing : X → ℝ)
    (hprice : ∀ e, Continuous (price e)) (hcrossing : Continuous crossing)
    (hnonneg : ∀ e x, 0 ≤ price e x)
    (hstrict : ∀ x, ∃ e, crossing x < (2 * D / axisLength e) * price e x)
    (comparison : ∀ (m : ℕ), 0 < m → ∀ b : AxisPair D → ℕ, (∀ e, 0 < b e) →
      (∀ x, ∃ e, (m : ℝ) * crossing x < b e * price e x) →
      ∃ K : ℕ, 0 < K ∧ ∀ j : ℕ, 0 < j → RestrictsWirePower (crossingTensor F D (m * j))
        (fun e => axisWire e (b e)) K j) :
    ∃ n : ℕ, 0 < n ∧ ShortenedCrossing F D n := by
  classical
  let i : Fin D := ⟨0, by omega⟩
  have : Nonempty (AxisPair D) := ⟨⟨Sym2.mk none (some (i, true)), by simp⟩⟩
  obtain ⟨m, hm, b, hb, hcover, hbudget⟩ := exists_shorter_wire_products (by omega : 0 < D)
    axisLength axisLength_pos price crossing hprice hcrossing hnonneg hstrict
  obtain ⟨K, hK, hres⟩ := comparison m hm b hb hcover
  obtain ⟨j, hj, v, hcost, hsave⟩ := hbudget K hK
  let wire e := axisWire e (b e)
  obtain ⟨T, hT⟩ := restriction_copiesOfWirePower wire (crossingTensor F D (m * j)) (hres j hj)
  let W := Fin K × (Fin j → AxisPair D)
  let ord := Fintype.equivFin W
  refine ⟨m * j, Nat.mul_pos hm hj, Fintype.card W, v, fun _ => j,
    fun a => wire ∘ (ord.symm a).2, fun a => T (ord.symm a).1 (ord.symm a).2, ?_, ?_, ?_, ?_⟩
  · have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
    exact Fintype.card_pos
  · intro x
    rw [hT, ← Fintype.sum_prod_type']
    exact (ord.symm.sum_comp _).symm
  · exact fun a => hcost (ord.symm a).2
  · simpa [W, mul_assoc] using hsave

end
end Crossing

end SpectralBooks
end LinearAlgebra
end OAI
