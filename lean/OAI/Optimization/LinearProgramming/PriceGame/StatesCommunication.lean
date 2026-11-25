import OAI.Optimization.LinearProgramming.PriceGame.StatesFeedback
import OAI.Optimization.LinearProgramming.PriceGame.QueryWire
import OAI.Optimization.LinearProgramming.PriceGame.ComputationIO

/-! The complete wire cost of each feedback vector, including branch-dependent free labels. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

variable {N : ℕ} {α : Type*} {B : ℕ}

/-- All individual prices in a query obey the binary encoding bound of the arithmetic RAM. -/
def PricesBounded (B : ℕ) (q : Query N) : Prop := ∀ i, RAM.ratBits (q.prices i) ≤ B

theorem Computation.allQueries_mono (P Q : Query N → Prop) (f : ∀ q, P q → Q q)
    (p : Computation N α) (hp : p.AllQueries P) : p.AllQueries Q := by
  induction p with
  | pure => exact True.intro
  | ask q next ih => exact ⟨f q hp.1, fun b => ih b (hp.2 b)⟩

/-- Worst-case bits written and read, with the signed, self-delimiting rational
encoding and fixed-width designation, for arbitrary history-dependent answers. -/
theorem query_bits_le (p : Computation N α) (h : p.AllQueries (PricesBounded B))
    (reply : List (Query N × Bool) → Query N → Bool) (history : List (Query N × Bool)) :
    (p.runMetered (Computation.wireCost Wire.query) reply history).2 ≤
      p.height * (N * (2 * B + 1) + (N.log2 + 1) + 1) := by
  apply Computation.communication_le
  exact Computation.allQueries_mono _ _ (fun q hq => Wire.query_length_le q B hq) _ h

namespace States

private theorem bounded_median {J : Type} (y : J → ℚ) (x : J × Bool → ℚ)
    (hy : ∀ i, RAM.ratBits (y i) ≤ B) (hx : ∀ i, RAM.ratBits (x i) ≤ B) (i : J) :
    RAM.ratBits (parentPrices y x i) ≤ B := by
  simp only [parentPrices, median₃, max_def, min_def]
  split_ifs <;> first | exact hy _ | exact hx _

theorem feedbackAt_pricesBounded {J : Type} (p : Path (Fin N) J) (y : J → ℚ)
    (x : J × Bool → ℚ) (i : J)
    (bases : p.pricesSatisfy (fun v => RAM.ratBits v ≤ B))
    (hy : ∀ j, RAM.ratBits (y j) ≤ B) (hx : ∀ j, RAM.ratBits (x j) ≤ B) :
    (Computation.ofTree (feedbackAt p y x i)).AllQueries (PricesBounded B) := by
  simp only [feedbackAt]
  split_ifs
  · exact True.intro
  · exact True.intro
  · refine ⟨?_, fun _ => True.intro⟩
    exact rootQuery_pricesSatisfy _ p bases _ (bounded_median y x hy hx) i

theorem feedbackAll_pricesBounded {l : ℕ} (p : Path (Fin N) (Mass.Vertex N l))
    (y : Mass.Vertex N l → ℚ) (x : Mass.Vertex N (l + 1) → ℚ)
    (bases : p.pricesSatisfy (fun v => RAM.ratBits v ≤ B))
    (hy : ∀ i, RAM.ratBits (y i) ≤ B) (hx : ∀ i, RAM.ratBits (x i) ≤ B) :
    (feedbackAll p y x).AllQueries (PricesBounded B) := by
  apply Computation.allQueries_map
  exact Computation.allQueries_traverse _ _ (fun i _ => feedbackAt_pricesBounded p y x i bases hy hx)

/-- A complete probe writes all root-query fields and reads all reply bits within
a bound explicit in the actual coordinate count and maximum input price size. -/
theorem feedbackAll_communication {l : ℕ} (p : Path (Fin N) (Mass.Vertex N l))
    (y : Mass.Vertex N l → ℚ) (x : Mass.Vertex N (l + 1) → ℚ)
    (bases : p.pricesSatisfy (fun v => RAM.ratBits v ≤ B))
    (hy : ∀ i, RAM.ratBits (y i) ≤ B) (hx : ∀ i, RAM.ratBits (x i) ≤ B)
    (reply : List (Query N × Bool) → Query N → Bool) (history : List (Query N × Bool)) :
    ((feedbackAll p y x).runMetered (Computation.wireCost Wire.query) reply history).2 ≤
      Fintype.card (Mass.Vertex N l) * (N * (2 * B + 1) + (N.log2 + 1) + 1) :=
  (query_bits_le _ (feedbackAll_pricesBounded p y x bases hy hx) reply history).trans
    (Nat.mul_le_mul_right _ (feedbackAll_height p y x))

end States
end PriceGame
end LinearProgramming
end Optimization
end OAI
