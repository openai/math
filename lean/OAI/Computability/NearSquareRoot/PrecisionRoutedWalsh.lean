import OAI.Computability.NearSquareRoot.PrecisionSlotTable
import OAI.Computability.NearSquareRoot.PrecisionPreparedGrid
import OAI.Computability.NearSquareRoot.SynchronizedRoutedWalsh

/-! # Finite phase records for a routed batch Walsh

The first active-pair-count labels in the completed physical route receive
unit phase. The remaining labels select one of six fixed eighth roots by the
phase round and designated address bit.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Strip Staff Carry Dusk Grid ShortFourier FixedPoint

variable {J : Type} {s : Regime J} {n m bits : J → ℕ}

/-- The header computes a routed Walsh phase using a binary comparison
against the active prefix length and a six-entry lookup on idle pairs. -/
theorem Prepared.routedWalsh (P : Realizes s bits) (round : J → Fin 3) (bit : J → Fin 2)
    (pair : (j : J) → Fin (n j))
    (R : Figure s (fun j => (round j).val)) (B : Figure s (fun j => (bit j).val))
    (Q : Figure s (fun j => (pair j).val)) (M : Figure s m) :
    Prepared s bits (fun j => RoutedWalsh.table (fun p : Fin (n j) => decide (p.val < m j))
      (round j) (bit j, pair j)) := by
  let i (j : J) : Fin 6 := ⟨2 * (round j).val + (bit j).val, by have := (round j).isLt; have := (bit j).isLt; omega⟩
  have I : Figure s (fun j => (i j).val) := ((Figure.natural 2).multiplied R).added B
  have h := Prepared.conditional (Q.compare_ M) (Prepared.one P) (Prepared.idleWalsh P i I)
  simpa only [RoutedWalsh.table, decide_eq_true_eq, i] using h

/-- The charged setup writes the routed phase in the grid format read by the
phase scan, with absolute complex error bounded by `2^(-70g)`. -/
theorem routedWalshRecord {g : J → ℕ} (G : Realizes s g) (round : J → Fin 3) (bit : J → Fin 2)
    (pair : (j : J) → Fin (n j))
    (R : Figure s (fun j => (round j).val)) (B : Figure s (fun j => (bit j).val))
    (Q : Figure s (fun j => (pair j).val)) (M : Figure s m) :
    ∃ output : (j : J) → Record (g j), s.Has (fun j => mark (output j)) ∧
      ∀ j, ‖FixedPoint.value (g j) (output j) -
        RoutedWalsh.table (fun p : Fin (n j) => decide (p.val < m j)) (round j) (bit j,pair j)‖
          ≤ 1 / (2 : ℝ) ^ (70 * g j) :=
  Prepared.toRecord G (fun _ => RoutedWalsh.table_norm ..)
    (Prepared.routedWalsh (((Realizes.fix 70).times G).plus (.fix 3)) round bit pair R B Q M)

end PhaseTable

end NearSquareRoot
end Computability
end OAI
