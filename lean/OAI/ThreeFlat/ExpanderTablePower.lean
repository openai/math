import OAI.Computability.BinPacking.Expanders.ExpanderTableEnumeration

namespace OAI
/-! # Squaring a tabulated regular graph

A squared port stores an ordered pair of old ports in mixed-radix order.
Reversing the resulting walk interchanges its two return ports. Computing
one new rotation row reads the old rotation table twice.
-/

namespace ThreeFlat.RouteUnits

open BinPackingGames.Foundations.PCP
open ExpanderTables SpectralReturn
open scoped BigOperators

/-- The table of length-two walks on the same vertices. -/
def squareTable {v q : ℕ} (T : Table v q) : Table v (q * q) :=
  ofGraph (GraphTransport.reindex (ZigzagGraphs.square (graph T))
    (Equiv.refl _) (rowIndex q q))

theorem lookup_squareTable {v q : ℕ} (T : Table v q) (x : Fin v × Fin (q * q)) :
    lookup (squareTable T) x =
      let ports := (rowIndex q q).symm x.2
      let first := lookup T (x.1, ports.1)
      let second := lookup T (first.1, ports.2)
      (second.1, rowIndex q q (second.2, first.2)) := by
  rw [squareTable, lookup_ofGraph]
  rfl

/-- A rotation row can be filled using two reads of the preceding table,
division and remainder for the mixed-radix fields, and integer arithmetic. -/
theorem squareTable_row_value {v q : ℕ} (T : Table v q) (x : Fin v × Fin (q * q)) :
    (reverseIndex (squareTable T) (rowIndex v (q * q) x)).val =
      let ports := (rowIndex q q).symm x.2
      let first := reverseIndex T (rowIndex v q (x.1, ports.1))
      let second := reverseIndex T (rowIndex v q (((rowIndex v q).symm first).1, ports.2))
      (first.val % q + q * (second.val % q)) + (q * q) * (second.val / q) := by
  rw [← ExpanderRowControl.rowIndex_lookup, lookup_squareTable]
  rfl

theorem squareTable_certificate {v q : ℕ} [NeZero v] [NeZero q]
    (T : Table v q) {lam : ℝ} (cert : SpectralCertificate (graph T) lam) :
    SpectralCertificate (graph (squareTable T)) (lam ^ 2) := by
  rw [squareTable, graph_ofGraph]
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    (ZigzagSpectral.square_certificate _ _ cert)

/-- The port count after repeated squaring, in the order used by `squareTable`. -/
def powerDegree (q : ℕ) : ℕ → ℕ
  | 0 => q
  | j + 1 => powerDegree q j * powerDegree q j

theorem powerDegree_eq (q j : ℕ) : powerDegree q j = q ^ (2 ^ j) := by
  induction j with
  | zero => simp [powerDegree]
  | succ j ih => rw [powerDegree, ih, pow_succ 2 j, pow_mul, pow_two]

def poweredTable {v q : ℕ} (T : Table v q) : (j : ℕ) → Table v (powerDegree q j)
  | 0 => T
  | j + 1 => squareTable (poweredTable T j)

theorem poweredTable_certificate {v q : ℕ} [NeZero v] [NeZero q]
    (T : Table v q) {lam : ℝ} (cert : SpectralCertificate (graph T) lam) (j : ℕ) :
    SpectralCertificate (graph (poweredTable T j)) (lam ^ (2 ^ j)) := by
  induction j with
  | zero =>
    change SpectralCertificate (graph T) (lam ^ (2 ^ 0))
    simpa only [pow_zero, pow_one] using cert
  | succ j ih =>
    let : NeZero (powerDegree q j) := ⟨by rw [powerDegree_eq]; exact pow_ne_zero _ (NeZero.ne q)⟩
    rw [pow_succ 2 j, pow_mul]
    exact squareTable_certificate _ ih

private theorem powerDegree_mono (q : ℕ) : Monotone (powerDegree q) := by
  apply monotone_nat_of_le_succ
  intro j
  change powerDegree q j ≤ powerDegree q j * powerDegree q j
  by_cases h : powerDegree q j = 0
  · simp [h]
  · exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h)

/-- Total rotation rows across all squaring stages, including the input
table, are bounded by the final row count times the number of stages. -/
theorem poweredTable_rows_le {v q : ℕ} (T : Table v q) (j : ℕ) :
    (∑ i ∈ Finset.range (j + 1), (poweredTable T i).rows.toList.length) ≤
      (j + 1) * (poweredTable T j).rows.toList.length := by
  simp only [row_count]
  calc
    _ ≤ ∑ _i ∈ Finset.range (j + 1), v * powerDegree q j :=
      Finset.sum_le_sum fun i hi =>
        Nat.mul_le_mul_left _ (powerDegree_mono q (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    _ = _ := by simp

end ThreeFlat.RouteUnits

end OAI
