import OAI.Optimization.LinearProgramming.Lattice.Oracle
import OAI.Optimization.LinearProgramming.Lattice.ProjectionGram
import OAI.Optimization.LinearProgramming.Lattice.QuerySize

/-! Size of every integer form queried in the adaptive sign-preserving algorithm. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open SignType WithLp

private theorem digitSize (p M : ℕ) :
    (searchDenominator p M ^ (p + 1) + 1).size ≤ precisionExponent p M * (p + 1) + 2 := by
  apply Nat.size_le.mpr
  rw [searchDenominator, ← pow_mul, pow_add]
  have := Nat.one_le_two_pow (n := precisionExponent p M * (p + 1))
  omega

/-- Degree-five polynomial bound (in `p` and the bit length of `M`) on the magnitude bits
of each coefficient queried. It covers queries made even at the final zero test. -/
def queryCoefficientWidth (p M : ℕ) : ℕ :=
  let r := precisionExponent p M * (p + 1) + 2
  let L := (2 * p + 2 * r) * p + 1
  searchPrecision p M + 1 + L * (p * p + 1)

theorem roundingProgramWith_query_size {p M : ℕ} (hp : 0 < p) (hM : 0 < M)
    (select : (Fin p → ℚ) → ℕ × (Fin p → ℤ))
    (hsel : ∀ u, 0 < (select u).1 ∧ (select u).1 ≤ searchDenominator p M ^ (p + 1) ∧
      ∀ i, |((select u).1 : ℚ) * u i - (select u).2 i| ≤ 1 / (8 * (p : ℚ) * M))
    (v : Fin p → ℝ) (oracle : (Fin p → ℤ) → Bool)
    (hOracle : ∀ c, oracle c = true ↔ 0 ≤ formValue c v)
    {row : Fin p → ℤ} (hm : row ∈ SignQueries.history oracle (roundingProgramWith M select)) (j : Fin p) :
    (row j).natAbs.size ≤ queryCoefficientWidth p M := by
  let D := searchDenominator p M ^ (p + 1) + 1
  let L := (2 * p + 2 * (precisionExponent p M * (p + 1) + 2)) * p + 1
  let probe old := SignQueries.run oracle (probeRowsQ (rationalResidualMatrix old) (searchPrecision p M))
  have hzero := fun old => (residualProbe_correct (M := M) v oracle hOracle old).1
  have herr := fun old => (residualProbe_correct (M := M) v oracle hOracle old).2
  have go (k : ℕ) (old : List (Fin p → ℤ)) (hkp : old.length + k ≤ p)
      (hb : ∀ z ∈ old, ∀ i, (z i).natAbs ≤ D)
      (hli : LinearIndependent ℝ (fun i : Fin old.length => toLp 2 (realCoordinates (old.get i))))
      (hrow : row ∈ SignQueries.history oracle (directionsQ M select k old)) :
      (row j).natAbs.size ≤ queryCoefficientWidth p M := by
    induction k generalizing old with
    | zero => simp [directionsQ, SignQueries.history] at hrow
    | succ k ih =>
      rw [directionsQ, residualTableMatrix_eq, SignQueries.history_bind, List.mem_append] at hrow
      rcases hrow with hrow | hrow
      · cases h : probe old with
        | none =>
          change row ∈ SignQueries.history oracle (match probe old with | none => _ | some _ => _) at hrow
          simp [h, SignQueries.history] at hrow
        | some u =>
          change row ∈ SignQueries.history oracle (match probe old with | none => _ | some _ => _) at hrow
          simp only [h, SignQueries.history_bind, SignQueries.history, List.nil_append] at hrow
          let z := (select u).2
          have hnext : selectedDirection probe select old = some z := by simp [selectedDirection, h, z]
          have hs := selectedDirection_correct hp hM v probe select hzero herr hsel old z hnext
          apply ih (z :: old) (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hkp) _
            (integerDirectionList_independent_cons old z hli hs.2.1) hrow
          intro a ha i
          rcases List.mem_cons.mp ha with rfl | ha
          · have ht : ((z i).natAbs : ℤ) ≤ D := by simpa only [Int.natCast_natAbs] using hs.1 i
            exact_mod_cast ht
          · exact hb a ha i
      · have hmtrx (i l : Fin p) :
            ((rationalResidualMatrix old i l).num.natAbs.size ≤ L) ∧
              (rationalResidualMatrix old i l).den.size ≤ L := by
          have hh := rationalResidualMatrix_entry_size old (by omega) hb hli i l
          have hL : (2 * p + 2 * D.size) * p + 1 ≤ L := by
            dsimp [L]
            gcongr
            exact digitSize p M
          exact ⟨hh.1.trans hL, hh.2.trans hL⟩
        exact probeRowsQ_natAbs_size oracle _ _ hmtrx hrow j
  simp only [roundingProgramWith, SignQueries.history_bind, SignQueries.history, List.nil_append] at hm
  let : IsEmpty (Fin ([] : List (Fin p → ℤ)).length) := inferInstanceAs (IsEmpty (Fin 0))
  exact go p [] (by simp) (by simp) linearIndependent_empty_type hm

end Lattice
end LinearProgramming
end Optimization
end OAI
