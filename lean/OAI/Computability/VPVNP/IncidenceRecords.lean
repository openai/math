import OAI.Computability.VPVNP.IncidenceScan
import OAI.Computability.VPVNP.InterleavedPinning

/-! # Physical encoding of a selected set of columns

The row test in the read-only machine counts selected columns incident with the
row. Each column occupies the same number of cells in the pinned input layout.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace IncidenceMachine

open InterleavedPinning

variable {m k : ℕ}

/-- Column records in the order visited by the machine. -/
def records (M : Fin m → Fin k → Bool) (x : Fin k → Bool) : List (Column m) :=
  (List.finRange k).map (fun i => (x i, fun r => M r i))

theorem hits_records (M : Fin m → Fin k → Bool) (x : Fin k → Bool) (r : Fin m) :
    rowHits r (records M x) = 1 ↔ ∃! i, x i = true ∧ M r i = true := by
  let hit (i : Fin k) := x i && M r i
  have hc := (List.nodup_finRange k).card_eq_countP (P := fun i => hit i = true)
  simp only [Bool.decide_eq_true] at hc
  simp only [rowHits, records, List.countP_map]
  change (List.finRange k).countP hit = 1 ↔ _
  rw [← hc, Finset.card_eq_one_iff_existsUnique]
  simp [hit]

theorem length_rowBits_records (M : Fin m → Fin k → Bool) (x : Fin k → Bool) :
    (rowBits (records M x)).length = k * (m + 2) + 1 := by
  have h (cs : List (Column m)) : (cs.flatMap columnBits).length = cs.length * (m + 2) := by
    induction cs with
    | nil => simp
    | cons c cs ih => simp [columnBits, ih, Nat.add_mul]; omega
  simp [rowBits, h, records]

/-- Filling the prescribed incidence bits gives the machine's actual input. -/
theorem fill_records (padded : List Bool) (M : Fin m → Fin k → Bool) (x : Fin k → Bool) :
    List.ofFn (fill (recordLayout padded (fun i => List.ofFn (fun r => M r i))).get x) =
      padded ++ (rowBits (records M x)).reverse := by
  rw [recordLayout_fill]
  simp [rowBits, records, List.flatMap_map, columnBits]

theorem length_recordLayout (padded : List Bool) (M : Fin m → Fin k → Bool) :
    (recordLayout padded (fun i => List.ofFn (fun r => M r i))).length =
      padded.length + k * (m + 2) + 1 := by
  have h := congrArg List.length (fill_records padded M (fun _ => false))
  simpa [length_rowBits_records, Nat.add_assoc] using h

end IncidenceMachine

end VPVNP
end Computability
end OAI
