import OAI.ThreeFlat.Diagonal.TraceStaticCost
import OAI.ThreeFlat.RAM.CapacityBudget
import OAI.ThreeFlat.Diagonal.TraceIncidence

namespace OAI
/-! # An absolute layout exponent before choosing the diagonal speedup -/

namespace ThreeFlat.Diagonal.TraceStaticRow

open scoped Classical

theorem diagonal_gateTable {F : Type*} [CommRing F] [Fintype F] {u d : ℕ}
    (hu : 128 ≤ u) (hq : Fintype.card F ≤ u) (hd : d ≤ 15*u^10)
    (hF : Fintype.card F ≤ 2^(16*u^10)) (hw : 3 ≤ 16*u^10+1) (hp : u ≤ 2^(16*u^10+1))
    (base f : ℕ) (st : Computability.VPVNP.BurstRAM.Word (16*u^10)) :
    (gateTable hF hw hp base f st u u d).cells ≤ (10^26*17^14)*u^140 :=
  (gateTable_size hF hw hp base f st).trans (diagonal_cells_bound hu hq hd)

/-- All outgoing fanout branches of one row obey a common absolute bound
when the row table and the XOR mask list have their diagonal sizes. -/
theorem diagonal_incidence {F : Type*} {p u d lane low slots : ℕ} {N : BitNetwork F p}
    (P : LaneCursor.RowLayout N lane low (1+(d+d)) slots) (v : LaneCursor.Row lane low)
    (hu : 128 ≤ u) (hd : d ≤ 15*u^10) (hs : slots ≤ (10^26*17^14)*u^140) :
    Fintype.card {e : LaneCursor.Occurrence N // P.owner e = v} ≤ (93*(10^26*17^14))*u^150 := by
  classical
  have h10 := Nat.le_self_pow (by decide : 10 ≠ 0) u
  have hmask : 1+(d+d) ≤ 31*u^10 := by omega
  exact (P.outgoing_at_most v).trans <| calc
    _ ≤ (31*u^10)*(((10^26*17^14)*u^140)*3) := Nat.mul_le_mul hmask (Nat.mul_le_mul_right _ hs)
    _ = _ := by ring

end ThreeFlat.Diagonal.TraceStaticRow

end OAI
