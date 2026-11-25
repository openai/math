import OAI.ThreeFlat.Diagonal.TraceVolumeArithmetic
import OAI.ThreeFlat.Diagonal.TraceDiagonalBudget
import OAI.ThreeFlat.Diagonal.TraceBitNetwork

namespace OAI
/-! # A common native tick template within volume V -/

namespace ThreeFlat.Diagonal.TraceVolume

open Computability.VPVNP BurstRAM TraceStaticRow

/-- The thresholds are constants and the field order. They can be met
without reference to the fixed native evaluator or the global speedup.
The bound counts actual shared wires, public bits, private bits, cells,
packing both local tables, and generating all eleven words of every cell. -/
theorem actual_work_le {F : Type*} [CommRing F] [Fintype F] {u S f : ℕ}
    (hu : 10^26*17^14 ≤ u) (hq : Fintype.card F ≤ u)
    (hF : Fintype.card F ≤ 2^(16*u^10)) (hw : 3 ≤ 16*u^10+1) (hp : u ≤ 2^(16*u^10+1))
    (base : ℕ) (st : Word (16*u^10)) (grid : S+f ≤ 2^(1+depth u)) :
    let W := 16*u^10
    let c := (gateTable hF hw hp base f st u u (depth u)).cells
    let h := (gateTable hF hw hp base f st u u (depth u)).internal
    let a := Fintype.card (Port W u u u (depth u))
    ∀ binds ≤ bindAllowance c a, work (2^(depth u)) S (TraceUniformRow.SharedCount W u u u (depth u) f)
      h c a W binds ≤ 2^(u^10) := by
  intro W c h a b hb
  have hu' : 50000 ≤ u := by omega
  have hd : depth u ≤ 15*u^10 := by have := depth_le u; omega
  have h128 : 128 ≤ u := by omega
  have cfit : c ≤ u^141 := (diagonal_gateTable h128 hq hd hF hw hp base f st).trans <| calc
    _ ≤ u*u^140 := Nat.mul_le_mul_right _ hu
    _ = u^141 := by ring
  have hconst : 400*18^3 ≤ u := by omega
  have pfit : a ≤ u^141 := by
    change Fintype.card (Port (16*u^10) u u u (depth u)) ≤ _
    rw [card_ports]
    exact (diagonal_ports_bound h128 hd).trans <| calc
      _ ≤ u*u^30 := Nat.mul_le_mul_right _ hconst
      _ = u^31 := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have hsum : S+f ≤ 2*2^(depth u) := by simpa only [pow_add,pow_one] using grid
  have sh := shared_le (w:=W) (p:=u) (r:=u) (k:=u) (d:=depth u) (f:=f) (by omega)
  exact work_le_volume hu' cfit pfit (by omega) (by simpa only [a,card_ports] using sh)
    (table_internal_le_cells hF hw hp base f st u u (depth u)) hb

end ThreeFlat.Diagonal.TraceVolume

end OAI
