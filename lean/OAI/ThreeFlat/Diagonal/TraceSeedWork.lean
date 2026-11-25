import OAI.ThreeFlat.Diagonal.TraceSeedPriceTerm
import OAI.ThreeFlat.Diagonal.TraceDiagonalBudget
import OAI.ThreeFlat.RAM.TraceStrideBound

namespace OAI
/-! # A fixed polynomial multiplier for the true H leaf resource charge -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM TraceSourceOwner RAM.TraceBucketAtom
open scoped BigOperators Classical

variable {F : Type*} [Fintype F] [CommRing F] {u S f d : ℕ}
variable (hF : Fintype.card F≤2^(16*u^10)) (hw : 3≤(16*u^10)+1) (hp : u≤2^((16*u^10)+1)) (base : ℕ) (st : Word (16*u^10))

/-- The initial number of trivalent half-word ordinals per physical low row.
The exponent is independent of the H fuel-saving parameter and of the chosen block. -/
theorem seedSlots_le (hu : 128≤u) (constant : 10^26*17^14≤u)
    (hq : Fintype.card F≤u) (hd : d≤15*u^10) :
    (1+(d+d))*(TraceStaticRow.gateTable hF hw hp base f st u u d).cells*3≤u^152 := by
  have up : 0<u := by omega
  have lim := TraceStaticRow.diagonal_gateTable hu hq hd hF hw hp base f st
  have upper : 10^26*17^14*u^140≤u^141 := by
    change 10^26*17^14*u^140≤u^(140+1)
    rw [pow_succ u 140,Nat.mul_comm (u^140) u]
    exact Nat.mul_le_mul_right _ constant
  have cells : (TraceStaticRow.gateTable hF hw hp base f st u u d).cells≤u^141 := lim.trans upper
  have off : 1+(d+d)≤31*u^10 := by have hpow : 0<u^10 := Nat.pow_pos up; omega
  calc
    _ ≤ ((31*u^10)*u^141)*3 := Nat.mul_le_mul_right _ (Nat.mul_le_mul off cells)
    _ = 93*u^151 := by ring
    _ ≤ u^152 := by
      rw [pow_succ u 151,Nat.mul_comm (u^151) u]
      exact Nat.mul_le_mul_right _ (by omega)

theorem seedTraceWork_le (low copies : ℕ) (_hu : 5000≤u) (constant : 10^26*17^14≤u)
    (hq : Fintype.card F≤u) (hd : d≤15*u^10) (degree : (copies+1)*2≤u) :
    seedTraceWork low (TraceSourceOwner.shape (16*u^10) u u u S f d (TraceStaticRow.gateTable hF hw hp base f st u u d).internal).stride (TraceStaticRow.gateTable hF hw hp base f st u u d).cells copies d≤2^low*u^160 := by
  have up : 0<u := by omega
  have mono {a b : ℕ} (m : a≤b) : u^a≤u^b := Nat.pow_le_pow_right up m
  have self : u≤u^10 := Nat.le_self_pow (by decide) _
  have small : (16*u^10)+1≤u^11 := by
    have a := Nat.mul_le_mul_left (u^10) (by omega : 17≤u)
    have b : 0<u^10 := Nat.pow_pos up
    rw [pow_succ u 10]; omega
  have pub : u≤1*((16*u^10)+1)^1 := by simp; omega
  have port := TraceAddressRecord.portRowWords_polynomial (w:=(16*u^10)) (d:=d) (by omega) pub pub pub
  have ports : TraceAddressRecord.portRowWords (16*u^10) u u u d≤u^45 := by
    calc
      _ ≤ 128*(u^11)^4 := by norm_num at port; exact port.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left small _))
      _ = 128*u^44 := by rw [←pow_mul]
      _ ≤ u^45 := by rw [pow_succ u 44,Nat.mul_comm (u^44) u]; exact Nat.mul_le_mul_right _ (by omega)
  have dc := TraceStaticRow.diagonal_gateTable (by omega : 128≤u) hq hd hF hw hp base f st
  have upper : 10^26*17^14*u^140≤u^141 := by
    change 10^26*17^14*u^140≤u^(140+1)
    rw [pow_succ u 140,Nat.mul_comm (u^140) u]
    exact Nat.mul_le_mul_right _ constant
  have cells : (TraceStaticRow.gateTable hF hw hp base f st u u d).cells≤u^141 := dc.trans upper
  have privateBits := (TraceStaticRow.table_internal_le_cells hF hw hp base f st u u d).trans cells
  have stride := (stride_le_ports (16*u^10) u u u S f d (TraceStaticRow.gateTable hF hw hp base f st u u d).internal).trans
    (Nat.add_le_add (Nat.mul_le_mul_left 2 ports) privateBits)
  have large : 2*u^45+u^141≤u^150 := by
    have a := mono (by decide : 45≤141)
    have b := Nat.mul_le_mul_left (u^141) (by omega : 3≤u)
    have c := mono (by decide : 142≤150)
    rw [pow_succ u 141] at c
    omega
  have stride' : (TraceSourceOwner.shape (16*u^10) u u u S f d (TraceStaticRow.gateTable hF hw hp base f st u u d).internal).stride≤u^150 := stride.trans large
  have offsets : 1+(d+d)≤31*u^10 := by have hpow : 0<u^10 := Nat.pow_pos up; omega
  have halves : copies+1≤u := by omega
  have routed : 12*(copies+1)*(1+(d+d))*(TraceStaticRow.gateTable hF hw hp base f st u u d).cells≤372*u^152 := calc
    _ ≤ 12*u*(31*u^10)*u^141 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ halves) offsets) cells
    _ = 372*u^152 := by ring
  have cost : 1+(2*(TraceSourceOwner.shape (16*u^10) u u u S f d (TraceStaticRow.gateTable hF hw hp base f st u u d).internal).stride+(TraceStaticRow.gateTable hF hw hp base f st u u d).cells+12*(copies+1)*(1+(d+d))*(TraceStaticRow.gateTable hF hw hp base f st u u d).cells)≤u^160 := by
    have m := mono (by decide : 150≤152)
    have n := mono (by decide : 141≤152)
    have one : 1≤u^152 := Nat.pow_pos up
    have c : 376*u^152≤u^153 := by
      rw [pow_succ u 152,Nat.mul_comm (u^152) u]
      exact Nat.mul_le_mul_right _ (by omega)
    exact (show _≤376*u^152 by omega).trans (c.trans (mono (by decide)))
  unfold seedTraceWork
  have localCount : 1≤2^low := Nat.two_pow_pos _
  have z := Nat.mul_le_mul_left (2^low) cost
  rw [Nat.mul_add,Nat.mul_one] at z
  omega

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
