import OAI.ThreeFlat.Diagonal.TraceBitRecordWord
import OAI.ThreeFlat.Diagonal.TraceBitAddresses
import OAI.ThreeFlat.Diagonal.TraceVolumePins
import OAI.ThreeFlat.RAM.CapacityBudget

namespace OAI
/-! # Word safety of every physical trace ROM record at the diagonal scale -/

namespace ThreeFlat.Diagonal.TraceAddressRecord

open TraceVolume

/-- At equal program, register, and table capacities the public polynomial
in the record bound is just the width plus one. -/
theorem staticBitPort_fits_at_scale {u S f base : ℕ} (hu : 5120 ≤ u)
    (hw : 3 ≤ 16*u^10+1) (grid : S+f ≤ 2^(1+depth u))
    (text : base+(1+6*u+u)*(16*u^10) ≤ S)
    (v : Fin (2^depth u)) (a : StaticPortIndex (16*u^10) u u u (depth u)) :
    (staticBitPort hw base S f a).Fits (16*u^10) v.val := by
  have threshold : RAM.traceWordThreshold (40*(64*(1+1))) (1+3) ≤ u := hu
  have cap : u ≤ 1*(16*u^10+1)^1 := by
    have low := Nat.le_self_pow (by decide : 10 ≠ 0) u
    simp only [pow_one,one_mul]
    omega
  exact staticBitPort_fits_of_public_bounds (c:=1) (e:=1) hw grid text threshold
    (by have := depth_le u; omega) cap cap cap v a

/-- The numeric table lookup used by the 430-bind ROM has all eight word
bounds of its underlying port, including the subtracted base and selected bit. -/
theorem bitRecords_fits_at_scale {u S f base : ℕ} (hu : 5120 ≤ u)
    (hw : 3 ≤ 16*u^10+1) (grid : S+f ≤ 2^(1+depth u))
    (text : base+(1+6*u+u)*(16*u^10) ≤ S)
    (v : Fin (2^depth u)) (j : Fin (Fintype.card (StaticPortIndex (16*u^10) u u u (depth u)))) :
    (TraceBitDescriptor.records hw base S f j).Fits (16*u^10) v.val :=
  staticBitPort_fits_at_scale hu hw grid text v ((Fintype.equivFin _).symm j)

/-- Four replaceable strings, the public parameters, and the advice segment
supply the grid and program-text bounds for every indexed native record. -/
theorem tick_bitRecords_fits {u e params base : ℕ} (hu : 5120 ≤ u) (he : e ≤ u)
    (hparams : params ≤ u^e) (hw : 3 ≤ 16*u^10+1)
    (hbase : base ≤ 4*2^(u^10-u^4)+params)
    (v : Fin (2^depth u)) (j : Fin (Fintype.card (StaticPortIndex (16*u^10) u u u (depth u)))) :
    (TraceBitDescriptor.records hw base ((4*2^(u^10-u^4)+params)+2^(u^3))
      (2^depth u) j).Fits (16*u^10) v.val := by
  have cutoff : cm ≤ u := by unfold cm; omega
  have grid := (tick_grid cutoff he hparams).2.2
  have text := RAM.CapacityPadding.text_add_advice_fit (by omega : 128 ≤ u)
  have program : (1+6*u+u)*(16*u^10) ≤ 2^(u^3) := (Nat.le_add_right _ _).trans text
  exact bitRecords_fits_at_scale hu hw grid (Nat.add_le_add hbase program) v j

end ThreeFlat.Diagonal.TraceAddressRecord

end OAI
