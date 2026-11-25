import OAI.Hierarchy.FactorBucketPass
import OAI.Hierarchy.RectangularWordScan

namespace OAI
/-! # The whole native threshold pass produces the geometric digits -/

namespace Hierarchy.FactorBucketRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {width : ℕ}

theorem div_mod_word {a b : ℕ} (smallA : a<2^width) (smallB : b<2^width) :
    BinaryOp.div.eval (a:Word width) (b:Word width) = ((a/b:ℕ):Word width) ∧
    BinaryOp.mod.eval (a:Word width) (b:Word width) = ((a%b:ℕ):Word width) := by
  simp [BinaryOp.eval,Fin.val_cast_of_lt smallA,Fin.val_cast_of_lt smallB]

theorem coordinates {cols row col : ℕ} (small : row*cols+col<2^width)
    (size : cols<2^width) (lt : col<cols) :
    BinaryOp.div.eval ((row*cols+col:ℕ):Word width) (cols:Word width)=(row:Word width) ∧
    BinaryOp.mod.eval ((row*cols+col:ℕ):Word width) (cols:Word width)=(col:Word width) := by
  have pos : 0<cols := by omega
  simpa [Nat.add_comm (row*cols),Nat.add_mul_div_right _ _ pos,Nat.div_eq_of_lt lt,
    Nat.mod_eq_of_lt lt] using div_mod_word small size

private theorem bits_before {rows cols r j : ℕ} (hr : r<rows) (hj : j<cols) :
    r*cols+j<rows*cols := by
  have h := Nat.mul_le_mul_right cols (Nat.succ_le_of_lt hr)
  rw [Nat.succ_mul] at h
  omega

/-- Immutable inputs before the digit scratch bank survive every prefix of
the first pass. -/
theorem digit_frame (v : Parameters width) (m : Memory width) (rows s digitBase : ℕ)
    (pos : 0<s) (sFit : s<2^width) (nFit : rows*s<2^width) (addrFit : digitBase+rows≤2^width)
    (pChannels : v 1=(s:Word width)) (pd : v 7=(digitBase:Word width)) (n : ℕ) (hn : n≤rows*s)
    (a : ℕ) (ha : a<digitBase) : iterRows digitStep v m n a = m a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have less : n<rows*s := by omega
    have rowBound : n/s<rows := (Nat.div_lt_iff_lt_mul pos).mpr less
    have ab : digitBase+n/s<2^width := by omega
    have dv := (div_mod_word (less.trans nFit) sFit).1
    simp only [iterRows,digitStep,pChannels,dv,pd,←Nat.cast_add]
    rw [GridPassageRAMRow.writeMemory_nat _ _ ab,Function.update_of_ne (ha.trans_le (Nat.le_add_right digitBase (n/s))).ne]
    exact ih (by omega)

/-- Inputs and thresholds both lie below the scratch digit area. All reads
therefore see the original tables throughout the pass. -/
theorem digit_table (w rows resourceBase thresholdBase digitBase : ℕ) (v : Parameters width)
    (m : Memory width) (resource : ℕ → ℕ)
    (pChannels : v 1=((20*(w+1)+1:ℕ):Word width)) (pr : v 5=(resourceBase:Word width))
    (pt : v 6=(thresholdBase:Word width)) (pd : v 7=(digitBase:Word width))
    (belowR : resourceBase+rows≤digitBase) (belowT : thresholdBase+(20*(w+1)+1)≤digitBase)
    (addrFit : digitBase+rows≤2^width) (nFit : rows*(20*(w+1)+1)<2^width)
    (sFit : 20*(w+1)+1<2^width)
    (xAt : ∀ r<rows, (m (resourceBase+r)).val=resource r)
    (tAt : ∀ j≤20*(w+1), (m (thresholdBase+j)).val=FactorBucket.threshold j) :
    ∀ r<rows, iterRows digitStep v m (rows*(20*(w+1)+1)) (digitBase+r) =
      ((FactorBucket.label w (resource r)).val:Word width) := by
  let s := 20*(w+1)+1
  let mem := iterRows digitStep v m
  have pos : 0<s := Nat.succ_pos _
  have below (n : ℕ) (hn : n≤rows*s) (a : ℕ) (ha : a<digitBase) : mem n a = m a :=
    digit_frame v m rows s digitBase pos sFit nFit addrFit pChannels pd n hn a ha
  have row (r j : ℕ) (hr : r<rows) (hj : j<s) :
      mem (r*s+j+1) = Function.update (mem (r*s+j)) (digitBase+r)
        (if FactorBucket.threshold j≤resource r then ((j+1:ℕ):Word width)
         else if j=0 then 0 else mem (r*s+j) (digitBase+r)) := by
    have less := bits_before hr hj
    obtain ⟨rd,cd⟩ := coordinates (width:=width) (less.trans nFit) sFit hj
    apply digit_natural v _ _ r j (pChannels ▸ rd) (pChannels ▸ cd) (hj.trans sFit)
      resourceBase thresholdBase digitBase pr pt pd (by omega) (by omega) (by omega) (resource r)
    · change (mem (r*s+j) (resourceBase+r)).val=resource r
      rw [below _ less.le (resourceBase+r) (by omega),xAt _ hr]
    · change (mem (r*s+j) (thresholdBase+j)).val=FactorBucket.threshold j
      have jj : j≤20*(w+1) := by dsimp [s] at hj; omega
      rw [below _ less.le (thresholdBase+j) (by omega),tAt _ jj]
  have done := RectangularWordScan.result_of_step rows s digitBase pos mem
    (fun r j => (FactorBucket.scanned (resource r) j:Word width))
    (by
      intro r hr
      simpa [FactorBucket.scanned] using congrFun (row r 0 hr pos) (digitBase+r))
    (by
      intro r hr j hj prev
      have h := congrFun (row r (j+1) hr hj) (digitBase+r)
      simp only [Nat.add_assoc] at prev
      by_cases yes : FactorBucket.threshold (j+1)≤resource r <;>
        simpa [FactorBucket.scanned,Nat.add_assoc,yes,prev] using h)
    (by
      intro r hr j hj a ne
      rw [row r j hr hj,Function.update_of_ne ne])
  intro r hr
  simpa [s,FactorBucket.scanned_eq_label,mem] using done r hr

end Hierarchy.FactorBucketRAM

end OAI
