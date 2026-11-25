import OAI.Hierarchy.FactorDigitPass
import OAI.Hierarchy.FactorKeyFold
import OAI.Hierarchy.FactorAllocation

namespace OAI
/-! # Correctness of the physical high-to-low key scan -/

namespace Hierarchy.FactorBucketRAM

open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing
variable {width : ℕ}

private theorem cell_lt {N d r j : ℕ} (hr : r<N) (hj : j<d) : r*d+j < N*d := by
  have h := Nat.mul_le_mul_right d (Nat.succ_le_of_lt hr)
  rw [Nat.succ_mul] at h
  omega

/-- No key step writes outside the key bank. -/
theorem key_frame {N d keyBase : ℕ} (v : Parameters width) (m : Memory width)
    (pd : v 2 = (d:Word width)) (pk : v 8 = (keyBase:Word width))
    (hd : 0<d) (smallD : d<2^width) (smallN : N*d<2^width)
    (fit : keyBase+N≤2^width) (n : ℕ) (hn : n≤N*d) (a : ℕ)
    (away : a<keyBase ∨ keyBase+N≤a) : iterRows keyStep v m n a = m a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have less : n<N*d := by omega
    have row : n/d<N := (Nat.div_lt_iff_lt_mul hd).mpr less
    have addr : keyBase+n/d<2^width := by omega
    have dv := (div_mod_word (width:=width) (less.trans smallN) smallD).1
    change keyStep v (n:Word width) (iterRows keyStep v m n) a = _
    simp only [keyStep,pd,dv,pk,← Nat.cast_add]
    have ne : a ≠ keyBase+n/d := by
      rcases away with low | high
      · exact (low.trans_le (Nat.le_add_right _ _)).ne
      · exact ((Nat.add_lt_add_left row keyBase).trans_le high).ne'
    rw [GridPassageRAMRow.writeMemory_nat _ _ addr, Function.update_of_ne ne]
    exact ih (by omega)

/-- Exact natural addresses and reset behavior of the native multiply-add. -/
theorem key_natural {d R digitBase keyBase r j : ℕ} (v : Parameters width) (m : Memory width)
    (pd : v 2=(d:Word width)) (pr : v 3=(R:Word width))
    (pds : v 7=(digitBase:Word width)) (pk : v 8=(keyBase:Word width))
    (hj : j<d) (smallD : d<2^width) (indexFit : r*d+j<2^width)
    (srcFit : digitBase+(r*d+(d-1-j))<2^width) (dstFit : keyBase+r<2^width) :
    keyStep v ((r*d+j:ℕ):Word width) m =
      Function.update m (keyBase+r)
        ((if j=0 then 0 else m (keyBase+r))*(R:Word width) + m (digitBase+(r*d+(d-1-j)))) := by
  obtain ⟨rd,cd⟩ := coordinates (width:=width) indexFit smallD hj
  have pred : (d:Word width)-1 = ((d-1:ℕ):Word width) := by
    rw [Nat.cast_sub (by omega : 1≤d), Nat.cast_one]
  have sub : ((d-1:ℕ):Word width)-(j:Word width) = ((d-1-j:ℕ):Word width) := by
    rw [Nat.cast_sub (by omega : j≤d-1)]
  have flag := (div_mod_word (width:=width) (hj.trans smallD) (hj.trans smallD)).1
  simp only [keyStep,pd,pr,pds,pk,rd,cd,pred,sub,← Nat.cast_mul,← Nat.cast_add,
    Fin.val_cast_of_lt srcFit,Fin.val_cast_of_lt dstFit]
  rw [GridPassageRAMRow.writeMemory_nat _ _ dstFit,flag]
  by_cases h : j=0
  · simp [h]
  · simp [h,Nat.div_self (Nat.pos_of_ne_zero h)]

/-- The native loop turns each little-endian row of bounded digits into its actual key word. -/
theorem key_table {N d R digitBase keyBase : ℕ} (v : Parameters width) (m : Memory width)
    (digits : Fin N → Fin d → Fin R)
    (pd : v 2=(d:Word width)) (pr : v 3=(R:Word width))
    (pds : v 7=(digitBase:Word width)) (pk : v 8=(keyBase:Word width))
    (hd : 0<d) (smallD : d<2^width) (smallN : N*d<2^width)
    (below : digitBase+N*d≤keyBase) (fit : keyBase+N≤2^width)
    (input : ∀ (i : Fin N) (j : Fin d),
      m (digitBase+(i.val*d+j.val)) = ((digits i j).val:Word width)) :
    ∀ i : Fin N, iterRows keyStep v m (N*d) (keyBase+i.val) =
      ((finFunctionFinEquiv (digits i)).val:Word width) := by
  let mem := iterRows keyStep v m
  let value (i j : ℕ) : Word width :=
    if hi : i<N then (keyPrefix (digits ⟨i,hi⟩) (j+1):Word width) else 0
  have row (i j : ℕ) (hi : i<N) (hj : j<d) :
      mem (i*d+j+1) = Function.update (mem (i*d+j)) (keyBase+i)
        ((if j=0 then 0 else mem (i*d+j) (keyBase+i))*(R:Word width) +
          (keyDigit (digits ⟨i,hi⟩) (d-1-j):Word width)) := by
    have rev : d-1-j<d := by omega
    have less := cell_lt hi hj
    have lessRev := cell_lt hi rev
    have src : digitBase+(i*d+(d-1-j))<keyBase := by omega
    change keyStep v ((i*d+j:ℕ):Word width) (mem (i*d+j)) = _
    rw [key_natural v _ pd pr pds pk hj smallD (less.trans smallN) (by omega) (by omega)]
    have orig := key_frame v m pd pk hd smallD smallN fit (i*d+j) less.le _ (Or.inl src)
    change mem (i*d+j) (digitBase+(i*d+(d-1-j))) = _ at orig
    rw [orig,input ⟨i,hi⟩ ⟨d-1-j,rev⟩]
    simp [keyDigit,rev]
  have done := RectangularWordScan.result_of_step N d keyBase hd mem value
    (by
      intro i hi
      have eq := congrFun (row i 0 hi hd) (keyBase+i)
      simpa [value,hi,keyPrefix_succ _ 0 hd] using eq)
    (by
      intro i hi j hj prev
      have eq := congrFun (row i (j+1) hi hj) (keyBase+i)
      simp only [value, dite_eq_left hi] at prev ⊢
      simp only [Nat.add_assoc] at eq prev ⊢
      simpa [prev,keyPrefix_succ _ (j+1) hj] using eq)
    (by
      intro i hi j hj a ne
      rw [row i j hi hj,Function.update_of_ne ne])
  intro i
  have lastCol : d-1+1=d := by omega
  simpa [value,i.isLt,lastCol,keyPrefix_done,mem] using done i.val i.isLt

/-- Applying the generic pass to the geometric resource digits produces the
index used to address the bucket counter. -/
theorem bucket_key_table {N d w digitBase keyBase : ℕ} (v : Parameters width) (m : Memory width)
    (cost : Fin N → Fin d → ℕ)
    (pd : v 2=(d:Word width)) (pr : v 3=((20*(w+1)+2:ℕ):Word width))
    (pds : v 7=(digitBase:Word width)) (pk : v 8=(keyBase:Word width))
    (hd : 0<d) (smallD : d<2^width) (smallN : N*d<2^width)
    (below : digitBase+N*d≤keyBase) (fit : keyBase+N≤2^width)
    (input : ∀ (i : Fin N) (j : Fin d),
      m (digitBase+(i.val*d+j.val)) = ((FactorBucket.label w (cost i j)).val:Word width)) :
    ∀ i : Fin N, iterRows keyStep v m (N*d) (keyBase+i.val) =
      ((finFunctionFinEquiv (FactorAllocation.key w cost i)).val:Word width) :=
  key_table v m (FactorAllocation.key w cost) pd pr pds pk hd smallD smallN below fit input

/-- When the counter bank fits the word range, its index is recovered as a
natural number as well as a word. -/
theorem bucket_key_value {N d w digitBase keyBase : ℕ} (v : Parameters width) (m : Memory width)
    (cost : Fin N → Fin d → ℕ)
    (pd : v 2=(d:Word width)) (pr : v 3=((20*(w+1)+2:ℕ):Word width))
    (pds : v 7=(digitBase:Word width)) (pk : v 8=(keyBase:Word width))
    (hd : 0<d) (smallD : d<2^width) (smallN : N*d<2^width)
    (below : digitBase+N*d≤keyBase) (fit : keyBase+N≤2^width)
    (classes : (20*(w+1)+2)^d ≤ 2^width)
    (input : ∀ (i : Fin N) (j : Fin d),
      m (digitBase+(i.val*d+j.val)) = ((FactorBucket.label w (cost i j)).val:Word width))
    (i : Fin N) :
    (iterRows keyStep v m (N*d) (keyBase+i.val)).val =
      (finFunctionFinEquiv (FactorAllocation.key w cost i)).val := by
  rw [bucket_key_table v m cost pd pr pds pk hd smallD smallN below fit input i,
      Fin.val_cast_of_lt ((finFunctionFinEquiv (FactorAllocation.key w cost i)).isLt.trans_le classes)]

end Hierarchy.FactorBucketRAM

end OAI
