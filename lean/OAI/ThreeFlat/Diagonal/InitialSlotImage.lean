import OAI.ThreeFlat.Diagonal.CompressorWordEncoding
import OAI.ThreeFlat.Diagonal.SlotImage

namespace OAI
/-! # Six physical fields of the cyclic straight/flip cursor -/
namespace ThreeFlat.Diagonal.InitialSlotImage
open LaneCursor CompressorPacking.Native

def next (axes v : ℕ) := if v+1 < axes then v+1 else 0
def prev (axes v : ℕ) := if v=0 then axes-1 else v-1

def field (axes v slot : ℕ) (back : Bool) : Fin 3 → ℕ :=
  let before := prev axes v
  ![if back then before else next axes v,slot,(slot%2)*2^(if back then before else v)]

theorem next_rotate {k : ℕ} (b : Fin (k+1)) : (finRotate _ b).val = next (k+1) b.val := by
  by_cases eq : b = Fin.last k
  · subst b
    simp [next]
  · have h : b.val < k := by
      have := b.isLt
      have ne : b.val ≠ k := fun h => eq (Fin.ext h)
      omega
    rw [coe_finRotate_of_ne_last eq]
    unfold next
    rw [ite_eq_left (show b.val+1<k+1 by omega)]

theorem prev_rotate {k : ℕ} (b : Fin (k+1)) : ((finRotate _).symm b).val = prev (k+1) b.val := by
  by_cases eq : b = 0
  · subst b
    have h : (finRotate (k+1)).symm 0 = Fin.last k := (Equiv.symm_apply_eq _).mpr (finRotate_last (n:=k)).symm
    simp [h,prev]
  · simpa [prev,Fin.val_ne_zero_iff.mpr eq] using coe_finRotate_symm_of_ne_zero eq

theorem axis_number {k : ℕ} (i : Fin k) (b : Fin 2) : (tagOrdinal k (axis i b)).val = b.val*2^i.val := by
  have h : axis i b = Pi.single i b := by
    funext j
    by_cases hj : j=i
    · subst j
      simp [axis]
    · simp [axis,hj]
  rw [h]
  exact finFunctionFinEquiv_single i b

theorem fields {k r : ℕ} (hk : 2 ≤ k+1) (p : Fin (k+1) × Fin (r*2)) (back : Bool) :
    SlotImage.fields (graph hk r) (Equiv.refl _) (tagOrdinal _) p back = field (k+1) p.1 p.2 back := by
  have forward : (p.1+1).val=next (k+1) p.1.val := by
    simpa only [finRotate_apply] using next_rotate p.1
  have backward : (p.1-1).val=prev (k+1) p.1.val := by
    simpa only [finRotate_symm_apply] using prev_rotate p.1
  let choice : Fin 2:=⟨p.2.val%2,Nat.mod_lt _ (by decide)⟩
  have digit (i : Fin (k+1)) : ((tagOrdinal (k+1)) (axis i choice)).val=p.2.val%2*2^i.val :=
    axis_number i choice
  funext f
  cases back <;> fin_cases f <;>
    simp [SlotImage.fields,SlotImage.oriented,SlotImage.shift,graph,field,finProdFinEquiv,Fin.modNat] <;>
    first | exact forward | exact backward | exact digit _ | exact (digit _).trans (by rw [backward])

/-- Word at an offset in the six equal graph columns. -/
def row (axes degree i : ℕ) : ℕ :=
  let rows := axes*degree
  let col := i/rows
  let v := i%rows/degree
  let slot := i%rows%degree
  let old := prev axes v
  let dst := if col<3 then next axes v else old
  let disp := (slot%2)*2^(if col<3 then v else old)
  if col%3=0 then dst else if col%3=1 then slot else disp

theorem row_cell {axes degree : ℕ} (E : SlotImage.Columns) (h : E.rows=axes*degree)
    (p : Fin axes × Fin degree) (back : Bool) (f : Fin 3) :
    row axes degree (SlotImage.cell E (Equiv.refl _) p back f - E.graph) =
      field axes p.1 p.2 back f := by
  let n := axes*degree
  let s := p.1.val*degree+p.2.val
  have hg : 0<degree := (Nat.zero_le _).trans_lt p.2.isLt
  have small : s<n := by
    dsimp [s,n]
    exact (Nat.add_lt_add_left p.2.isLt _).trans_le (by simpa [Nat.succ_mul] using Nat.mul_le_mul_right degree p.1.isLt)
  have hp : 0<n := Nat.zero_le s |>.trans_lt small
  have hval : s / degree = p.1.val := by
    dsimp [s]
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hg,Nat.div_eq_of_lt p.2.isLt,Nat.zero_add]
  have rmod : s%degree=p.2.val := by simp [s,Nat.add_mod,Nat.mod_eq_of_lt p.2.isLt]
  change row axes degree (E.graph+E.rows*SlotImage.column back f+s-E.graph) = _
  rw [h]
  simp only [Nat.add_assoc,Nat.add_sub_cancel_left]
  change row axes degree (n*SlotImage.column back f+s) = _
  have divE (k : ℕ) : (n*k+s)/n=k := by
    rw [Nat.mul_comm n k,Nat.add_comm,Nat.add_mul_div_right _ _ hp,Nat.div_eq_of_lt small,Nat.zero_add]
  have modE (k : ℕ) : (n*k+s)%n=s := by simp [Nat.add_mod,Nat.mod_eq_of_lt small]
  unfold row
  dsimp only
  have rows : axes*degree=n:=rfl
  simp only [rows,divE,modE,rmod,hval]
  cases back <;> fin_cases f <;> rfl

end ThreeFlat.Diagonal.InitialSlotImage

end OAI
