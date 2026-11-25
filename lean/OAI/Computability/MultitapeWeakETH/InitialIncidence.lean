import OAI.Computability.MultitapeWeakETH.PackedFormula
import OAI.Computability.VPVNP.CompressorRecordsCursor

/-! # Six numeric incidence columns of the packed formula network -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.InitialIncidence

open VPVNP Compression CompressorRecords PackedSwitches
open private stages from OAI.Computability.MultitapeWeakETH.PackedFormula
open private bitWord_zero bitWord_single from OAI.Computability.VPVNP.CompressorRecordsCursorCoordinates
open scoped Classical
noncomputable section

def axis (d i : ℕ) := if i < d then i else 2*d-1-i

private theorem stages_axis {d : ℕ} (hd : 1 ≤ d) (i : Fin (2*d-2+2)) :
    (stages d hd i).2 = axis d i.val := by
  simp only [stages,NearSquareRoot.Benes.executionOrder,List.getElem_append,List.length_map,List.length_range,axis]
  split
  · simp
  · simp
    omega

def mask (g j port : ℕ) := if port = 1 ∧ j < g then 2^(g-1-j) else 0

private theorem shift_number (g j p : ℕ) :
    (bitWordFinEquiv g (shift g j (decide (p=1)))).val = mask g j p := by
  by_cases h : p=1 ∧ j<g
  · let t : Fin g := ⟨j,h.2⟩
    have eq : shift g j (decide (p=1)) = (fun i : Fin g => if i=t.rev.rev then 1 else 0) := by
      funext i
      simp only [shift,h.1,decide_true,true_and,Fin.rev_rev]
      simp only [Fin.ext_iff,t,eq_comm]
    rw [eq,bitWord_single]
    simp [mask,h,t,Fin.val_rev]
    omega
  · have eq : shift g j (decide (p=1)) = 0 := by
      funext i
      change (if decide (p=1) = true ∧ j=i.val then (1 : ZMod 2) else 0) = 0
      apply ite_eq_right
      rintro ⟨hp,rfl⟩
      exact h ⟨of_decide_eq_true hp,i.isLt⟩
    rw [eq,bitWord_zero,mask,ite_eq_right h]

def nextStage (d i : ℕ) := if i+1=2*d then 0 else i+1
def prevStage (d i : ℕ) := if i=0 then 2*d-1 else i-1

private theorem stage_next {d : ℕ} (hd : 1 ≤ d) (i : Fin (2*d-2+2)) :
    (finRotate _ i).val = nextStage d i.val := by
  rw [coe_finRotate,nextStage]
  have eq : i = Fin.last _ ↔ i.val+1 = 2*d := by rw [Fin.ext_iff,Fin.val_last]; omega
  simp only [eq]

private theorem stage_prev {d : ℕ} (hd : 1 ≤ d) (i : Fin (2*d-2+2)) :
    ((finRotate _).symm i).val = prevStage d i.val := by
  by_cases h : i=0
  · subst i
    rw [show (finRotate (2*d-2+2)).symm 0 = Fin.last _ from
      (finRotate _).symm_apply_eq.mpr finRotate_last.symm]
    simp [prevStage]
    omega
  · rw [coe_finRotate_symm_of_ne_zero h,prevStage,ite_eq_right (by exact fun e => h (Fin.ext e))]

/-- The six columns are indexed by consecutive base slots or actual
slots. Only actual columns decode a lane coordinate from the row number. -/
def column (a g r : ℕ) (c : Fin 6) (row : ℕ) : ℕ :=
  let D := 2^a
  let V := 2^g
  let d := g+(r+2)
  let j := row/D
  let p := row%D
  let i := j/V
  let x := j%V
  let prev := prevStage d i
  ![nextStage d j*D+p,prevStage d j*D+p,mask g (axis d j) p,
    (nextStage d i*V+(x ^^^ mask g (axis d i) p))*D+p,
    (prev*V+(x ^^^ mask g (axis d prev) p))*D+p,
    if p<2 then 2^(r+2) else 0] c

private theorem sub_eq_add {g} (x y : BitWord g) : x-y=x+y := by
  funext i
  change x i-y i=x i+y i
  generalize x i=z
  generalize y i=q
  decide +revert

variable {a g r w : ℕ}
local notation "X" => inputState a g r
local notation "D₀" => g+(r+2)

private theorem idx_div (i : ℕ) {p n : ℕ} (h : p<n) : (i*n+p)/n=i := by
  rw [Nat.mul_comm,Nat.mul_add_div (by omega),Nat.div_eq_of_lt h,Nat.add_zero]

theorem base_columns (i : Fin (2*D₀-2+2)) (p : Fin (2^a)) :
    let row := i.val*2^a+p.val
    column a g r 0 row = ((finRotate _ i).val*2^a+p.val) ∧
    column a g r 1 row = (((finRotate _).symm i).val*2^a+p.val) ∧
    column a g r 2 row = (bitWordFinEquiv g ((X).slots.displacement (i,p))).val := by
  intro row
  have h : row/2^a=i.val ∧ row%2^a=p.val := by
    dsimp [row]; simp [idx_div _ p.isLt,Nat.mod_eq_of_lt p.isLt]
  change _ ∧ _ ∧ _ = (bitWordFinEquiv g (shift g (stages D₀ (by omega) i).2 (decide (p.val=1)))).val
  simp only [column,h.1,h.2,stage_next (d:=D₀) (by omega),stage_prev (d:=D₀) (by omega),stages_axis,shift_number]
  exact ⟨rfl,rfl,rfl⟩

theorem actual_columns (i : Fin (2*D₀-2+2)) (x : BitWord g) (p : Fin (2^a)) :
    let row := (i.val*2^g+(bitWordFinEquiv g x).val)*2^a+p.val
    let out := (X).slots.actualGraph.target ((i,x),p)
    let inn := (X).slots.actualGraph.target.symm ((i,x),p)
    column a g r 3 row = (out.1.1.val*2^g+(bitWordFinEquiv g out.1.2).val)*2^a+out.2.val ∧
    column a g r 4 row = (inn.1.1.val*2^g+(bitWordFinEquiv g inn.1.2).val)*2^a+inn.2.val ∧
    column a g r 5 row = (X).width ((i,p),x) := by
  intro row out inn
  let z := (bitWordFinEquiv g x).val
  have div : row/2^a=i.val*2^g+z := by
    simp [row,z,idx_div _ p.isLt]
  have lane : (i.val*2^g+z)/2^g=i.val ∧ (i.val*2^g+z)%2^g=z := by
    simp [z,idx_div _ (bitWordFinEquiv g x).isLt,
      Nat.mod_eq_of_lt (bitWordFinEquiv g x).isLt]
  have port : row%2^a=p.val := by simp [row,Nat.mod_eq_of_lt p.isLt]
  let step := stages D₀ (by omega)
  change _ = ((finRotate _ i).val*2^g+(bitWordFinEquiv g (x+shift g (step i).2 (decide (p.val=1)))).val)*2^a+p.val ∧
    _ = (((finRotate _).symm i).val*2^g+
      (bitWordFinEquiv g (x-shift g (step ((finRotate _).symm i)).2 (decide (p.val=1)))).val)*2^a+p.val ∧
    _ = if p.val < 2 then 2^(r+2) else 0
  simp only [column,div,port,lane.1,lane.2,sub_eq_add,bitWordFinEquiv_add_val,step,stages_axis,shift_number,
    stage_next (d:=D₀) (by omega),stage_prev (d:=D₀) (by omega)]
  exact ⟨rfl,rfl,rfl⟩

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.InitialIncidence
