import OAI.Hierarchy.ProbeActualGroups
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Public translation of local CT group words to global stage-group ordinals -/

namespace Hierarchy.ProtocolRAM.ReportGroupROM
open ProbeStage Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
noncomputable section
variable {z d w K : ℕ}

def bits (z d : ℕ) := 2*(rounds d+1)+z
def stride (z d : ℕ) := 2^bits z d
def words (z d : ℕ) := (permutationFabric z d).shapes.length*stride z d
def bank (start z d : ℕ) (t : StageAt z d) : Bank := ⟨start+t.val*stride z d,bits z d⟩

theorem stride_eq (z d : ℕ) : stride z d=4^(rounds d+1)*2^z := by
  simp only [stride,bits,pow_add,pow_mul]
  norm_num

theorem size (t : StageAt z d) (hd : 1≤d) : Fintype.card (stageAt z d t).Group ≤ stride z d := by
  let shape := stageAt z d t
  have bounds := template_dyadic hd shape (List.get_mem ..)
  have sockets : 0 < shape.span := (Nat.two_pow_pos _).trans_le bounds.span_lower
  rw [stride_eq]
  exact (Nat.le_mul_of_pos_right _ sockets).trans bounds.2

abbrev Numbering (z d : ℕ) := (t : StageAt z d) → (stageAt z d t).Group ≃ Fin (Fintype.card (stageAt z d t).Group)

private def entry (groups : Fin K ≃ AllGroups z d) (num : Numbering z d) (index group : ℕ) : Word w :=
  if ht : index < (permutationFabric z d).shapes.length then
    let t : StageAt z d:=⟨index,ht⟩
    if hg : group < Fintype.card (stageAt z d t).Group then
      ((groups.symm ⟨t,(num t).symm ⟨group,hg⟩⟩).val:Word w) else 0
  else 0

def load (start : ℕ) (groups : Fin K ≃ AllGroups z d) (num : Numbering z d) (m : Memory w) : Memory w :=
  fillSegment start (words z d) (fun a=>entry groups num ((a-start)/stride z d) ((a-start)%stride z d)) m

def Resident (start : ℕ) (groups : Fin K ≃ AllGroups z d) (num : Numbering z d) (m : Memory w) : Prop :=
  ∀ (t : StageAt z d) (g : (stageAt z d t).Group),
    (bank start z d t).read m ((num t g).val:Word w)=((groups.symm ⟨t,g⟩).val:Word w)

theorem address (start : ℕ) (t : StageAt z d) (r : Word w) :
    start≤(bank start z d t).base+r.val%(bank start z d t).size ∧
    (bank start z d t).base+r.val%(bank start z d t).size < start+words z d := by
  have upper := Nat.mul_le_mul_right (stride z d) t.isLt
  rw [Nat.succ_mul] at upper
  have rem := Nat.mod_lt r.val (Nat.two_pow_pos (bits z d))
  change r.val%stride z d < stride z d at rem
  change start ≤ start+t.val*stride z d+r.val%stride z d ∧ start+t.val*stride z d+r.val%stride z d < start+((permutationFabric z d).shapes.length*stride z d)
  omega

theorem of_frame {start : ℕ} {groups : Fin K ≃ AllGroups z d} {num : Numbering z d} {m m' : Memory w}
    (resident : Resident start groups num m)
    (same : ∀ a,start≤a → a < start+words z d → m' a=m a) : Resident start groups num m' := by
  intro t g
  have span := address start t ((num t g).val:Word w)
  exact (same _ span.1 span.2).trans (resident t g)

theorem resident (start : ℕ) (groups : Fin K ≃ AllGroups z d) (num : Numbering z d) (m : Memory w)
    (hd : 1≤d) (fit : stride z d≤2^w) : Resident start groups num (load start groups num m) := by
  intro t g
  let i := (num t g).val
  have digit : i<Fintype.card (stageAt z d t).Group := (num t g).isLt
  have small : i < stride z d := digit.trans_le (size t hd)
  have quo : (t.val*stride z d+i)/stride z d=t.val := by
    rw [Nat.mul_comm t.val,Nat.mul_add_div (m:=stride z d) (show 0 < stride z d from Nat.two_pow_pos _) t.val i,Nat.div_eq_of_lt small,Nat.add_zero]
  have rem : (t.val*stride z d+i)%stride z d=i := Nat.mul_add_mod_of_lt small
  have edge := Nat.mul_le_mul_right (stride z d) t.isLt
  rw [Nat.succ_mul] at edge
  have interval : start ≤ start+t.val*stride z d+i ∧ start+t.val*stride z d+i < start+words z d := by
    unfold words;omega
  change load start groups num m (start+t.val*stride z d+(i:Word w).val%stride z d)=_
  rw [Fin.val_cast_of_lt (small.trans_le fit),Nat.mod_eq_of_lt small]
  have unbase : start+t.val*stride z d+i-start=t.val*stride z d+i := by omega
  rw [load,fillSegment,ite_eq_left interval,unbase,quo,rem]
  have slot : entry (w:=w) groups num t.val (num t g).val=((groups.symm ⟨t,g⟩).val:Word w) := by
    simp only [entry,dite_eq_left t.isLt,Fin.eta,dite_eq_left (num t g).isLt,Equiv.symm_apply_apply]
  exact slot

theorem frame (start : ℕ) (groups : Fin K ≃ AllGroups z d) (num : Numbering z d) (m : Memory w)
    (a : ℕ) (outside : a < start ∨ start+words z d≤a) : load start groups num m a=m a := by
  simp [load,fillSegment,show ¬(start≤a ∧ a < start+words z d) by omega]

end
end Hierarchy.ProtocolRAM.ReportGroupROM

end OAI
