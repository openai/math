import OAI.Hierarchy.ProbeStageAddress
import OAI.Hierarchy.ProbeStageRowLayout

namespace OAI
/-! # One fixed geometry tape shared by all input permutations -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

abbrev GeometryCell (h d : ℕ) := Fin (rounds d) × Fin 8 × Fin (extent h d)

def GeometryCell.address {h d : ℕ} (copies : ℕ) (x : GeometryCell h d) :=
  bankBase h d copies x.1.val (3+x.2.1.val)+x.2.2.val

private theorem word_components {e k : ℕ} (size : 0<e) (i : Fin e) :
    ((k*e+i.val)/e, (k*e+i.val)%e) = (k,i.val) := by
  rw [Nat.mul_comm k e,Nat.mul_add_div size,Nat.div_eq_of_lt i.isLt,Nat.add_zero,Nat.add_mod]
  simp [Nat.mod_eq_of_lt i.isLt]

theorem GeometryCell.injective {h d : ℕ} (copies : ℕ) :
    Function.Injective (address (h:=h) (d:=d) copies) := by
  rintro ⟨j,c,i⟩ ⟨k,b,o⟩ eq
  have ep : 0<extent h d := pow_pos (by decide) _
  have sp : 0<stride d copies := by unfold stride;omega
  have small (a : Fin 8) : 3+a.val<stride d copies := by unfold stride;omega
  have addr (j : Fin (rounds d)) (c : Fin 8) (i : Fin (extent h d)) :
      address copies (j,c,i) = (3+j.val*stride d copies+(3+c.val))*extent h d+i.val := by
    unfold address bankBase phase
    ring
  rw [addr,addr] at eq
  have read := congrArg (fun a => (a/extent h d,a%extent h d)) eq
  simp only [word_components ep] at read
  obtain ⟨slots,off⟩ := Prod.mk.inj read
  have sc : j.val*stride d copies+(3+c.val)=k.val*stride d copies+(3+b.val) := by omega
  have eq' := congrArg (fun a => (a/stride d copies,a%stride d copies)) sc
  have components (j : Fin (rounds d)) (c : Fin 8) :
      ((j.val*stride d copies+(3+c.val))/stride d copies,
       (j.val*stride d copies+(3+c.val))%stride d copies) = (j.val,3+c.val) :=
    word_components sp (k:=j.val) ⟨3+c.val,small c⟩
  rw [components,components] at eq'
  obtain ⟨jv,cv⟩ := Prod.mk.inj eq'
  have je := Fin.ext jv
  have ce : c=b := Fin.ext (by omega)
  have ie := Fin.ext off
  simp [je,ce,ie]

/-- Six fixed arithmetic tables, followed by the two endpoint residue
tables consumed by the color chooser. -/
def GeometryCell.value {h d : ℕ} (x : GeometryCell h d) : ℕ :=
  let B := radix h d
  let m := 2^widthLog h d x.1.val
  let pos := radix_pos h d
  if c : x.2.1.val<6 then tableWords (B^x.1.val) m B pos ⟨x.2.1.val,c⟩ x.2.2.val
  else if inside : x.2.2.val < m then
    let residue := (decode m B pos ⟨x.2.2.val,inside⟩).2.val % (B^2)
    if x.2.1.val=6 then residue else B^2*residue
  else 0

/-- Install every geometry table once in its disjoint banks before the
first subdivision record. The other private input words are preserved. -/
noncomputable def geometryTape (h d copies w : ℕ) (m : Memory w) : Memory w :=
  Function.extend (GeometryCell.address (h:=h) (d:=d) copies)
    (fun x => (GeometryCell.value x : Word w)) m

theorem geometryTape_cell {h d copies w : ℕ} (m : Memory w) (x : GeometryCell h d) :
    geometryTape h d copies w m (x.address copies) = (x.value : Word w) :=
  (GeometryCell.injective copies).extend_apply _ _ _

theorem geometryTape_away {h d copies w a : ℕ} (m : Memory w)
    (outside : ¬∃ x : GeometryCell h d, x.address copies=a) :
    geometryTape h d copies w m a = m a :=
  Function.extend_apply' _ _ _ outside

theorem geometryTape_prefix {h d copies w a : ℕ} (m : Memory w) (low : a<3*extent h d) :
    geometryTape h d copies w m a=m a := by
  apply geometryTape_away
  rintro ⟨x,rfl⟩
  have rel : 3*extent h d ≤ phase h d copies x.1.val := by
    apply Nat.mul_le_mul_right
    omega
  unfold GeometryCell.address bankBase at low
  omega

theorem geometry_words (h d : ℕ) :
    Fintype.card (GeometryCell h d) = (rounds d*8*4^(rounds d+1))*2^h := by
  simp [GeometryCell,extent,room_slots]
  ring

end Hierarchy.ProbeStage.Native

end OAI
