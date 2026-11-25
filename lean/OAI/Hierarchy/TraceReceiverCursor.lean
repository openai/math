import OAI.ThreeFlat.RAM.PhysicalInputPhases

namespace OAI
/-! # Starting the gather at the genuine command interval of the selected tick -/
namespace Hierarchy.TraceFactorReceiver.Cursor
open ThreeFlat RAM Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure
open RAM.DescriptorExpr RAM.DescriptorScan
open scoped Fin.CommRing

def term (W cursor commands count : ℕ) : Term W 0 1 :=
  .select .eq (.result 0) (.literal cursor) (.literal commands)
    (.binary .add (.literal commands) (.binary .mul (.literal 7) (.load (.literal count))))

def program (W cursor commands count : ℕ) : Procedure W :=
  PhysicalInputPhases.writing (term W cursor commands count) Fin.elim0 cursor 2

private theorem binds (W cursor commands count : ℕ) :
    (term W cursor commands count).binds=9 := by
  simp [term,Term.select,Term.binary,Term.load,Term.literal,Term.binds]

theorem hardware (W cursor commands count : ℕ) :
    let p:=program W cursor commands count
    p.labels+p.registers+p.slots≤100 := by
  simp [program,PhysicalInputPhases.writing,Term.labels_eq,binds]

theorem cost (W cursor commands count : ℕ) :
    4+2*(2*(term W cursor commands count).binds+4)≤100 := by
  rw [binds]
  decide

def image {W : ℕ} (cursor commands roots : ℕ) (m : Memory W) :=
  fillSegment cursor 2 (fun j=>if j=cursor then (commands:Word W) else ((commands+7*roots:ℕ):Word W)) m

theorem run {W : ℕ} (cursor commands count roots : ℕ) (m : Memory W)
    (word : m count=(roots:Word W)) (room : cursor+2<2^W) (countRoom : count<2^W)
    (sep : count<cursor ∨ cursor+2≤count) :
    (program W cursor commands count).Spec (·=m) (fun _ out=>out=image cursor commands roots m)
      (4+2*(2*(term W cursor commands count).binds+4)) := by
  let digits (j : ℕ) : Word W:=if j=cursor then commands else ((commands+7*roots:ℕ):Word W)
  intro P R K M pc reg pub exit rom data c init start eq
  subst init
  apply PhysicalInputPhases.writing_spec (term W cursor commands count) Fin.elim0 cursor 2 room
    (·=m) digits (by
      rintro _ rfl a temp lo hi frame
      have ptr : ((cursor:Word W)).val=cursor:=Fin.val_cast_of_lt (by omega)
      have read:=frame count sep
      have iff : a=(cursor:Word W) ↔ a.val=cursor := by rw [←Fin.val_inj,ptr]
      simp only [term,Term.eval_select,Term.eval_binary,Term.eval_literal,Term.eval_load,Term.eval,
        Comparison.test,beq_iff_eq,BinaryOp.eval,Fin.val_cast_of_lt countRoom,read,word,digits]
      by_cases h : a.val=cursor
      · simp [iff,h]
      · simp [iff,h,Nat.cast_add,Nat.cast_mul]) M pc reg pub exit rom data c m start rfl

theorem words {W : ℕ} (cursor commands roots : ℕ) (m : Memory W) :
    image cursor commands roots m cursor=(commands:Word W) ∧
    image cursor commands roots m (cursor+1)=((commands+7*roots:ℕ):Word W) ∧
    ∀ z,z<cursor ∨ cursor+2≤z → image cursor commands roots m z=m z := by
  refine ⟨by simp [image,fillSegment],by simp [image,fillSegment],?_⟩
  intro z hz
  simp [image,fillSegment,show ¬(cursor≤z ∧ z<cursor+2) by omega]

end Hierarchy.TraceFactorReceiver.Cursor

end OAI
