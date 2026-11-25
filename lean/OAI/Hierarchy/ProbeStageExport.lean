import OAI.Hierarchy.ProbeStageWorkBanks
import OAI.Hierarchy.ProbeStageRecordSpace

namespace OAI
/-! # Public addresses of the three fields of every physical tile -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM

/-- The consumer uses three permanent arrays per movement stage. The
middle matching is read directly from the deepest inner columns. -/
def stageBank (h d : ℕ) (stage : Fin (2*rounds d+1)) (field : Fin 3) : Bank :=
  if stage.val<rounds d then
    outputBank (output h d copies stage.val) h ⟨field.val,by omega⟩
  else if stage.val=rounds d then
    parentAt h d copies (rounds d) field
  else
    outputBank (output h d copies (2*rounds d-stage.val)) h ⟨6+field.val,by omega⟩

theorem stageBank_enter {h d : ℕ} (j : Fin (rounds d)) (field : Fin 3) :
    stageBank h d ⟨j.val,by omega⟩ field =
      outputBank (output h d copies j.val) h ⟨field.val,by omega⟩ := by
  simp [stageBank,j.isLt]

theorem stageBank_center (h d : ℕ) (field : Fin 3) :
    stageBank h d ⟨rounds d,by omega⟩ field=parentAt h d copies (rounds d) field := by
  simp [stageBank]

theorem stageBank_exit {h d : ℕ} (j : Fin (rounds d)) (field : Fin 3) :
    stageBank h d ⟨2*rounds d-j.val,by omega⟩ field =
      outputBank (output h d copies j.val) h ⟨6+field.val,by omega⟩ := by
  have low := j.isLt
  have gt : rounds d<2*rounds d-j.val := by omega
  simp [stageBank,not_lt.mpr gt.le,gt.ne',show 2*rounds d-(2*rounds d-j.val)=j.val by omega]

/-- Every output array uses the original record-index bit width. -/
theorem stageBank_bits (h d : ℕ) (stage : Fin (2*rounds d+1)) (field : Fin 3) :
    (stageBank h d stage field).bits=h := by
  unfold stageBank
  split
  · rfl
  split
  · cases e : rounds d <;> fin_cases field <;> rfl
  · rfl

/-- The caller may begin its durable private data at the first word after
the subdivision heap. All three exported columns fit below that address. -/
theorem stageBank_end (h d : ℕ) (s : Fin (2*rounds d+1)) (c : Fin 3) :
    (stageBank h d s c).base+(stageBank h d s c).size≤heapEnd h d copies := by
  have bound (j : Fin (rounds d)) (k : Fin 9) :
      (outputBank (output h d copies j.val) h k).base+(outputBank (output h d copies j.val) h k).size≤
        heapEnd h d copies := by
    have count := Nat.mul_le_mul_right (2^h) (show k.val+1≤9 from k.isLt)
    rw [Nat.succ_mul] at count
    change output h d copies j.val+k.val*2^h+2^h≤_
    calc
      _ ≤ output h d copies j.val+9*2^h := by rw [Nat.add_assoc];exact Nat.add_le_add_left count _
      _ ≤ _ := (output_end h d copies j.val).trans (phase_in_heap j.isLt)
  by_cases left : s.val<rounds d
  · rw [stageBank,ite_eq_left left]
    exact bound ⟨s.val,left⟩ _
  by_cases center : s.val=rounds d
  · rw [stageBank,ite_eq_right left,ite_eq_left center]
    exact parent_end h d copies (rounds d) c
  · rw [stageBank,ite_eq_right left,ite_eq_right center]
    exact bound ⟨2*rounds d-s.val,by omega⟩ _

end Hierarchy.ProbeStage.Native

end OAI
