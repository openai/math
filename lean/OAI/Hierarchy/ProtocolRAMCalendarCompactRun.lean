import OAI.Hierarchy.ProtocolRAMCalendarBoot
import OAI.Hierarchy.ProbeStageCompactRun

namespace OAI
/-! # A single counted subdivision over the finite mounted calendar tape -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.Boot
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical

theorem compact_start {h d k jobs size : ℕ} (v : Fin jobs→Market h d k) (L : Layout v size)
    (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (words : Tape h d)
    (authentic : ∀i : Fin (2^h),words i.val=((π i).val:Word _)) :
    (Native.Compact.subdivision h d).Exec (initial v size words) (booted v size words)
      (Native.Compact.constant d*2^h) := by
  let raw : Tape h d := Computability.VPVNP.RAMMemory.initialMemory size words
  let data:=controller v raw
  have rows (i : Fin (2^h)) : data i.val=((π i).val:Word _) := by
    have early:=i.isLt.trans_le (root_extent (z:=h) (d:=d))
    have miss (j : Fin jobs) : ¬ProtocolRAMStaticSlabs.Inside (fun t=>low (v t)) (fun t=>high (v t)) j i.val :=
      fun hit=>(not_le_of_gt (early.trans_le (L.afterHeap j))) hit.1
    change controller v raw i.val=_
    rw [controller,ProtocolRAMStaticSlabs.outside _ _ miss]
    simpa only [raw,Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (early.trans_le L.subdivision)] using authentic i
  have first : initial v size words=inputTape h d (wordBits h d copies) data:=initial_eq v L words
  rw [booted,first]
  intro programs registers slots machine
  exact Native.Compact.linear_run hd π data rows machine

abbrev compactProgram {h d q goods : ℕ} (C : Chart (wordBits h d copies) q goods) (flag : ℕ) :=
  (Native.Compact.subdivision h d).seq (checked C flag)

theorem compact_checked {h d k jobs size q goods : ℕ} (C : Chart (wordBits h d copies) q goods) (flag : ℕ)
    (v : Fin jobs→Market h d k) (L : Layout v size) (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (words : Tape h d)
    (auth : ∀i : Fin (2^h),words i.val=((π i).val:Word _)) (ready : mounted C (events C.mesh) (booted v size words))
    (fits : (historyFlag C (events C.mesh)).Fits (wordBits h d copies) flag) (word : flag+1<2^wordBits h d copies) :
    (compactProgram C flag).Exec (initial v size words) (checkedOut C flag (booted v size words))
      (Native.Compact.constant d*2^h+checkedCost C) :=
  Procedure.Exec.then (compact_start v L hd π words auth) (checked_exec C flag _ ready fits word)

end Hierarchy.ProtocolRAM.Calendar.Boot
end

end OAI
