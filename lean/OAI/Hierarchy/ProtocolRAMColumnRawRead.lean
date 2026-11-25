import OAI.Hierarchy.ProtocolRAMStageColumnRead
import OAI.Hierarchy.ProtocolRAMCalendarBoot
import OAI.Hierarchy.ProbeStageRawInput

namespace OAI
/-! # The same calendar boot retains the actual exterior permutation -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets.ColumnROM
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native Calendar
open scoped Classical Fin.CommRing

theorem raw_output {h d : ℕ} (hd : 1≤ d) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h d)
    (auth : ∀p : Fin (2^h), raw p.val=((π p).val:Word _)) :
    Native.Resident (initialOutput h) (images h d (inputTape h d _ raw) (rounds d))
      (fun p : Fin (2^h)=>(π p).val) := by
  intro p
  have word := p.isLt.trans_le ((height_extent h d).trans (extent_word h d Native.copies).le)
  simpa only [Bank.read,initialOutput,Bank.size,Nat.zero_add,Fin.val_cast_of_lt word,Nat.mod_eq_of_lt p.isLt] using
    (images_raw hd π raw auth p).trans (auth p)

theorem boot_raw {h d k jobs : ℕ} (v : Fin jobs→Market h d k) {size : ℕ} (layout : Boot.Layout v size)
    (hd : 1≤ d) (π : Equiv.Perm (Fin (2^h))) (words : Boot.Tape h d)
    (auth : ∀p : Fin (2^h), words p.val=((π p).val:Word _)) :
    Native.Resident (initialOutput h) (Boot.booted v size words) (fun p : Fin (2^h)=>(π p).val) := by
  let raw := Computability.VPVNP.RAMMemory.initialMemory size words
  let data := Boot.controller v raw
  have early : 2^h≤ heapEnd h d Native.copies := by
    have cap := height_extent h d
    have first := phase_in_heap (h:=h) (d:=d) (copies:=Native.copies) (Nat.zero_le (rounds d))
    simp only [phase,Nat.zero_mul,Nat.add_zero] at first
    omega
  have read (p : Fin (2^h)) : data p.val=((π p).val:Word _) := by
    have low := p.isLt.trans_le early
    have miss (j : Fin jobs) : ¬ ProtocolRAMStaticSlabs.Inside (fun t=>Boot.low (v t)) (fun t=>Boot.high (v t)) j p.val :=
      fun hit=>Nat.not_lt_of_ge hit.1 (low.trans_le (layout.afterHeap j))
    change Boot.controller v raw p.val=_
    rw [Boot.controller,ProtocolRAMStaticSlabs.outside _ _ miss]
    simpa only [raw,Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (low.trans_le layout.subdivision)] using auth p
  unfold Boot.booted
  rw [Boot.initial_eq v layout words]
  exact raw_output hd π data read

theorem raw_frame {h w : ℕ} {π : Equiv.Perm (Fin (2^h))} {m m' : Memory w}
    (seen : Native.Resident (initialOutput h) m (fun p : Fin (2^h)=>(π p).val))
    (keep : ∀a<2^h,m' a=m a) : Native.Resident (initialOutput h) m' (fun p : Fin (2^h)=>(π p).val) := by
  intro p
  have original := seen p
  simp only [Bank.read,initialOutput,Bank.size,Nat.zero_add] at original ⊢
  exact (keep _ (Nat.mod_lt (p.val:Word w).val (Nat.two_pow_pos h))).trans original

end Hierarchy.ProtocolRAM.BoughtSockets.ColumnROM
end

end OAI
