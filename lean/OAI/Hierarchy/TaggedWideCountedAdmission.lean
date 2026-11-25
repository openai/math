import OAI.Hierarchy.ProtocolRAMCalendarCompactRun
import OAI.Hierarchy.TaggedWideControlProcedure

namespace OAI
/-! # Authenticated admission through the counted subdivision and original checker -/
noncomputable section
namespace Hierarchy.Tagged.WideControlJoin
open ThreeFlat Routing Diagonal TraceRows TraceBanks
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
open AdaptiveProbe ProtocolRAM ProtocolRAM.Calendar ProbeStage ProbeStage.Native
open TaggedShorterControlHistory
open scoped Classical BigOperators Fin.CommRing



variable {F : Type*} [Field F] {z d k jobs q goods S clock m : ℕ}
local notation "W" => wordBits z d copies

theorem compact_gate_run (C : Chart W q goods) (markets : Fin jobs→Market z d k) (flag : ℕ)
    (layout : Boot.Layout markets S) (hd : 1≤d) (π : Equiv.Perm (Fin (2^z)))
    (words : Boot.Tape z d) (auth : ∀i : Fin (2^z),words i.val=((π i).val:Word W))
    (ready : mounted C (events C.mesh) (Boot.booted markets S words)) (order : ProtocolRAM.Calendar.separated C (events C.mesh))
    (fit : (historyFlag C (events C.mesh)).Fits W flag) (room : flag+1<2^W)
    (st : Word W) (ww : 3≤W+1) (labels : (Boot.compactProgram C flag).labels+3≤2^(W+1))
    (hs : S≤2^W) (timed : clock+1≤2^(W+1)) (size : S+(clock+1)≤2^m) (record : W+1≤4*m)
    (fuel : Native.Compact.constant d*2^z+checkedCost C+2<clock) :
    let A := Gate.ofProcedure (Boot.compactProgram C flag) (flag:Word W) st (fun _ : Fin 1=>(flag:Word W))
      m ww labels hs timed
    A.Ran (Boot.header markets S words) (checkedOut C flag (Boot.booted markets S words)) ∧
    A.observed (Boot.header markets S words) (A.zeroFlag (F:=F) (0 : Fin 1)) =
      if admissible C (events C.mesh) (Boot.booted markets S words) then 1 else 0 := by
  intro A
  let out:=checkedOut C flag (Boot.booted markets S words)
  have exec : (Boot.compactProgram C flag).Exec (Boot.initial markets S words) out
      (Native.Compact.constant d*2^z+checkedCost C) :=
    Boot.compact_checked C flag markets layout hd π words auth ready fit room
  have ran : A.Ran (Boot.header markets S words) out :=
    Gate.ofProcedure_run (Boot.compactProgram C flag) (flag:Word W) st _ m ww labels hs timed
      (Boot.header markets S words) out _ fuel exec
  refine ⟨ran,?_⟩
  rw [prefix_run A (Boot.header markets S words) (0 : Fin 1) out ran size record]
  change (if (out ((flag:Word W).val)).val=0 then (1:F) else 0)=_
  rw [Fin.val_cast_of_lt (by omega : flag<2^W)]
  have observed : (out flag).val=0 ↔ admissible C (events C.mesh) (Boot.booted markets S words) := by
    rw [←checked_read C flag _ ready order (by omega : 0<W)]
    exact ⟨fun h=>Fin.ext h,fun h=>congrArg Fin.val h⟩
  exact if_congr observed rfl rfl

end Hierarchy.Tagged.WideControlJoin

end
end OAI
