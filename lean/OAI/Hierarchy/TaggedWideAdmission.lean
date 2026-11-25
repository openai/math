import OAI.Hierarchy.TaggedWideObserved
import OAI.Hierarchy.ProtocolRAMCalendarBoot

namespace OAI
/-! # Rejecting malformed raw selector words before using any paid terminal readout -/

noncomputable section
namespace Hierarchy.TaggedShorterControlHistory
open ThreeFlat Routing Diagonal TraceRows TraceBanks
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
open AdaptiveProbe ProtocolRAM ProtocolRAM.Calendar ProbeStage ProbeStage.Native
open scoped Classical BigOperators Fin.CommRing
variable {F : Type*} [CommRing F] {z d k jobs q goods S clock m : ℕ}
local notation "W" => wordBits z d copies

/-- On every binary word of the proper format, the prefixValue machine runs
through all local checks using the actual starting tape. This control cut
does not require a funded settlement or a priced geometry on rejected
inputs. Its output can be multiplied by any other physical host factor. -/
theorem observed_admission (C : Chart W q goods) (markets : Fin jobs→Market z d k) (flag : ℕ)
    (layout : Boot.Layout markets S) (hd : 1≤d) (π : Equiv.Perm (Fin (2^z)))
    (words : Boot.Tape z d) (auth : ∀i : Fin (2^z),words i.val=((π i).val:Word W))
    (ready : mounted C (events C.mesh) (Boot.booted markets S words)) (order : separated C (events C.mesh))
    (fit : (historyFlag C (events C.mesh)).Fits W flag) (room : flag+1<2^W)
    (st : Word W) (ww : 3≤W+1) (labels : (Boot.program C flag).labels+3≤2^(W+1))
    (hs : S≤2^W) (timed : clock+1≤2^(W+1)) (size : S+(clock+1)≤2^m) (record : W+1≤4*m)
    (fuel : subdivisionConstant d*2^z+checkedCost C+2<clock) :
    observationSum (F:=F) (m:=m) 28 (machine (Boot.program C flag) (flag:Word W)) ww labels st
      (fun _ : Fin 1=>(flag:Word W)) (Boot.header markets S words) hs timed
      (fun seen=>if (seen 0).val=0 then 1 else 0) =
      if admissible C (events C.mesh) (Boot.booted markets S words) then 1 else 0 := by
  let out := checkedOut C flag (Boot.booted markets S words)
  have execution : (Boot.program C flag).Exec (Boot.initial markets S words) out
      (subdivisionConstant d*2^z+checkedCost C) :=
    Boot.checked_from_header C flag markets layout hd π words auth ready fit room
  obtain ⟨t,ht,done,ran,halt⟩ := machine_run _ (flag:Word W) st _ out _ execution
  have test := checked_read C flag _ ready order (by omega : 0<W)
  exact observed_accepting _ ww labels st _ _ hs timed size (by decide : 0<28) (record_fits_width record)
    done out _ (ht.trans_lt fuel) ran halt (0:Fin 1) flag (Fin.val_cast_of_lt (by omega : flag<2^W))
    _ test (fun _=>1)

/-- Only the accepted chronological branch needs a semantic identification
of the payload circuit. This also covers arbitrary polynomial coefficients
of the unused suffix and invalid parent tag words. -/
theorem retained_factor (auth admitted : Prop) (prefixValue payload value : F)
    (accept : auth → prefixValue=if admitted then 1 else 0)
    (realized : auth → admitted → payload=value) :
    (if auth then 1 else 0)*prefixValue*payload=if auth ∧ admitted then value else 0 := by
  by_cases ha:auth
  · by_cases ok:admitted
    · simp [ha,ok,accept ha,realized ha ok]
    · simp [ha,ok,accept ha]
  · simp [ha]

end Hierarchy.TaggedShorterControlHistory

end
end OAI
