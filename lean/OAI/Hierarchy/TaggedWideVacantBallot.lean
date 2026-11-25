import OAI.Hierarchy.TaggedWideDatedLayout
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Empty ballot at an actual feed date -/
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical
variable {W : ℕ}

/-- The real controller still runs the zero-row field program. Its temporary
registers are discharged and the entire native heap survives this date. -/
theorem Shape.empty_exec (p : Shape) (sites rom work : ℕ) (f : Fields p) (m : Memory W)
    (nc : p.count=0) (nf : p.columns=0)
    (room : work+1<2^W) (addrFit : (p.sheet sites rom work f).address.Fits W (work+1))
    (valFit : (p.sheet sites rom work f).value.Fits W (work+1)) :
    ((p.sheet sites rom work f).code W).Exec m m (p.sheet sites rom work f).ticks := by
  let q:=p.sheet sites rom work f
  have clear (e : Expr) : ProtocolRAM.image (work+1) 0 e m=m := by
    funext a
    simp [ProtocolRAM.image,fillSegment]
  have c : (scan W (work+1) 0 (.lit 0)).Exec m
      (ProtocolRAM.image (work+1) 0 (.lit 0) m) 4 :=
    scan_exec (work+1) 0 (.lit 0) m trivial (by omega)
  rw [clear] at c
  have g : (ProtocolRAMGeneratedWrite.program W (work+1) (work+1) 0 q.address q.value).Exec m
      (ProtocolRAMGeneratedWrite.image (work+1) (work+1) q.address q.value
        (Fin.elim0 : Fin 0→ℕ) (Fin.elim0 : Fin 0→Word W) m)
      (ProtocolRAMGeneratedWrite.work 0 q.address q.value) :=
    ProtocolRAMGeneratedWrite.run (n:=0) (work+1) (work+1) q.address q.value
      Fin.elim0 Fin.elim0 m addrFit valFit (by omega) (by omega)
      (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
      (fun i _ => i.elim0) (fun i _ => i.elim0)
  have empty : ProtocolRAMGeneratedWrite.image (work+1) (work+1) q.address q.value
      (Fin.elim0 : Fin 0→ℕ) (Fin.elim0 : Fin 0→Word W) m=m := by
    simp only [ProtocolRAMGeneratedWrite.image,ProtocolRAMIndexedWrite.image,clear]
  rw [empty] at g
  change (ProtocolRAMTurnReplay.program W q.base q.length q.scratch q.rows q.address q.value).Exec m m
    (ProtocolRAMTurnReplay.work q.length q.rows q.address q.value)
  have len : q.length=0:=by simp [q,Shape.sheet,nf]
  have nr : q.rows=0:=nc
  have scratch : q.scratch=work+1:=by simp [q,Shape.sheet,nf]
  rw [len,nr,scratch]
  change ((scan W (work+1) 0 (.lit 0)).seq
    (ProtocolRAMGeneratedWrite.program W (work+1) (work+1) 0 q.address q.value)).Exec
    m m (4+ProtocolRAMGeneratedWrite.work 0 q.address q.value)
  intro P R K machine pc reg pub exit installed data cfg mem entry same
  exact Procedure.Exec.then c g machine pc reg pub exit installed data cfg mem entry same

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end OAI
