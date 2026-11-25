import OAI.Hierarchy.ProtocolRAMCalendarBootStart
import OAI.Hierarchy.ProbeStageCheap
import OAI.Hierarchy.ProtocolRAMCatalystArchiveReturn

namespace OAI
/-! # Booting the chronological reserve controller and returning its physical flag -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical

variable {z d k jobs size : ℕ}
local notation "W" => wordBits z d copies

/-- The middle procedure contains the actual catalogue and route directory
promotion. Both it and the final reporter run on their predecessor's output. -/
def bootProgram (z d : ℕ) (promotion tail : Procedure (wordBits z d copies)) :=
  ((subdivisionProgram z d).seq promotion).seq tail

theorem boot_terminal (v : Fin jobs→Market z d k) (layout : Boot.Layout v size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (auth : ∀i : Fin (2^z),words i.val=((π i).val:Word W)) (promotion tail : Procedure W)
    (origin out : Memory W) (prep finish : ℕ)
    (began : promotion.Exec (Boot.booted v size words) origin prep) (ran : tail.Exec origin out finish) :
    (bootProgram z d promotion tail).Exec (Computability.VPVNP.RAMMemory.initialMemory size (Boot.header v size words))
      out (subdivisionConstant d*2^z+prep+finish) :=
  Procedure.Exec.then (b:=origin)
    (Procedure.Exec.then (b:=Boot.booted v size words) (Boot.start v layout hd π words auth).1 began) ran

theorem boot_cheap (promotion tail : Procedure W) (prep : CheapCode promotion) (last : CheapCode tail) :
    CheapCode (bootProgram z d promotion tail) :=
  @cheap_seq W ((subdivisionProgram z d).seq promotion) tail
    (@cheap_seq W (subdivisionProgram z d) promotion (@subdivision_cheap z d) @prep) @last

theorem boot_cpu_cheap (promotion tail : Procedure W) (flag : ℕ)
    (prep : CheapCode promotion) (last : CheapCode tail) :
    ∀i,TaggedShorterCheapCPU.Cheap ((machine (bootProgram z d promotion tail) (flag:Word W)).code i) :=
  machine_cheap _ _ (boot_cheap promotion tail prep last)

theorem boot_machine (v : Fin jobs→Market z d k) (layout : Boot.Layout v size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (auth : ∀i : Fin (2^z),words i.val=((π i).val:Word W)) (promotion tail : Procedure W)
    (origin out : Memory W) (prep finish flag : ℕ) (state : Word W) (fit : flag<2^W)
    (began : promotion.Exec (Boot.booted v size words) origin prep) (ran : tail.Exec origin out finish) :
    let cpu:=machine (bootProgram z d promotion tail) (flag:Word W)
    ∃ t≤ subdivisionConstant d*2^z+prep+finish+2,∃ done,
      advance cpu.program t (cpu.program.start state) (Computability.VPVNP.RAMMemory.initialMemory size (Boot.header v size words))
        =some (done,out) ∧ cpu.program.step done=.finish (some (out flag)) := by
  dsimp only
  obtain ⟨t,ht,done,h,halt⟩:=machine_run _ (flag:Word W) state _ out _
    (boot_terminal v layout hd π words auth promotion tail origin out prep finish began ran)
  exact ⟨t,ht,done,h,by simpa only [Fin.val_cast_of_lt fit] using halt⟩

/-- When the route directory is installed by the terminal itself, the machine
moves directly from the subdivision to that terminal. -/
theorem boot_machine_direct (v : Fin jobs→Market z d k) (layout : Boot.Layout v size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (auth : ∀i : Fin (2^z),words i.val=((π i).val:Word W)) (tail : Procedure W) (out : Memory W)
    (finish flag : ℕ) (state : Word W) (fit : flag<2^W) (ran : tail.Exec (Boot.booted v size words) out finish) :
    let cpu:=machine ((subdivisionProgram z d).seq tail) (flag:Word W)
    ∃t≤ subdivisionConstant d*2^z+finish+2,∃done,
      advance cpu.program t (cpu.program.start state) (Computability.VPVNP.RAMMemory.initialMemory size (Boot.header v size words))
        =some (done,out) ∧ cpu.program.step done=.finish (some (out flag)) := by
  dsimp only
  have exec : ((subdivisionProgram z d).seq tail).Exec (Boot.initial v size words) out
      (subdivisionConstant d*2^z+finish) :=
    Procedure.Exec.then (b:=Boot.booted v size words) (Boot.start v layout hd π words auth).1 ran
  obtain ⟨t,ht,done,run,halt⟩:=machine_run _ (flag:Word W) state _ out _ exec
  exact ⟨t,ht,done,run,by simpa only [Fin.val_cast_of_lt fit] using halt⟩

section Run
variable {q goods r edges count payload : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {core : I→List (Fin edges)} {center : J→List (Fin edges)}

omit [Fintype I] [Fintype J] in
/-- Complete finite-header machine run, including the genuine two route-index
passes, native commitment, reporter and actual external flag load. -/
theorem terminal_machine (v : Fin jobs→Market z d k) (layout : Boot.Layout v size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (auth : ∀i : Fin (2^z),words i.val=((π i).val:Word W))
    (promotion : Procedure W) (origin : Memory W) (prep : ℕ)
    (began : promotion.Exec (Boot.booted v size words) origin prep)
    (C : Chart W q goods) (L : OwnerLedger) (routes : List Pass) (flag : ℕ) (s : Sink r edges)
    (src : ℕ) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (issued : Attempt→Entry count payload)
    (pos : 0<count) (routeFits : ∀p∈routes,p.Fits W) (enum : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→Fin count) (state : Word W)
    (active : mounted C (events C.mesh) origin) (order : separated C (events C.mesh))
    (flagFit : (historyFlag C (events C.mesh)).Fits W flag) (flagEnd : flag+1<2^W)
    (width : s.banks.width.base+edges<2^W) (rows : ∀e∈events C.mesh,L.rows e≤L.arena.stride)
    (inputs : ∀e∈events C.mesh,(L.term e).Fits W L.arena.first) (ownerRoom : L.arena.endAddress C.mesh<2^W)
    (routeLow : ∀p∈routes,flag<p.out)
    (below : flag<L.arena.first ∧ flag<s.banks.reserved.base ∧ flag<s.banks.used.base ∧ flag<a.scratch ∧
      flag<s.banks.width.base ∧ flag<s.table ∧ flag<s.destination) :
    let n:=recordCount C.mesh issued
    let supply:=fuel C.mesh*payload
    let tail:=terminal C L routes flag s src ss a count n supply
    let price:=terminalTime C L routes s ss a count n supply
    let chk:=checkedOut C flag origin
    let cash:=PaidWidths.output s.banks.width edges src ss chk
    let archive:=result routes (result (L.scans C.mesh count) cash)
    let owner:=nativeSite L C.mesh issued pos chk
    let debitWord:=debit C.mesh issued
    let out:=s.output (ReserveUse.output a s.banks supply owner debitWord archive) enum ci (fun j=>(cj j).val)
    let cpu:=machine (bootProgram z d promotion tail) (flag:Word W)
    PaidWidths.Mounted s.banks.width edges src ss chk →
    Whole.Reconciliation s a supply owner debitWord enum ci cj archive →
    ∃t≤ subdivisionConstant d*2^z+prep+price+2,∃done,
      advance cpu.program t (cpu.program.start state) (Computability.VPVNP.RAMMemory.initialMemory size (Boot.header v size words))
        =some (done,out) ∧ cpu.program.step done=.finish (some (out flag)) ∧
      (out flag=0 ↔ Calendar.admissible C (events C.mesh) origin) := by
  intro n supply tail price chk cash archive owner debitWord out cpu paid settled
  have exec : tail.Exec origin out price :=
    terminal_exec C L routes flag s src ss a issued pos routeFits enum ci cj origin active
      flagFit flagEnd width rows inputs ownerRoom paid settled
  obtain ⟨t,ht,done,run,halt⟩:=boot_machine v layout hd π words auth promotion tail origin out prep price flag state
    (by omega) began exec
  exact ⟨t,ht,done,run,halt,terminal_verdict C L routes flag s src ss a issued pos enum ci cj origin active
    order (by unfold wordBits;omega) paid settled.ports.width routeLow below⟩

end Run

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
