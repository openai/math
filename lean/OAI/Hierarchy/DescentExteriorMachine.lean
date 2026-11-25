import OAI.Hierarchy.DescentExteriorCoefficient
import OAI.Hierarchy.ProtocolRAMMachine
import OAI.Hierarchy.TaggedShorterClockCost

namespace OAI
/-! # A real closed-machine trace and linear bit cost for the exterior service -/
namespace Hierarchy.DescentExteriorShelf
open DescentExterior DescentGL Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure ContinuationLink
open scoped Classical Fin.CommRing
noncomputable section

variable {w e j r t : ℕ}
local notation "k" => j+(j+r)
local notation "n" => e*2^(j+r)
local notation "H" => span j r t e

private theorem output_trace {bits cost limit : ℕ} (P : Procedure bits) (flag state : Word bits)
    (pre checked : Memory bits→Prop) (image : Memory bits→Memory bits)
    (serviceSpec : P.Spec pre (fun m o=>o=image m ∧ checked o) cost ∧ CheapCode P)
    (bound : cost+2≤limit)
    (m : Memory bits) (hm : pre m) :
    let cpu:=machine P flag
    (∃fuel≤limit,∃cfg,advance cpu.program fuel (cpu.program.start state) m=some (cfg,image m) ∧
      cpu.program.step cfg=.finish (some (image m flag.val))) ∧
      (∀pc,TaggedShorterCheapCPU.Cheap (cpu.code pc)) ∧ checked (image m) := by
  intro cpu
  obtain ⟨spec,cheap⟩:=serviceSpec
  refine ⟨?_,machine_cheap P flag (@cheap),?_⟩
  · have words : P.Spec pre (fun m o=>o=image m) cost :=
      Procedure.Spec.mono (@spec) (fun _ h=>h) (fun _ _ h=>h.1) le_rfl
    have exe : P.Exec m (image m) cost :=
      @Procedure.Spec.exec bits P cost pre image (@words) m hm
    obtain ⟨t,low,c,ran,stopped⟩:=machine_run P flag state m (image m) cost (@exe)
    exact ⟨t,low.trans bound,c,ran,stopped⟩
  ·
    have installed : P.block.Installed cpu (Fin.castAddEmb 3) (Fin.castAddEmb 1) id
        (Fin.natAdd P.labels (0:Fin 3)) := by
      unfold cpu machine
      exact close_installed (P.block.reindex (Fin.castAddEmb 1) id) (0:Fin 3) _ P.publicData
    obtain ⟨_,_,_,out,_,_,eq,h⟩:=spec cpu (Fin.castAddEmb 3) (Fin.castAddEmb 1)
      id (Fin.natAdd P.labels (0:Fin 3)) installed (fun _=>rfl) (cpu.program.start state) m rfl hm
    exact eq ▸ h

attribute [local irreducible] service serviceMemory machine Receipt Loaded

/-- This is the clock theorem consumed by the two-array RAM detector, with
the actual selected public/hidden words and genuine output memory image. -/
theorem machine_trace (origin : ℕ) (wordPos : 0<w) (wordRoom : 2^j*t≤w)
    (space : origin+22*H<2^w) (M : Fin e→Layout k) (x : Fin e→Plane j r→Fin t→Bool)
    (z : Hidden e j r t→Bool) (m : Memory w) (st flag : Word w) (primed : Loaded origin M x z m) :
    let P:=service w j r t e origin
    let cpu:=machine P flag
    let dst:=serviceMemory (j:=j) (r:=r) (t:=t) (e:=e) origin m
    (∃fuel≤18+364*n,∃cfg,advance cpu.program fuel (cpu.program.start st) m=some (cfg,dst) ∧
      cpu.program.step cfg=.finish (some (dst flag.val))) ∧
      (∀pc,TaggedShorterCheapCPU.Cheap (cpu.code pc)) ∧ Receipt origin M x z dst := by
  exact @output_trace w (16+364*n) (18+364*n) (service w j r t e origin) flag st
    (Loaded origin M x z) (Receipt origin M x z)
    (serviceMemory (j:=j) (r:=r) (t:=t) (e:=e) origin)
    (native_exact origin wordPos wordRoom space M x z) (by omega) m primed


theorem machine_clock_price (w j r t e origin : ℕ) :
    let P:=service w j r t e origin
    TaggedShorterClock.unitPrice w (P.labels+3) (P.registers+1)≤
      (w+1)*TaggedShorterClock.unitPrice 1 553 191 := by
  intro P
  obtain ⟨labels,regs,_⟩:=text_bound w j r t e origin
  change TaggedShorterClock.unitPrice w ((service w j r t e origin).labels+3)
    ((service w j r t e origin).registers+1)≤_
  rw [labels,regs]
  exact TaggedShorterClock.unitPrice_le ..

end
end Hierarchy.DescentExteriorShelf

end OAI
