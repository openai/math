import OAI.Optimization.LinearProgramming.Compression.BinaryWireAdapter
import OAI.Optimization.LinearProgramming.BitRAM.NativeLinked
import OAI.Optimization.LinearProgramming.Games.RecoveryMachineWire

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM RAM.Tape RAM.Callable BitRAM OracleSpec OracleSpec.MinorLog
open Games.RecoveryMachine (outputWire)

/-- The checked BitStack `writeAnswer` transducer emits precisely the physical decoder's word. -/
theorem optionalRationalWord_eq_outputWire (r : Option ℚ) : optionalRationalWord r = outputWire r := by
  cases r <;> rfl

/-- Inlined numeric handler, interpreted bit program, and physical optional-value decoder. -/
def linkedTaggedFlatTail (p : BitProgram) (handler : Fragment) : Fragment :=
  .seq (NativeService.linkedOutput p handler) (.ofBlock decodeTaggedFlatReply)

def linkedDriverClock (p : BitProgram) (factor steps k : ℕ) :=
  (2*p.states+64+factor)*steps+2+(13*k+7)

/-- Relocatable computation up to the final two-instruction public return. -/
theorem linkedTaggedFlatReply_run {p : BitProgram} {bo : WordOracle} {handler : Fragment}
    {ctx : Transcript → Memory ℚ → Prop} {allowed : p.Config → Fin p.states → Prop} {factor limit : ℕ}
    (machine : NativeService.Implements p bo handler (fun z=>ratBits z ≤ limit) ctx allowed factor)
    {c d : p.Config} {steps : ℕ} (source : p.Run bo c steps d) (halt : d.pc=none)
    (valid : Dispatch.PermittedAsksFrom p bo allowed c) {m : Memory ℚ} (rep : Rep p c m)
    (safe : m.AllData (fun z=>ratBits z ≤ limit)) (initial : ctx c.transcript m)
    (r : Option ℚ) (wire : d.bufferRev.reverse=outputWire r) (budget : 2*(outputWire r).length+7 ≤ limit) :
    ∃ z, (linkedTaggedFlatTail p handler).Run (fun y=>ratBits y ≤ limit) m
      (linkedDriverClock p factor steps (outputWire r).length + (taggedReplyClock (outputWire r).length-2)) z ∧
      TaggedReady z r := by
  have h0 : ratBits (0:ℚ) ≤ limit := by change 3 ≤ limit; omega
  have h1 : ratBits (1:ℚ) ≤ limit := by change 3 ≤ limit; omega
  obtain ⟨a,native,_,endCtx,len,packet⟩ := NativeService.run_output machine h0 h1 source halt valid rep safe initial
  rw [wire] at len packet
  obtain ⟨s,z,publish,clock,result⟩ := decodeTaggedFlatReply_spec a r limit native.safe_end
    (machine.ports _ _ endCtx).1 (by simpa only [bufferLenReg,optionalRationalWord_eq_outputWire] using len)
    (by
      rw [optionalRationalWord_eq_outputWire]
      intro i hi
      have entry := packet i hi
      rw [show sendBaseReg = 43 from rfl] at entry
      refine entry.trans ?_
      cases (outputWire r)[i] <;> rfl)
    (by simpa only [optionalRationalWord_eq_outputWire] using budget)
  rw [optionalRationalWord_eq_outputWire] at clock
  have joined := native.seq (Fragment.Run.ofBlock publish)
  have eqLen : d.bufferRev.length=(outputWire r).length := by simpa using congrArg List.length wire
  refine ⟨z,joined.mono ?_,result⟩
  unfold linkedDriverClock
  rw [eqLen]; omega

/-- Standalone deployment when the interpreter's ordinary memory is already prepared. -/
def linkedTaggedFlatReply (p : BitProgram) (handler : Fragment) : Program :=
  finishTaggedFragment (linkedTaggedFlatTail p handler)

theorem linkedTaggedFlatReply_call {p : BitProgram} {bo : WordOracle} {handler : Fragment}
    {ctx : Transcript → Memory ℚ → Prop} {allowed : p.Config → Fin p.states → Prop} {factor limit : ℕ}
    (machine : NativeService.Implements p bo handler (fun z=>ratBits z ≤ limit) ctx allowed factor)
    {c d : p.Config} {steps : ℕ} (source : p.Run bo c steps d) (halt : d.pc=none)
    (valid : Dispatch.PermittedAsksFrom p bo allowed c) {m : Memory ℚ} (rep : Rep p c m)
    (safe : m.AllData (fun z=>ratBits z ≤ limit)) (initial : ctx c.transcript m)
    (r : Option ℚ) (wire : d.bufferRev.reverse=outputWire r) (budget : 2*(outputWire r).length+7 ≤ limit) :
    ∃ t, call (linkedTaggedFlatReply p handler)
      (linkedDriverClock p factor steps (outputWire r).length + taggedReplyClock (outputWire r).length)
      limit (m.atPC 0) t ∧ emits t r := by
  obtain ⟨z,go,ready⟩ := linkedTaggedFlatReply_run machine source halt valid rep safe initial r wire budget
  obtain ⟨t,⟨l,hl,tr,run,last,ht⟩,out⟩ := finishTaggedFragment_run _ m z r limit _ go ready
  have h2 : 2 ≤ taggedReplyClock (outputWire r).length := by unfold taggedReplyClock; omega
  exact ⟨t,⟨l,by omega,tr,run,last,ht⟩,out⟩

/-- The numeric-cache/bytecode setup may run in the same physical program immediately
before the binary interpreter. No second virtualization or new memory image is required. -/
def prefixLinkedTaggedFlatReply (front : Fragment) (p : BitProgram) (handler : Fragment) : Program :=
  finishTaggedFragment (.seq front (linkedTaggedFlatTail p handler))

theorem prefixLinkedTaggedFlatReply_call {front : Fragment} {p : BitProgram} {bo : WordOracle} {handler : Fragment}
    {ctx : Transcript → Memory ℚ → Prop} {allowed : p.Config → Fin p.states → Prop}
    {factor limit setupClock : ℕ} {ordinary m : Memory ℚ}
    (setup : front.Run (fun z=>ratBits z ≤ limit) ordinary setupClock m)
    (machine : NativeService.Implements p bo handler (fun z=>ratBits z ≤ limit) ctx allowed factor)
    {c d : p.Config} {steps : ℕ} (source : p.Run bo c steps d) (halt : d.pc=none)
    (valid : Dispatch.PermittedAsksFrom p bo allowed c) (rep : Rep p c m)
    (initial : ctx c.transcript m) (r : Option ℚ) (wire : d.bufferRev.reverse=outputWire r)
    (budget : 2*(outputWire r).length+7 ≤ limit) :
    ∃ t, call (prefixLinkedTaggedFlatReply front p handler)
      (setupClock + linkedDriverClock p factor steps (outputWire r).length + taggedReplyClock (outputWire r).length)
      limit (ordinary.atPC 0) t ∧ emits t r := by
  obtain ⟨z,go,ready⟩ := linkedTaggedFlatReply_run machine source halt valid rep setup.safe_end initial r wire budget
  obtain ⟨t,⟨l,hl,tr,run,last,ht⟩,out⟩ := finishTaggedFragment_run _ ordinary z r limit _ (setup.seq go) ready
  have h2 : 2 ≤ taggedReplyClock (outputWire r).length := by unfold taggedReplyClock; omega
  exact ⟨t,⟨l,by omega,tr,run,last,ht⟩,out⟩

end Compression
end LinearProgramming
end Optimization
end OAI
