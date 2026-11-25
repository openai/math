import OAI.Hierarchy.DescentTerminalLastReadback
import OAI.Hierarchy.ProtocolRAMMachine

namespace OAI
/-! # Closing a reached terminal program and exposing the same fixed observation wires -/
namespace Hierarchy.DescentTerminalReadout
open DescentTerminalRAM DescentTerminalHost DescentTerminalPorts DescentTerminalThreshold DescentTerminalLast
open ThreeFlat Routing Diagonal TraceRows TraceBanks
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory ProtocolRAM TaggedShorterControlHistory
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {A T P I : Type} [Fintype I] {rows slots word bins W w cut stop arity dest geo : ℕ}
variable (L : Tape) (S : DescentCensusRAM.Banks w slots bins) (ready : Ready L S cut stop rows word)
local notation "Raw" => RowBit rows word→Bool
local notation "Input" => Choice A rows word→Bool

/-- Only earlier, already emitted physical cells are consumed by the suffix.
A malformed candidate is allowed arbitrary total/row values and request words. -/
structure InputCells (μ : Input→Memory w) (decode : Raw→(A→Bool)→Option T)
    (total : T→ℕ) (n : T→I→ℕ) (key : T→Raw→Fin slots→Fin bins) (seed : I→ℕ) : Prop where
  seedOK : ∀a t pay,decode pay a=some t→∀i,μ (Sum.elim a pay) (seed i)=(n t i:Word w)
  whole : ∀a t pay,decode pay a=some t→(μ (Sum.elim a pay) L.whole.base).val=total t/word
  remainder : ∀a t pay,decode pay a=some t→(μ (Sum.elim a pay) L.tail.base).val=total t%word
  request : ∀a t pay,decode pay a=some t→∀i, μ (Sum.elim a pay) (L.keys.base+i.val)=((key t pay i).val:Word w)
  flags : ∀a pay,(∀i,μ (Sum.elim a pay) (L.flags i).base=0) ↔ ∃t,decode pay a=some t

/-- One fixed native suffix for all inputs. Its output readback is total
even on words rejected by every seed and profile decoder. -/
def finalMem (μ : Input→Memory w) (a : Input) : Memory w := Classical.choose (run L S ready (μ a))

theorem suffix (μ : Input→Memory w) (z : Input) :
    (DescentTerminalLast.program L S cut stop rows word).Exec (μ z) (finalMem L S ready μ z) (ticks L S rows word) ∧
    CheapCode (DescentTerminalLast.program L S cut stop rows word) ∧
    Output L S cut stop rows word ready.binsPos (μ z) (finalMem L S ready μ z) :=
  Classical.choose_spec (run L S ready (μ z))

def complete («prefix» : Procedure w) := «prefix».seq (DescentTerminalLast.program L S cut stop rows word)

private abbrev ClosedExecution (P : Procedure w) (flag state : Word w) (start out : Memory w) (budget : ℕ) :=
  let M := ProtocolRAM.machine P flag
  (∃ t cfg result, t < budget+3 ∧
    RAM.advance M.program t (M.program.start state) start = some (cfg,out) ∧
    M.program.step cfg = .finish result) ∧ ∀pc,TaggedShorterCheapCPU.Cheap (M.code pc)

private theorem close_execution (P : Procedure w) (flag state : Word w) (start out : Memory w)
    (budget : ℕ) (go : P.Exec start out budget) (cheap : CheapCode P) :
    ClosedExecution P flag state start out budget := by
  obtain ⟨t,lt,cfg,adv,halt⟩ := machine_run P flag state start out budget go
  exact ⟨⟨t,cfg,_,by omega,adv,halt⟩,machine_cheap P flag cheap⟩

set_option maxHeartbeats 800000 in
theorem full_exec (Q : Procedure w) (initial : Input→Memory w) (μ : Input→Memory w)
    (time : ℕ) (issued : ∀b,Q.Exec (initial b) (μ b) time) (cheapPrefix : CheapCode Q)
    (state : Word w) (z : Input) :
    ClosedExecution (complete L S (cut:=cut) (stop:=stop) (rows:=rows) (word:=word) Q)
      (stop:Word w) state (initial z) (finalMem L S ready μ z) (time+ticks L S rows word) := by
  let P:=complete L S (cut:=cut) (stop:=stop) (rows:=rows) (word:=word) Q
  obtain ⟨go,ch,_⟩:=suffix L S ready μ z
  have execute : P.Exec (initial z) (finalMem L S ready μ z) (time+ticks L S rows word) :=
    Procedure.Exec.then (issued z) go
  exact close_execution P (stop:Word w) state (initial z) (finalMem L S ready μ z) _ execute
    (@cheap_seq w Q (DescentTerminalLast.program L S cut stop rows word) cheapPrefix ch)

variable {widths : Fin arity→ℕ} (x : Catalyst.Port dest widths→Bool) (seed : I→ℕ) (before : ∀i,seed i<cut)
  (short : depth word≤w+1) (width : W≤w+1) (pos : 0<word)
  (μ : (Choice A rows word→Bool)→Memory w) (decode : (RowBit rows word→Bool)→(A→Bool)→Option T)
  (total : T→ℕ) (n : T→I→ℕ) (key : T→(RowBit rows word→Bool)→Fin slots→Fin bins)
  (read : InputCells (slots:=slots) (bins:=bins) (word:=word) L μ decode total n key seed)
local notation "addr" => (fun i=>(observations (fun j:Fin rows=>cut+Fin.val j) seed (fun j:Fin bins=>S.bins+Fin.val j) stop i:Word w))
local notation "obs" => pins (I:=I) short width

include before pos read in
theorem full_admit (nw : ∀t i,n t i<2^w) (a : A→Bool) (t : T) (pay : Raw) (accept : decode pay a=some t) :
    resultPins addr obs x (Sum.elim a pay) (finalMem L S ready μ (Sum.elim a pay))=
      DescentTerminalPaidFactors.factorPins (fun i=>DescentTerminalDenseMask.valid word (total t) i.val) pay
        (countDigit (requests (n t) (key t pay))) := by
  have h:=admit L S ready seed before short width x a pay _ _ (suffix L S ready μ _).2.2
    (n t) (key t pay) (nw t) (read.seedOK a t pay accept) ((read.flags a pay).2 ⟨t,accept⟩)
    (read.request a t pay accept)
  simpa only [read.whole a t pay accept,read.remainder a t pay accept,cutoff_valid _ _ _ pos] using h

include before read in
theorem full_reject {F : Type} [Field F] (original : I→F) (table : Fin bins→F)
    (posW : 0<W) (wide : 1<2^w) (a : A→Bool) (pay : Raw) (bad : decode pay a=none) :
    ∃c f b i,(∀j,c j≤word) ∧ scalar original table b=0 ∧ f (b,i)=true ∧
      resultPins addr obs x (Sum.elim a pay) (finalMem L S ready μ (Sum.elim a pay))=
      DescentTerminalPaidFactors.factorPins c pay f := by
  apply reject L S ready seed before short width x a pay _ _ (suffix L S ready μ _).2.2 original table _ posW wide
  rintro h
  obtain ⟨t,good⟩:=(read.flags a pay).1 h
  rw [bad] at good
  contradiction

end
end Hierarchy.DescentTerminalReadout

end OAI
