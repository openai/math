import OAI.Computability.BorderVNP.DiagonalNativeSequence
import OAI.Computability.BorderVNP.DiagonalNativeUnit
import OAI.Computability.BorderVNP.TransmissionPinSlots

/-! # The signed native evaluator on the true processor initialization

Returning traces can be counted using either structured execution or the fetched opcode
table whenever the code has no early accepting halt. The input to the charged machine
is the actual concatenation of literal, exterior and secondary-pin segments of the
processors, followed in memory by zeros. The bijections retain every instruction event.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP BurstRAM TeamContraction
open scoped BigOperators

variable {w : ℕ} (c : Code) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w)

/-- Structured returns and native acceptances indexed by their actual per-instruction
choice tapes are in bijection when success occurs at the fall-through halt. -/
noncomputable def returnAcceptEquiv (hc : c.withoutAccept = true) :
    Returns c pub mac s m ≃ NativeAccepts c pub mac s m := by
  let f (x : Returns c pub mac s m) : NativeAccepts c pub mac s m :=
    ⟨(x.val.1.map TeamRAM.Event.choices,x.val.1),x.property.execute⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y eq
    have he : x.val.1 = y.val.1 := congrArg (fun z => z.val.2) eq
    obtain ⟨_,ht,hm⟩ := x.property.eq_of_shared_events y.property
      (tail := []) (tail' := []) (by simp only [List.append_nil,he])
    exact Subtype.ext (Prod.ext he (Prod.ext ht hm))
  · intro y
    obtain ⟨⟨z,mz,run⟩,ht⟩ := (Code.execute_iff_runs hc).mp y.property
    exact ⟨⟨(y.val.2,z,mz),run⟩,Subtype.ext (Prod.ext ht rfl)⟩

/-- The accepting history and its private choice tapes are exactly the recorded
history and its event-by-event choice projection. -/
theorem returnAcceptEquiv_val (hc : c.withoutAccept = true) (x : Returns c pub mac s m) :
    (returnAcceptEquiv c pub mac s m hc x).val = (x.val.1.map TeamRAM.Event.choices,x.val.1) := rfl

/-- Passing from returning traces with a final state to accepting traces preserves
the exact integer sum. -/
theorem nativeAccepts_eq_return_sum (hc : c.withoutAccept = true)
    [Fintype (Returns c pub mac s m)] [Fintype (NativeAccepts c pub mac s m)] :
    (∑ z : NativeAccepts c pub mac s m, pathWeight z.val.2) =
      ∑ x : Returns c pub mac s m, pathWeight x.val.1 := by
  rw [← (returnAcceptEquiv c pub mac s m hc).sum_comp (fun z => pathWeight z.val.2)]
  rfl

variable {L : Pins.Layout} (fields : Pins.ProcessorFields L)

/-- Initial shared memory on the literal, exterior and pin input of the processors. -/
def processorMemory (w : ℕ) : Memory w :=
  RAMMemory.initialMemory fields.header.length (TeamTapeInputEmit.headerWord w fields.header)

/-- The paper's charged machine input with the actual finite opcode table, entry PC
zero, live registers and full physical processor header. -/
def processorMachine : MachineInput w (TeamOpcode.State w (c.slots+1) 64) where
  program := c.program.fetch pub mac
  start := ⟨0,s⟩
  inputSize := fields.header.length
  header := TeamTapeInputEmit.headerWord w fields.header

variable (ticks burst clock : ℕ)

/-- The native paths at any cutoff are exactly the accepting traces that obey all
three physical budgets, even for a code with an early accepting instruction. -/
def boundedAcceptEquiv :
    {z : NativeAccepts c pub mac s (processorMemory fields w) // Within ticks burst clock z.val.2} ≃
      NativePath (processorMachine c pub mac s fields) ticks burst clock where
  toFun z := ⟨z.val.val.2,(TeamRAM.execute_spec z.val.property).2.2.symm ▸ z.val.property,z.property⟩
  invFun p := ⟨⟨(p.val.map TeamRAM.Event.choices,p.val),p.property.1⟩,p.property.2⟩
  left_inv z := Subtype.ext (Subtype.ext (Prod.ext (TeamRAM.execute_spec z.val.property).2.2 rfl))
  right_inv _ := rfl

variable (hc : c.withoutAccept = true)
    (budget : ∀ x : Returns c pub mac s (processorMemory fields w), Within ticks burst clock x.val.1)

/-- When each returning trace fits the charged budgets, dropping the redundant
tape and inserting its budget proof is an equivalence to the genuine RAM paths. -/
noncomputable def acceptNativePathEquiv :
    NativeAccepts c pub mac s (processorMemory fields w) ≃
      NativePath (processorMachine c pub mac s fields) ticks burst clock := by
  let e : NativeAccepts c pub mac s (processorMemory fields w) ≃
      {z : NativeAccepts c pub mac s (processorMemory fields w) // Within ticks burst clock z.val.2} :=
    { toFun z := ⟨z,by
        obtain ⟨⟨t,mt,run⟩,_⟩ := (Code.execute_iff_runs hc).mp z.property
        exact budget ⟨(z.val.2,t,mt),run⟩⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.trans (boundedAcceptEquiv c pub mac s fields ticks burst clock)

/-- The signed history itself is unchanged by passing to the native bounded path. -/
theorem acceptNativePathEquiv_events (z : NativeAccepts c pub mac s (processorMemory fields w)) :
    (acceptNativePathEquiv c pub mac s fields ticks burst clock hc budget z).val = z.val.2 := rfl

include hc budget

/-- The charged finite-path theorem also makes the unrestricted returning family
finite on this input once all of its traces satisfy the cutoff. -/
theorem processorReturns_finite : Finite (Returns c pub mac s (processorMemory fields w)) :=
  Finite.of_equiv _ ((returnAcceptEquiv c pub mac s (processorMemory fields w) hc).trans
    (acceptNativePathEquiv c pub mac s fields ticks burst clock hc budget)).symm

/-- The actual charged native value equals the unrestricted signed sum over accepting
traces on the very same physical processor input. -/
theorem nativeValue_eq_accept_sum [Fintype (NativeAccepts c pub mac s (processorMemory fields w))] :
    nativeValue (processorMachine c pub mac s fields) ticks burst clock =
      ∑ z : NativeAccepts c pub mac s (processorMemory fields w), pathWeight z.val.2 := by
  classical
  unfold nativeValue
  let := Fintype.ofFinite (NativePath (processorMachine c pub mac s fields) ticks burst clock)
  exact ((acceptNativePathEquiv c pub mac s fields ticks burst clock hc budget).sum_comp
    (fun z => pathWeight z.val)).symm

/-- The charged machine value is the signed sum of structured returns with their
true chronological trace, post-registers and post-memory. -/
theorem nativeValue_eq_return_sum [Fintype (Returns c pub mac s (processorMemory fields w))] :
    nativeValue (processorMachine c pub mac s fields) ticks burst clock =
      ∑ x : Returns c pub mac s (processorMemory fields w), pathWeight x.val.1 := by
  let := Fintype.ofEquiv _ (returnAcceptEquiv c pub mac s (processorMemory fields w) hc)
  exact (nativeValue_eq_accept_sum c pub mac s fields ticks burst clock hc budget).trans
    (nativeAccepts_eq_return_sum c pub mac s _ hc)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
