import OAI.Computability.VPVNP.CompressorOnlineBranchCut
import OAI.Computability.VPVNP.CompressionState

/-! # Complete descriptor paths indexed by the mathematical compression tree

An internal node has the native cut for its single compression pass. Its
children begin in the memory and control state returned for the selected term.
At a leaf the last deterministic native segment halts. Recursion gives an
exact bijection with complete accepting streams of the one fixed table,
retaining its actual reports, final memory and optional resource predicate.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BranchSegments
open BurstRAM Compression

variable {w cap : ℕ} {Q : Type*} {P : BurstRAM.Program w Q}
variable {st : Option (Word w)} {m : Memory w}
variable {R : Type*} [CommSemiring R] {a g b n : ℕ} {X : State a g}

/-- One local pass on the native machine and recursive executions on its
actual outputs. The only terminal case is a forced native halting segment. -/
inductive ExecutionTrace (P : BurstRAM.Program w Q) (cap : ℕ) :
    {a g b n : ℕ} → {X : State a g} → StateExecution R b n X → Option (Word w) → Memory w → Type _ where
  | done {b n : ℕ} {X : State b n} {st m} (s : Segment P cap st m) (calls : ℕ)
      (quiet : s.bits = List.replicate calls []) (halt : s.state = none) : ExecutionTrace P cap (.done X) st m
  | more {a g a' g' b n : ℕ} {X : State a g} {p : StatePass R X a' g'}
      {tail : ∀ i, StateExecution R b n (p.next i)} {st m}
      (pass : Cut P cap st m p.step.Choice)
      (next : ∀ i, ExecutionTrace P cap (tail i) (pass.part i).state (pass.part i).memory) :
      ExecutionTrace P cap (.more p tail) st m

namespace ExecutionTrace

variable {E : StateExecution R b n X}

/-- The native prefix is the concatenation of the chosen passes and the
terminating segment on that very branch. -/
def cut {a g b n : ℕ} {X : State a g} {E : StateExecution R b n X} {st m} (t : ExecutionTrace P cap E st m) : Cut P cap st m E.Choices :=
  match t with
  | .done s calls quiet _ => Cut.deterministic s calls quiet
  | .more pass next => pass.bind fun i => cut (next i)

theorem stopped (t : ExecutionTrace P cap E st m) (z : E.Choices) : (t.cut.part z).state = none := by
  induction t with
  | done s calls quiet halt => exact halt
  | more pass next ih => exact ((pass.part z.1).append_state ((next z.1).cut.part z.2)).trans (ih z.1 z.2)

private theorem stopped_empty {bits rs} (run : runSegment P cap none m bits = some rs) : bits = [] ∧ rs = [] := by
  cases bits with
  | nil => exact ⟨rfl,(Option.some.inj run).symm⟩
  | cons b bs => contradiction

/-- Complete accepted paths with a report predicate are exactly the terms
whose actual descriptor execution meets that predicate. -/
noncomputable def acceptedEquiv (t : ExecutionTrace P cap E st m) (allow : List (Report w) → Prop) :
    {z : E.Choices // allow (t.cut.part z).logs} ≃ LiveProgram.PathsFrom P cap st m allow := by
  classical
  let emit (z : {z : E.Choices // allow (t.cut.part z).logs}) : LiveProgram.PathsFrom P cap st m allow :=
    ⟨(t.cut.part z.val).bits,_,(t.cut.part z.val).run,t.stopped z.val,z.property⟩
  apply Equiv.ofBijective emit
  constructor
  · intro a b h
    apply Subtype.ext
    apply t.cut.separate a.val b.val [] []
    simpa only [List.append_nil] using congrArg Subtype.val h
  · rintro ⟨bs,rs,run,halt,good⟩
    obtain ⟨i,rest,more,hb,hl,hr,_⟩ := t.cut.split run halt
    rw [t.stopped i] at hr
    obtain ⟨rfl,rfl⟩ := stopped_empty hr
    rw [List.append_nil] at hl hb
    exact ⟨⟨i,hl ▸ good⟩,Subtype.ext hb.symm⟩

@[simp] theorem acceptedEquiv_bits (t : ExecutionTrace P cap E st m) (allow : List (Report w) → Prop)
    (z : {z : E.Choices // allow (t.cut.part z).logs}) :
    ((t.acceptedEquiv allow) z).val = (t.cut.part z.val).bits := rfl

/-- Every mathematical branch meets the allotted resource predicate. -/
noncomputable def allEquiv (t : ExecutionTrace P cap E st m) (allow : List (Report w) → Prop)
    (allowed : ∀ z, allow (t.cut.part z).logs) : E.Choices ≃ LiveProgram.PathsFrom P cap st m allow :=
  (Equiv.subtypeUnivEquiv allowed).symm.trans (t.acceptedEquiv allow)

@[simp] theorem allEquiv_bits (t : ExecutionTrace P cap E st m) (allow : List (Report w) → Prop)
    (allowed : ∀ z, allow (t.cut.part z).logs) (z : E.Choices) :
    (t.allEquiv allow allowed z).val = (t.cut.part z).bits := rfl

end ExecutionTrace
end CompressorRecords.BranchSegments

end VPVNP
end Computability
end OAI
