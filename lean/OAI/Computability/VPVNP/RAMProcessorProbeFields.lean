import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.RAMTapeWordOperands

/-!
# Staging ports for external reads, writes, and call returns

The architectural bank shares the read destination and the address and value
registers with the instruction interpreter. Three separate field stacks feed
the pre-sort record writer. Both copy stacks are empty at every boundary.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ProbeStages

open BurstRAM TapeWord

/-- Non-architectural ports for the choice stream, staged record fields, running flag and two
copy stacks. -/
inductive Extra where
  | choices | tag | address | value | running | copyA | copyB
  deriving DecidableEq

instance : Fintype Extra := derive_fintype% _

/-- Combined port space for the instruction interpreter and the extra stacks used to stage
external probes. -/
abbrev Port (r k : ℕ) := ISA.Port r k ⊕ Extra

/-- Stack contents at a probe-stage boundary, comprising the architectural bank, unused
choices, staged record fields and running flag. -/
structure Bank (r k : ℕ) where
  /-- Architectural register, public-word, persistent-state and interpreter workspace stacks
  available to the probe stages. -/
  isa : Stacks (ISA.Port r k)
  /-- Remaining private bits from which an external read draws its guessed word. -/
  choices : List Bool
  /-- Encoded operation tag staged for the next memory record. -/
  tag : List Bool
  /-- Bits of the probed address, saved before a read may overwrite its address register. -/
  address : List Bool
  /-- Payload bits for the next record, drawn from the choice stream on a read and from a
  register on a write. -/
  value : List Bool
  /-- Stack encoding the site's running flag, which the accept callback sets to false. -/
  running : List Bool

variable {r k w : ℕ}

/-- Realize the probe-stage bank on the combined port space, supplying empty stacks at both
copy ports. -/
def Bank.stacks (s : Bank r k) : Stacks (Port r k)
  | .inl p => s.isa p
  | .inr .choices => s.choices
  | .inr .tag => s.tag
  | .inr .address => s.address
  | .inr .value => s.value
  | .inr .running => s.running
  | .inr .copyA | .inr .copyB => []

/-- Word transfers for staging register operands, assigning a read result, returning a
persistent state or forming a record tag. -/
inductive Transfer (r : ℕ) where
  | address (i : Fin r) | value (i : Fin r) | assign (i : Fin r) | returnState (i : Fin r) | tag

/-- Source port for a staged word transfer. Tag generation uses the persistent word as its
width template. -/
def Transfer.src : Transfer r → Port r k
  | .address i | .value i | .returnState i => .inl (.reg i)
  | .assign _ => .inr .value
  | .tag => .inl .persistent

/-- Port receiving the transfer's word, selected among the record fields, a read destination
register and persistent state. -/
def Transfer.dst : Transfer r → Port r k
  | .address _ => .inr .address
  | .value _ => .inr .value
  | .assign i => .inl (.reg i)
  | .returnState _ => .inl .persistent
  | .tag => .inr .tag

/-- Install a bit string at the transfer's destination in the structured probe bank. -/
def Transfer.set (f : Transfer r) (s : Bank r k) (data : List Bool) : Bank r k :=
  match f with
  | .address _ => {s with address := data}
  | .value _ => {s with value := data}
  | .assign i => {s with isa := Function.update s.isa (.reg i) data}
  | .returnState _ => {s with isa := Function.update s.isa .persistent data}
  | .tag => {s with tag := data}

theorem Transfer.set_stacks (f : Transfer r) (s : Bank r k) (data : List Bool) :
    Function.update s.stacks f.dst data = (f.set s data).stacks := by
  funext j
  rcases j with j | j
  · cases f <;> simp [Transfer.dst, Transfer.set, Bank.stacks, Function.update] <;> split_ifs <;> simp_all <;> subst_vars <;> rfl
  · cases f <;> cases j <;> rfl

private def ports (f : Transfer r) : ScanPort → Port r k
  | .left => f.src
  | .right => .inr .copyA
  | .tmp => .inr .copyB
  | .out => f.dst

private theorem injective (f : Transfer r) : Function.Injective (ports (k := k) f) := by
  intro i j h
  cases f <;> cases i <;> cases j <;> simp_all [ports, Transfer.src, Transfer.dst]

private def normal {A : Type} : Operand.State A → Bool
  | .done _ => true
  | _ => false

private def wordRoutine {A : Type} [Fintype A] (f : Transfer r)
    (step : A → Bool → Bool × A) (a : A) : FiniteRoutine (Port r k) :=
  .ofStackCode (Operand.code step) (ports f) (.clear a) normal

private theorem wordRun {A : Type} [Fintype A] (f : Transfer r) (step : A → Bool → Bool × A)
    (a b : A) (s : Bank r k) (data : List Bool) (n : ℕ)
    (h : StackRuns (Operand.code step) n (.clear a)
      (scanStacks (s.stacks f.src) [] [] (s.stacks f.dst)) (.done b)
      (scanStacks (s.stacks f.src) [] [] data)) :
    (wordRoutine f step a).Runs n s.stacks (f.set s data).stacks := by
  rw [← Transfer.set_stacks]
  refine FiniteRoutine.runs_ofStackCode_framed (injective f) (normal := normal) rfl rfl
    (fun q hq => ?_) h ?_ ?_ ?_
  · cases q <;> first | rfl | contradiction
  · intro i; cases i <;> rfl
  · intro i
    cases f <;> cases i <;> simp [ports, Transfer.src, Transfer.dst, scanStacks, Bank.stacks]
  · intro j hj
    exact Function.update_of_ne (Ne.symm (hj .out)) ..

/-- Copy a transfer's source word to its destination using the two staging scratch stacks and
restore the source. -/
def copy (f : Transfer r) : FiniteRoutine (Port r k) := wordRoutine f Operand.copyBit ()

theorem copy_run (f : Transfer r) (s : Bank r k) :
    (copy f).Runs ((s.stacks f.dst).length + 7*(s.stacks f.src).length + 3) s.stacks
      (f.set s (s.stacks f.src)).stacks := wordRun f _ () () s _ _ (Operand.copy_run ..)

/-- Write the literal record tag at the width of the persistent word, reducing the literal
modulo the word capacity. -/
def setTag (n : ℕ) : FiniteRoutine (Port r k) :=
  wordRoutine .tag (Operand.literalBit n) (Fin.last n)

theorem tag_run (n : ℕ) (s : Bank r k) (p : Word w) (hp : s.isa .persistent = wordBits p) :
    (setTag n).Runs (s.tag.length + 7*w + 3) s.stacks
      ({s with tag := wordBits (Fin.ofNat (2^w) n)} : Bank r k).stacks := by
  obtain ⟨b, h⟩ := Operand.literal_run n p s.tag
  apply wordRun .tag _ (Fin.last n) b s _ _
  simpa only [Transfer.src, Transfer.dst, Bank.stacks, hp] using h

end RAMTape.ProbeStages

end VPVNP
end Computability
end OAI
