import OAI.Computability.BorderVNP.TeamRAM
import Mathlib.Data.Set.Finite.List

/-! # Finite signed path sums of the charged team RAM

The external instruction clock bounds the number of choice blocks. The private clock
bounds the length of each block, including branches inside bursts. These two bounds
make the accepting adaptive RAM paths finite without any finiteness assumption on
the semantic state space. The choice tape determines the event list even when distinct
branch choices give the same registers and sign.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP TeamRAM
open BurstRAM (Word)
open scoped BigOperators Classical

/-- The machine, initial state, and the actual consecutive word header. -/
structure MachineInput (w : ℕ) (S : Type*) where
  /-- Fixed semantic instruction table. -/
  program : S → Instr w S
  /-- Initial control and registers. -/
  start : S
  /-- Number of occupied input addresses. -/
  inputSize : ℕ
  /-- Initial data at those addresses. -/
  header : ℕ → Word w

/-- Independent resource bounds on a chronological trace. -/
structure Within {w : ℕ} (ticks burst privateClock : ℕ) (es : List (Event w)) : Prop where
  /-- Total charged ticks, one plus the burst length at each call. -/
  cost : RAMBuckets.cost (fun e => e.action.extra) es ≤ ticks
  /-- Maximum number of consecutive addressed words read by a private routine. -/
  length : ∀ e ∈ es, e.action.extra ≤ burst
  /-- Maximum number of binary transitions on any instruction's exact private tape. -/
  choices : ∀ e ∈ es, e.choices.length ≤ privateClock

variable {w : ℕ} {S : Type*}

/-- Genuine accepting paths, retaining the individual private branch strings.
Every old word comes from execution on the real mutable external memory. -/
abbrev NativePath (M : MachineInput w S) (ticks burst privateClock : ℕ) :=
  { es : List (Event w) // execute M.program M.start (RAMMemory.initialMemory M.inputSize M.header)
      (es.map Event.choices) = some es ∧ Within ticks burst privateClock es }

private abbrev Tapes (ticks clock : ℕ) :=
  { bs : List (List Bool) // bs.length ≤ ticks ∧ ∀ b ∈ bs, b.length ≤ clock }

private theorem tapesFinite (ticks clock : ℕ) : Finite (Tapes ticks clock) := by
  let Short := {b : List Bool // b.length ≤ clock}
  let : Finite Short := List.finite_length_le Bool clock
  let : Finite {bs : List Short // bs.length ≤ ticks} := List.finite_length_le Short ticks
  let code (bs : Tapes ticks clock) : {s : List Short // s.length ≤ ticks} :=
    ⟨bs.val.attachWith _ bs.property.2, List.length_attachWith.le.trans bs.property.1⟩
  apply Finite.of_injective code
  intro b c he
  apply Subtype.ext
  simpa [code,Short] using congrArg (fun s : {s : List Short // s.length ≤ ticks} => s.val.map Subtype.val) he

/-- Every accepted trace is uniquely indexed by its actual chronological choice blocks. -/
instance finiteNativePath (M : MachineInput w S) (ticks burst clock : ℕ) :
    Finite (NativePath M ticks burst clock) := by
  let := tapesFinite ticks clock
  let tape (p : NativePath M ticks burst clock) : Tapes ticks clock := ⟨p.val.map Event.choices, by
    constructor
    · rw [List.length_map]; have h := p.property.2.cost; rw [RAMBuckets.cost_eq_length_add_probes] at h; omega
    · intro b hb; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb; exact p.property.2.choices e he⟩
  apply Finite.of_injective tape
  intro p q he
  apply Subtype.ext
  have ht : p.val.map Event.choices = q.val.map Event.choices := congrArg Subtype.val he
  have hx := p.property.1
  rw [ht,q.property.1] at hx
  exact Option.some.inj hx.symm

/-- The paper's weight on an accepting path, multiplying only the actual instruction signs. -/
def pathWeight (es : List (Event w)) : ℤ := (es.map (Sign.value ∘ Event.sign)).prod

/-- Signed value of the RAM on its true shared memory up to the charged cutoff. -/
noncomputable def nativeValue (M : MachineInput w S) (ticks burst privateClock : ℕ) : ℤ :=
  letI := Fintype.ofFinite (NativePath M ticks burst privateClock)
  ∑ p : NativePath M ticks burst privateClock, pathWeight p.val

end TeamContraction

end BorderVNP
end Computability
end OAI
