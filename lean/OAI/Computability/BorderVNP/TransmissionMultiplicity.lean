import OAI.Computability.BorderVNP.TransmissionProgramBits
import OAI.Computability.BorderVNP.TransmissionChoiceDecoder
import OAI.Computability.BorderVNP.TransmissionTableInverse
import OAI.Computability.BorderVNP.TransmissionPinsPositive

/-! # Multiplicity of the physical transmission program

An assignment consists of exactly one bit for each locally shared slot. Every
permitted assignment gives one returning native history, and every such history
has a permitted assignment. Remote sends are checked against the actual source
word along the memory trajectory of that assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ}

/-- Two chronological streams agree exactly when their assignments agree at every
locally shared slot. There are no spurious choices from padding or other teams. -/
theorem tableChoiceBits_eq_iff_slot_eq (rows : ℕ → Range w) (self : Word w) (a b : ℕ → ℕ → Bool) (k : ℕ) :
    tableChoiceBits rows self a k = tableChoiceBits rows self b k ↔
      ∀ i < k, (rows i).selected self = some (some .sharedHere) →
        ∀ j < (rows i).width.val, a i j = b i j := by
  simp only [tableChoiceBits_eq_iff, Range.choiceBits_eq_iff]

/-- Admitted words have one position per locally shared slot and pass every physical
role check on the actual successive memories. -/
def PermittedWords (rows : ℕ → Range w) (pub : Arg → Word w) (m : Memory w) :=
  {b : Fin (choiceOffset rows (directoryFrame pub m 0) (directoryFrame pub m 13).val) → Bool //
    ∃ bits : ℕ → ℕ → Bool,
      (∀ i < (directoryFrame pub m 13).val, (rows i).allowed (directoryFrame pub m 0) pub
        (tableMemory rows (directoryFrame pub m 0) pub m bits i) (bits i)) ∧
      tableChoiceBits rows (directoryFrame pub m 0) bits (directoryFrame pub m 13).val = List.ofFn b}

/-- A native return, retaining the complete chronological trace, final registers and memory. -/
def TableReturn (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) :=
  {z : List (TeamRAM.Event w) × Bank w × Memory w // Runs pub macros transmitRanges s m z.1 z.2.1 z.2.2}

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Every opcode of the entire transmit-ranges traversal is native. -/
theorem transmitRanges_native : ∀ pc, transmitRanges.program.tag pc = .native := by decide

/-- Replaying any admitted representative of a returned choice word gives the actual
final memory, the incident-only cost bound and positive sign at every transmission event. -/
theorem table_return_effects (rows : ℕ → Range w) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (bits : ℕ → ℕ → Bool)
    (table : ∀ i < (directoryFrame pub m 13).val,
      rangeAt (tableMemory rows (directoryFrame pub m 0) pub m bits i)
        (cursorAt (directoryFrame pub m 12) 7 i) (cursorAt (directoryFrame pub m 20) 1 i) = rows i)
    (allowed : ∀ i < (directoryFrame pub m 13).val, (rows i).allowed (directoryFrame pub m 0) pub
      (tableMemory rows (directoryFrame pub m 0) pub m bits i) (bits i))
    (r : TableReturn pub macros s m)
    (word : r.val.1.flatMap TeamRAM.Event.choices = tableChoiceBits rows
      (directoryFrame pub m 0) bits (directoryFrame pub m 13).val) :
    r.val.2.2 = tableMemory rows (directoryFrame pub m 0) pub m bits (directoryFrame pub m 13).val ∧
      traceCost r.val.1 ≤ setup.slots + (20 + decision.depth)*(directoryFrame pub m 13).val +
        (∑ i ∈ Finset.range (directoryFrame pub m 13).val, (rows i).teamCost (directoryFrame pub m 0)) + 1 ∧
      ∀ e ∈ r.val.1, e.sign = .plus := by
  obtain ⟨fs,u,canon,cb,cost⟩ := table_runs_bits rows pub macros m s bits table allowed
  have he : fs.flatMap TeamRAM.Event.choices ++ [] = r.val.1.flatMap TeamRAM.Event.choices ++ [] :=
    congrArg (· ++ []) (cb.trans word.symm)
  obtain ⟨et,_,em⟩ := DiagonalResidueRAM.unique_returns transmitRanges_native canon r.property he
  exact ⟨em.symm,et ▸ cost,r.property.positive (by decide)⟩

/-- A guess-preserving bijection between the finite permitted slot assignments and the
actual returning execution histories of the sparse transmission program. -/
theorem table_return_equiv (rows : ℕ → Range w) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w)
    (table : ∀ bits : ℕ → ℕ → Bool, ∀ i < (directoryFrame pub m 13).val,
      rangeAt (tableMemory rows (directoryFrame pub m 0) pub m bits i)
        (cursorAt (directoryFrame pub m 12) 7 i) (cursorAt (directoryFrame pub m 20) 1 i) = rows i)
    (safe : ∀ bits : ℕ → ℕ → Bool, ∀ i < (directoryFrame pub m 13).val,
      (rows i).arithmeticSafe (directoryFrame pub m 0) pub
        (tableMemory rows (directoryFrame pub m 0) pub m bits i)) :
    ∃ e : PermittedWords rows pub m ≃ TableReturn pub macros s m,
      ∀ b, (e b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b.val := by
  classical
  have make (b : PermittedWords rows pub m) : ∃ r : TableReturn pub macros s m,
      r.val.1.flatMap TeamRAM.Event.choices = List.ofFn b.val := by
    obtain ⟨bits,ok,h⟩ := b.property
    obtain ⟨es,t,run,stream,_⟩ := table_runs_bits rows pub macros m s bits (table bits) ok
    exact ⟨⟨⟨es,t,_⟩,run⟩,stream.trans h⟩
  choose f hf using make
  refine ⟨Equiv.ofBijective f ⟨?_,?_⟩, hf⟩
  · intro a b he
    apply Subtype.ext
    exact List.ofFn_injective ((hf a).symm.trans (he ▸ hf b))
  · intro r
    obtain ⟨bits,ok,_,he⟩ := table_sound rows pub macros m s table safe r.property
    let xs := tableChoiceBits rows (directoryFrame pub m 0) bits (directoryFrame pub m 13).val
    let k := choiceOffset rows (directoryFrame pub m 0) (directoryFrame pub m 13).val
    have hk : xs.length = k := tableChoiceBits_length ..
    let b (j : Fin k) := xs[j.val]'(j.isLt.trans_eq hk.symm)
    have hx : List.ofFn b = xs := by
      apply List.ext_getElem (by simp [hk])
      intro i _ _
      simp [b]
    let a : PermittedWords rows pub m := ⟨b,bits,ok,hx.symm⟩
    refine ⟨a, ?_⟩
    have hstream : (f a).val.1.flatMap TeamRAM.Event.choices ++ [] =
        r.val.1.flatMap TeamRAM.Event.choices ++ [] := by rw [hf, he]; exact congrArg (· ++ []) hx
    obtain ⟨het,heb,hem⟩ := DiagonalResidueRAM.unique_returns transmitRanges_native (f a).property r.property hstream
    exact Subtype.ext (Prod.ext het (Prod.ext heb hem))

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
