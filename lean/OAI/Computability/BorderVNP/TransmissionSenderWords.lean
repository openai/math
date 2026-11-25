import OAI.Computability.BorderVNP.TransmissionMultiplicity
import OAI.Computability.BorderVNP.TransmissionTableSafety
import OAI.Computability.BorderVNP.TransmissionBudget

/-! # Multiplicity and runtime after scheduling the transmission directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ}

/-- The finite words indexed by the actual locally shared slots that pass every
remote source/link comparison. Intermediate memories are obtained by the canonical
decoder; the predicate contains no machine-run or permittedness hypotheses. -/
def SenderWords (rows : ℕ → Range w) (pub : Arg → Word w) (m : Memory w) :=
  let team := directoryFrame pub m 0
  let count := (directoryFrame pub m 13).val
  {b : Fin (choiceOffset rows team count) → Bool // ∀ i < count,
    (rows i).senderMatches team pub (tableMemory rows team pub m (decodeChoices rows team (List.ofFn b)) i)}

/-- The checked scheduler and destination allocations reduce the finite assignment
domain to the explicit physical sender comparisons. Each passing word has exactly
one history, realizes its decoded memory fold with positive signs, and pays only for
incident bits in addition to the public directory scan. -/
theorem scheduled_sender_equiv {f : BroadcastFrame} {width : Fin f.teams → Fin f.teams → ℕ}
    (rows : ℕ → Range w) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (a : Schedule f width pub m)
    (spans : ∀ i < (directoryFrame pub m 13).val, ScheduledRange f width (rows i))
    (kind : ∀ i < (directoryFrame pub m 13).val, (rows i).kind = 0 ∨ (rows i).kind = 1)
    (sep : ∀ i < (directoryFrame pub m 13).val,
      (rows i).scheduleSeparated (directoryFrame pub m 0) pub m f.teams)
    (sourceFit : ∀ i < (directoryFrame pub m 13).val,
      (rows i).selected (directoryFrame pub m 0) = some (some .sendData) →
        (rows i).source.val+(rows i).width.val ≤ 2^w)
    (table : ∀ bits : ℕ → ℕ → Bool, ∀ i < (directoryFrame pub m 13).val,
      rangeAt (tableMemory rows (directoryFrame pub m 0) pub m bits i)
        (cursorAt (directoryFrame pub m 12) 7 i) (cursorAt (directoryFrame pub m 20) 1 i) = rows i) :
    let team := directoryFrame pub m 0
    let count := (directoryFrame pub m 13).val
    ∃ E : SenderWords rows pub m ≃ TableReturn pub macros s m, ∀ b,
      (E b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b.val ∧
      (E b).val.2.2 = tableMemory rows team pub m (decodeChoices rows team (List.ofFn b.val)) count ∧
      traceCost (E b).val.1 ≤ 256*(1+count+∑ i ∈ Finset.range count, (rows i).incident team) ∧
      ∀ e ∈ (E b).val.1, e.sign = .plus := by
  let team := directoryFrame pub m 0
  let count := (directoryFrame pub m 13).val
  have ht : team.val = f.team := by simpa [team,directoryFrame,frameField,readings] using a.frame.1
  have hs := allTableArithmetic rows team a ht count spans sep
  have ok (b : SenderWords rows pub m) :
      ∀ i < count, (rows i).allowed team pub (tableMemory rows team pub m
        (decodeChoices rows team (List.ofFn b.val)) i) (decodeChoices rows team (List.ofFn b.val) i) :=
    fun i hi => (table_allowed_iff_senderMatches rows team a ht count spans kind sep sourceFit _ hi).mpr (b.property i hi)
  let H (b : Fin (choiceOffset rows team count) → Bool) := List.ofFn b
  have round (b : Fin (choiceOffset rows team count) → Bool) :
      tableChoiceBits rows team (decodeChoices rows team (H b)) count = H b :=
    tableChoiceBits_decodeChoices rows team (H b) List.length_ofFn
  let equiv : SenderWords rows pub m ≃ PermittedWords rows pub m := Equiv.subtypeEquivRight fun b => by
    constructor
    · intro matchBits
      exact ⟨decodeChoices rows team (H b), ok ⟨b,matchBits⟩, round b⟩
    · rintro ⟨bits,permit,stream⟩ i hi
      apply (table_allowed_iff_senderMatches rows team a ht count spans kind sep sourceFit _ hi).mp
      rw [← stream]
      exact (decodeChoices_allowed rows team pub m bits count i hi).mpr (permit i hi)
  obtain ⟨E, guesses⟩ := table_return_equiv rows pub macros m s table hs
  refine ⟨equiv.trans E, fun b => ?_⟩
  have stream := guesses (equiv b)
  change (E (equiv b)).val.1.flatMap TeamRAM.Event.choices = List.ofFn b.val at stream
  obtain ⟨mem,cost,signs⟩ := table_return_effects rows pub macros m s
    (decodeChoices rows team (H b.val)) (table _) (ok b) (E (equiv b)) (stream.trans (round b.val).symm)
  exact ⟨stream,mem,cost.trans (directory_tick_bound ..),signs⟩

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
