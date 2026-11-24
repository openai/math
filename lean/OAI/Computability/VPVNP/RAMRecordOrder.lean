import OAI.Computability.VPVNP.RAMMemory

/-!
# Deterministic comparison of complete RAM record slots

The sorting network moves a whole five-word record at each comparison.
The address and timestamp decide the primary order. When keys tie, the
kind and value distinguish the remaining payload using fields already in
the record. The unique empty slot sorts after every nonempty one.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMMemory

variable {Word : Type*}

/-- Tie-breaking rank of an initialization, read, or write in the sort order, numbered zero,
one, and two respectively. -/
def Kind.code : Kind → ℕ
  | .init => 0
  | .read => 1
  | .write => 2

private theorem kind_code_injective : Function.Injective Kind.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [Kind.code]

/-- Physical record with the network's deterministic total order. -/
structure OrderedSlot (Word : Type*) where
  /-- Optional memory record at a sorting wire, with the empty option representing a padding
  slot. -/
  record : Option (Record Word)

/-- Lexicographic sorting key for an occupied slot, using address and timestamp followed by
kind rank and value. Padding sorts above every record. -/
def OrderedSlot.code (s : OrderedSlot Word) :
    WithTop (Lex (Lex (ℕ × Lex (ℕ × Lex (ℕ × ℕ))) × Lex (ℕ × Word))) :=
  match s.record with
  | none => ⊤
  | some r => ↑(toLex (toLex (r.address, r.timestamp), toLex (Kind.code r.kind, r.value)))

private theorem slot_code_injective : Function.Injective (@OrderedSlot.code Word) := by
  rintro ⟨a⟩ ⟨b⟩ h
  cases a with
  | none =>
    cases b <;> simp_all [OrderedSlot.code]
  | some r =>
    cases b with
    | none => simp [OrderedSlot.code] at h
    | some s =>
      simp [OrderedSlot.code, Record.timestamp] at h
      obtain ⟨⟨ha, _, hc, hj⟩, hk, hv⟩ := h
      have he := kind_code_injective hk
      cases r
      cases s
      simp_all

instance [LinearOrder Word] : LinearOrder (OrderedSlot Word) :=
  LinearOrder.lift' OrderedSlot.code slot_code_injective

/-- Every ascending comparator output is ascending in the paper's primary
key even when a tie required consulting the remaining fields. -/
theorem paddedKey_mono [LinearOrder Word] : Monotone (fun s : OrderedSlot Word => paddedKey s.record) := by
  rintro ⟨a⟩ ⟨b⟩ h
  change OrderedSlot.code ⟨a⟩ ≤ OrderedSlot.code ⟨b⟩ at h
  cases a with
  | none =>
    cases b <;> simp_all [OrderedSlot.code, paddedKey]
  | some r =>
    cases b with
    | none => simp [paddedKey]
    | some s =>
      simp only [OrderedSlot.code, WithTop.coe_le_coe, Prod.Lex.toLex_le_toLex] at h
      simpa [paddedKey] using h.elim le_of_lt (fun e => e.1.le)

end RAMMemory

end VPVNP
end Computability
end OAI
