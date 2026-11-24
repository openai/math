import OAI.Computability.VPVNP.CompressorSlotOwnerRuns

/-!
# Gathering classifier keys for the arcs of one bundle

The classifier stores a key for every old arc at its absolute identifier.
The preimage scan stores a consecutive row of the identifiers assigned to
one bundle. The worker looks up each identifier's key and writes it at the
same offset in a separate row. The rank scan can then traverse these keys
without changing the original identifiers or the old widths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleKeys

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- Public words are the starting addresses of the ID row, global key column,
and destination row. The persistent cursor is an offset in the two rows. -/
def materializeKey : List (Op 3 3) :=
  [.stateWord 0, .publicWord 1 0, .binary .add 1 1 0, .read 2 1,
   .publicWord 1 1, .binary .add 1 1 2, .read 2 1,
   .publicWord 1 2, .binary .add 1 1 0, .write 1 2,
   .constant 1 1, .binary .add 0 0 1]

/-- Each row entry requires an ID read, an indirect key read, and one write. -/
def materializeEvents (p : Fin 3 → Word w) (mem : Memory w) (i : Word w) : List (Event w) :=
  let idAddr := p 0 + i
  let id := mem idAddr.val
  let keyAddr := p 1 + id
  let key := mem keyAddr.val
  [.tick, .tick, .tick, .read idAddr id, .tick, .tick, .read keyAddr key,
   .tick, .tick, .write (p 2 + i) key, .tick, .tick]

theorem materialize_native (p : Fin 3 → Word w) (mem : Memory w) (i : Word w) :
    let M := (template materializeKey 0).instantiate w p
    execute M.program 13 (M.program.start i) mem [] =
      some ⟨materializeEvents p mem i, some (i + 1)⟩ := by
  let M := (template materializeKey 0).instantiate w p
  change execute M.program (1 + materializeKey.length) ⟨M.entry, i, fun _ => 0, fun _ => 0⟩ mem [] = _
  rw [execute_template, run_eq_trace]
  rfl

theorem materialize_after (p : Fin 3 → Word w) (mem : Memory w) (i : Word w) :
    after mem (materializeEvents p mem i) =
      writeMemory mem (p 2 + i) (mem (p 1 + mem (p 0 + i).val).val) := rfl

theorem materialize_work (p : Fin 3 → Word w) (mem : Memory w) (i : Word w) :
    countProbes (materializeEvents p mem i) = 3 ∧ (materializeEvents p mem i).length = 12 := ⟨rfl, rfl⟩

/-- The output interval is disjoint from the ID row and both absolute-arc
columns. Each disjoint interval can lie on either side of the output. -/
structure KeyRowRegions (p : Fin 3 → Word w) (count arcCount widthBase : ℕ) : Prop where
  idsFit : (p 0).val + count ≤ 2 ^ w
  keysFit : (p 1).val + arcCount ≤ 2 ^ w
  destinationFits : (p 2).val + count ≤ 2 ^ w
  idsApart : (p 0).val + count ≤ (p 2).val ∨ (p 2).val + count ≤ (p 0).val
  keysApart : (p 1).val + arcCount ≤ (p 2).val ∨ (p 2).val + count ≤ (p 1).val
  widthsApart : widthBase + arcCount ≤ (p 2).val ∨ (p 2).val + count ≤ widthBase

/-- Gather the complete row in ID order. One call and three probes per entry
fill the destination. Every cell outside it keeps its value, including the
whole old-width column. -/
theorem materialize_run (p : Fin 3 → Word w) (initial : Memory w) (count arcCount widthBase : ℕ)
    (reg : KeyRowRegions p count arcCount widthBase)
    (legal : ∀ i < count, (initial ((p 0).val + i)).val < arcCount) :
    let P := ((template materializeKey 0).instantiate w p).program
    ∃ rs, SlotOwners.FilledRun P 13 3 12 count (p 2)
        (fun i => initial ((p 1).val + (initial ((p 0).val + i)).val)) initial rs ∧
      ∀ e < arcCount, after initial (eventLog rs) (widthBase + e) = initial (widthBase + e) := by
  intro P
  let value := fun i => initial ((p 1).val + (initial ((p 0).val + i)).val)
  have visit : SlotOwnerPass.Visit P 13 3 12 (p 2).val 0 count value initial := by
    intro j _ hj mem frame
    let i := Fin.ofNat (2 ^ w) j
    have hj' : j < count := by simpa only [Nat.zero_add] using hj
    have hidFit := reg.idsFit
    have hi : i.val = j := Nat.mod_eq_of_lt (by omega)
    have ha : (p 0 + i).val = (p 0).val + j := by
      rw [Fin.val_add, hi, Nat.mod_eq_of_lt (by omega)]
    have sameID : mem (p 0 + i).val = initial ((p 0).val + j) := by
      rw [ha]
      apply frame
      have := reg.idsApart
      omega
    let id := initial ((p 0).val + j)
    have hid : id.val < arcCount := legal j hj'
    have keyFit := reg.keysFit
    have hk : (p 1 + id).val = (p 1).val + id.val := by
      rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
    have sameKey : mem (p 1 + id).val = value j := by
      rw [hk]
      apply frame
      have := reg.keysApart
      omega
    have hd : p 2 + i = Fin.ofNat (2 ^ w) ((p 2).val + j) := by
      apply Fin.ext
      rw [Fin.val_add, hi, Fin.val_ofNat]
    have hs : i + 1 = Fin.ofNat (2 ^ w) (j + 1) := by
      apply Fin.ext
      simp [i, Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]
    refine ⟨materializeEvents p mem i, ?_, ?_, (materialize_work p mem i).1, (materialize_work p mem i).2⟩
    · rw [materialize_native p mem i, hs]
    · rw [materialize_after, hd, sameID]
      exact congrArg (writeMemory mem (Fin.ofNat (2 ^ w) ((p 2).val + j))) sameKey
  obtain ⟨rs, executed, cursor, filled, frame, len, calls, cost⟩ :=
    SlotOwnerPass.run P 13 3 12 (p 2).val 0 count value initial (by simpa using reg.destinationFits) visit
  refine ⟨rs, ⟨executed, by simpa using cursor, fun j hj => filled j (Nat.zero_le j) (by simpa using hj),
    fun a ha => frame a (by simpa using ha), len, calls, cost⟩, ?_⟩
  intro e he
  apply frame
  have := reg.widthsApart
  omega

end CompressorRecords.BundleKeys

end VPVNP
end Computability
end OAI
