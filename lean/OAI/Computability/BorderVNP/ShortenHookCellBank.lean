import OAI.Computability.BorderVNP.ShortenHookStaging
import OAI.Computability.BorderVNP.PackedCellAddressRead
import OAI.Computability.BorderVNP.CellSparseSemantics

/-!
# Hook equality records in the concrete compact cell bank

At either end of a hook, one equality record reads the appropriate slice of
that fine site's staging area and the actual physical wire. An internal
wire reads its canonical shared guess; a crossing wire reads the cell's
supplied endpoint word.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.SeedIntervals

open Crossing Packing CellSparse

/-- Relative start in the old site or the crossing-terminal staging word. -/
def CutDescriptor.stageOffset (d : CutDescriptor) (oldEnd : Bool) : ℕ :=
  if oldEnd then d.localStart else d.ordinal

variable {D edges ports sites : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (L : Network D P bits)
variable {C : Type} (cell : L.Site → C) (c : C) (edgeID : L.Edge ↪ Fin edges) (portID : P ↪ Fin ports)
variable (siteID : L.Site ↪ Fin sites) (aux : L.Site → ℕ)
variable (v : {v : L.Site // cell v = c}) (wire : {e : L.Edge // L.src e = v.val ∨ L.dst e = v.val})

/-- One fine site's staged word and its incident hook are tied inside the same cell's bank. -/
noncomputable def stagedHookRecord (d : CutDescriptor) (oldEnd : Bool) (base : ℕ) : Record :=
  let stage : Port := ⟨CellAddresses.siteBase L cell c siteID aux v + base,0,1⟩
  let canonical : Port := ⟨CellAddresses.wireBase L cell c edgeID portID aux v wire,0,1⟩
  d.hookRow oldEnd 1 stage canonical

/-- Exact sparse-record semantics on the three physical stack blocks, for both fine ends
and both internal and crossing physical hook cables. -/
theorem stagedHookRecord_valid (d : CutDescriptor) (oldEnd : Bool) (base : ℕ)
    (hw : L.width wire.val = d.span) (hroom : base + d.stageOffset oldEnd + d.span ≤ aux v.val)
    (boxes : List (List Factor)) (guessed : Fin (CellAddresses.guessedSize L cell c) → Bool)
    (staged : Fin (CellAddresses.siteSize L cell c aux) → Bool)
    (supplied : Fin (CellAddresses.suppliedSize L cell c) → Bool) :
    (stagedHookRecord L cell c edgeID portID siteID aux v wire d oldEnd base).Valid boxes
      (lookup (CellAddresses.bank L cell c aux guessed staged supplied)) ↔
    ∀ i : Fin d.span, CellAddresses.siteWords L cell c siteID aux staged v
        ⟨base + d.stageOffset oldEnd + i.val,by omega⟩ =
      (CellAddresses.wire L cell c edgeID portID v wire (Fin.cast hw.symm i)).elim guessed supplied := by
  let read := lookup (CellAddresses.bank L cell c aux guessed staged supplied)
  let stage : Port := ⟨CellAddresses.siteBase L cell c siteID aux v + base,0,1⟩
  let canonical : Port := ⟨CellAddresses.wireBase L cell c edgeID portID aux v wire,0,1⟩
  let sp := if oldEnd then d.oldPort stage else d.terminalPort stage
  have hs (i : Fin d.span) : read (sp.atBit 0 i.val) =
      CellAddresses.siteWords L cell c siteID aux staged v ⟨base + d.stageOffset oldEnd + i.val,by omega⟩ := by
    have he : sp.atBit 0 i.val = CellAddresses.siteBase L cell c siteID aux v + (base + d.stageOffset oldEnd + i.val) := by
      cases oldEnd <;> simp [sp,stage,CutDescriptor.oldPort,CutDescriptor.terminalPort,
        CutDescriptor.slice,CutDescriptor.stageOffset,Port.atBit,Nat.add_assoc]
    rw [he]
    exact CellAddresses.site_at L cell c aux siteID guessed staged supplied v ⟨base + d.stageOffset oldEnd + i.val, by omega⟩
  have hd (i : Fin d.span) : read (canonical.atBit 0 i.val) =
      (CellAddresses.wire L cell c edgeID portID v wire (Fin.cast hw.symm i)).elim guessed supplied := by
    have he : canonical.atBit 0 i.val = CellAddresses.wireBase L cell c edgeID portID aux v wire + i.val := by
      simp [canonical,Port.atBit]
    rw [he]
    exact CellAddresses.wire_at L cell c edgeID portID aux guessed staged supplied v wire (Fin.cast hw.symm i)
  change (∀ copy < 1, ∀ i < d.span, read (sp.atBit copy i) = read (canonical.atBit copy i)) ↔ _
  constructor
  · intro h i
    exact (hs i).symm.trans ((h 0 Nat.zero_lt_one i.val i.isLt).trans (hd i))
  · intro h copy hc i hi
    obtain rfl : copy = 0 := by omega
    exact (hs ⟨i,hi⟩).trans ((h ⟨i,hi⟩).trans (hd ⟨i,hi⟩).symm)

end Shortening.SeedIntervals

end BorderVNP
end Computability
end OAI
