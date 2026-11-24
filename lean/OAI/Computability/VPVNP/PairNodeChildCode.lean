import OAI.Computability.VPVNP.PairNodeChildHeader
import OAI.Computability.VPVNP.PairNodeChildScan

/-!
# A finite instruction table for a parent's child scan

For a fixed old degree, the table contains the parent header, the shared
child loop, and the setup, width lookup, and guess code of every outgoing
and incoming slot. All destinations refer to its finite label set except
the supplied return address. The same region can be embedded in a larger
vertex handler.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.ChildCode

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

/-- One incidence slot of an old site. The Boolean selects outgoing (false) or incoming (true),
and the ordinal selects one of the 2^a ports in that direction. -/
abbrev Slot (a : ℕ) := Bool × Fin (2 ^ a)
/-- Instruction labels within a single slot, divided into two for port setup, six for the width
lookup and seven for guessing and storing field bits. -/
abbrev SlotLabel := Fin 2 ⊕ (Fin 6 ⊕ Fin 7)
/-- Labels for the entire child scan. The alternatives distinguish the parent header, loop
guard, child address calculation and instructions specific to each incidence slot. -/
abbrev Label (a : ℕ) := Fin 17 ⊕ (Fin 3 ⊕ (Fin 7 ⊕ (Slot a × SlotLabel)))

/-- Number of child-scan instructions before the return destination. The shared blocks use 27
instructions, and each of the 2 · 2^a slots contributes 15. -/
def size (a : ℕ) := 17 + (3 + (7 + (2 * 2 ^ a) * (2 + (6 + 7))))

/-- Arithmetic numbering of all parent and slot instructions. -/
def number (a : ℕ) : Label a ≃ Fin (size a) :=
  let slots := (finTwoEquiv.symm.prodCongr (Equiv.refl (Fin (2 ^ a)))).trans finProdFinEquiv
  let part := ((Equiv.refl (Fin 2)).sumCongr finSumFinEquiv).trans finSumFinEquiv
  let bodies := (slots.prodCongr part).trans finProdFinEquiv
  let child := ((Equiv.refl (Fin 7)).sumCongr bodies).trans finSumFinEquiv
  let loop := ((Equiv.refl (Fin 3)).sumCongr child).trans finSumFinEquiv
  ((Equiv.refl (Fin 17)).sumCongr loop).trans finSumFinEquiv

variable {w p r k a : ℕ}

/-- Program counter of the j-th parent-header instruction in the supplied placement of
child-scan labels. -/
def headerPC (loc : Label a → Fin p) (j : Fin 17) := loc (.inl j)

/-- Restricts the label placement to the loop guard, address calculation and three blocks for
each slot, giving the destinations needed to link the child loop. -/
def sites (loc : Label a → Fin p) : ChildScan.Sites a p where
  guard i := loc (.inr (.inl i))
  address i := loc (.inr (.inr (.inl i)))
  slots :=
    { setup := fun i j => loc (.inr (.inr (.inr (i, .inl j))))
      header := fun i j => loc (.inr (.inr (.inr (i, .inr (.inl j)))))
      guess := fun i j => loc (.inr (.inr (.inr (i, .inr (.inr j))))) }

private def afterSlot (i : Slot a) : List (Slot a) → List (Slot a)
  | [] => []
  | j :: js => if i = j then js else afterSlot i js

private theorem slots_nodup (n : ℕ) : (ChildSlots.slots n).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨List.nodup_ofFn_ofInjective (fun _ _ h => congrArg Prod.snd h),
    List.nodup_ofFn_ofInjective (fun _ _ h => congrArg Prod.snd h), ?_⟩
  intro x h₁ h₂
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h₁
  obtain ⟨l, eq⟩ := List.mem_ofFn.mp h₂
  exact Bool.noConfusion (congrArg Prod.fst eq)

/-- Emit the relative instruction at a body label. The slot loader may read
a public operand or a private ordinal register. -/
def instructionWith (loc : Label a → Fin p) (reg : Fin 16 ↪ Fin r)
    (source : ChildSlots.Names (2 ^ a) r k)
    (ret : Fin p) : Label a → Instr w p r k
  | .inl j => ChildHeader.instruction (headerPC loc) reg ((sites loc).guard 0) j
  | .inr (.inl j) => ChildScan.guard (sites loc).guard reg ((sites loc).address 0) ret j
  | .inr (.inr (.inl j)) => ChildAddress.instruction (sites loc).address reg
      (ChildSlots.first (sites loc).slots ((sites loc).guard 0) (ChildSlots.slots (2 ^ a))) j
  | .inr (.inr (.inr (i, .inl j))) =>
      ChildSlots.setupWith (sites loc).slots (ChildScan.slotRegs reg) source i j
  | .inr (.inr (.inr (i, .inr (.inl j)))) =>
      FieldGuess.instruction ((sites loc).slots.header i)
        (ChildSlots.guessRegs (ChildScan.slotRegs reg)) ((sites loc).slots.guess i 0) j
  | .inr (.inr (.inr (i, .inr (.inr j)))) =>
      PrivateFields.instruction .guess ((sites loc).slots.guess i)
        (FieldGuess.fieldRegs (ChildSlots.guessRegs (ChildScan.slotRegs reg)))
        (ChildSlots.first (sites loc).slots ((sites loc).guard 0)
          (afterSlot i (ChildSlots.slots (2 ^ a)))) j

theorem resize_instructionWith (loc : Label a → Fin p) (reg : Fin 16 ↪ Fin r)
    (source : ChildSlots.Names (2 ^ a) r k) (ret : Fin p) (j : Label a) :
    (instructionWith (w := 1) loc reg source ret j).resize w =
      instructionWith loc reg source ret j := by
  rcases j with j | j | j | ⟨i, j | j | j⟩
  · fin_cases j <;> rfl
  · exact ChildScan.resize_guard ..
  · exact ChildAddress.resize_instruction ..
  · exact ChildSlots.resize_setupWith ..
  · exact FieldGuess.resize_instruction ..
  · exact PrivateFields.resize_instruction .guess _ _ _ j

/-- A machine containing this code satisfies every linkage condition, including
the return from the last slot to the original parent guard. -/
theorem linkedWith (M : Machine w p r k) (loc : Label a → Fin p) (reg : Fin 16 ↪ Fin r)
    (source : ChildSlots.Names (2 ^ a) r k) (ret : Fin p)
    (code : ∀ j, M.code (loc j) = instructionWith loc reg source ret j) :
    ChildHeader.Linked M (headerPC loc) reg ((sites loc).guard 0) ∧
      ChildScan.LinkedWith M (sites loc) reg source ret := by
  refine ⟨fun j => code (.inl j), ⟨fun j => code (.inr (.inl j)),
    fun j => code (.inr (.inr (.inl j))), ?_⟩⟩
  let allSlots := ChildSlots.slots (2 ^ a)
  have aux (xs : List (Slot a)) (hs : xs.Nodup)
      (suffix : ∀ i ∈ xs, afterSlot i allSlots = afterSlot i xs) :
      ChildSlots.LinkedWith M (sites loc).slots (ChildScan.slotRegs reg) source
        ((sites loc).guard 0) xs := by
    induction xs with
    | nil => trivial
    | cons i xs ih =>
      have hi := List.nodup_cons.mp hs
      have jump : afterSlot i allSlots = xs :=
        (suffix i List.mem_cons_self).trans (by simp [afterSlot])
      refine ⟨fun j => code (.inr (.inr (.inr (i, .inl j)))),
        fun j => code (.inr (.inr (.inr (i, .inr (.inl j))))), ?_, ih hi.2 ?_⟩
      · intro j
        have hit := code (.inr (.inr (.inr (i, .inr (.inr j)))))
        change M.code ((sites loc).slots.guess i j) = PrivateFields.instruction .guess _ _
          (ChildSlots.first (sites loc).slots ((sites loc).guard 0) (afterSlot i allSlots)) j at hit
        rwa [jump] at hit
      · intro j hj
        have ne : j ≠ i := fun eq => hi.1 (eq ▸ hj)
        simpa only [afterSlot, ite_eq_right ne] using suffix j (List.mem_cons_of_mem _ hj)
  exact aux allSlots (slots_nodup _) (fun _ _ => rfl)

/-- The original table obtains its slot names from public operands. -/
abbrev instruction (loc : Label a → Fin p) (reg : Fin 16 ↪ Fin r) (port : Fin (2 ^ a) → Fin k)
    (ret : Fin p) : Label a → Instr w p r k := instructionWith loc reg (.operand port) ret

theorem resize_instruction (loc : Label a → Fin p) (reg : Fin 16 ↪ Fin r)
    (port : Fin (2 ^ a) → Fin k) (ret : Fin p) (j : Label a) :
    (instruction (w := 1) loc reg port ret j).resize w = instruction loc reg port ret j :=
  resize_instructionWith ..

theorem linked (M : Machine w p r k) (loc : Label a → Fin p) (reg : Fin 16 ↪ Fin r)
    (port : Fin (2 ^ a) → Fin k) (ret : Fin p)
    (code : ∀ j, M.code (loc j) = instruction loc reg port ret j) :
    ChildHeader.Linked M (headerPC loc) reg ((sites loc).guard 0) ∧
      ChildScan.Linked M (sites loc) reg port ret := by
  obtain ⟨hh, hl⟩ := linkedWith M loc reg (.operand port) ret code
  exact ⟨hh, hl.guard, hl.address, hl.slots⟩

/-- A standalone parent handler has one terminal instruction in addition to
its child scan. Slot ordinals use the corresponding public parameter number. -/
def localPC (a : ℕ) (j : Label a) : Fin (size a + 1) := (number a j).castSucc

/-- Standalone 16-register machine template for a parent scan. It starts at the first header
instruction, loads slot ordinals from public operands and returns to a final accept
instruction. -/
def table (a : ℕ) : Template (size a + 1) 16 (2 ^ a) where
  literalWidth := 1
  entry := headerPC (localPC a) 0
  code := Fin.lastCases .accept fun j =>
    instruction (localPC a) (Function.Embedding.refl _) id (Fin.last (size a)) ((number a).symm j)

theorem table_linked (a w : ℕ) (pub : Fin (2 ^ a) → Word w) :
    let M := (table a).instantiate w pub
    let loc := localPC a
    let reg := Function.Embedding.refl (Fin 16)
    ChildHeader.Linked M (headerPC loc) reg ((sites loc).guard 0) ∧
      ChildScan.Linked M (sites loc) reg id (Fin.last (size a)) := by
  apply linked
  intro j
  simp only [Template.instantiate, table, localPC, Fin.lastCases_castSucc,
    Equiv.symm_apply_apply, resize_instruction]

end PairSimulation.NodeArguments.ChildCode

end VPVNP
end Computability
end OAI
