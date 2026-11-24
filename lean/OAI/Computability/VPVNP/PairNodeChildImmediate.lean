import OAI.Computability.VPVNP.PairNodeChildBankInit
import OAI.Computability.VPVNP.PairNodeChildCode
import OAI.Computability.VPVNP.PairNodeChildStage

/-!
# Child-argument scans on the eleven-operand vertex machine

A fixed register bank supplies every slot number. The initializer writes zero
and one as instruction literals and derives each following ordinal by addition.
The body uses a register copy in the slot's existing setup instruction. The
number of setup instructions and the field, packet and probe traces of the
child scan are therefore independent of the source of the slot numbers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.ChildCode.RegisterBank

open BurstRAM BurstRAM.PrivateRAM CompressorRecords Compression DFS ChildScan
open scoped Fin.CommRing

variable {a g w p r k : ℕ}

/-- Body instruction embedded at the existing parent, child and slot labels. -/
abbrev instruction (loc : Label a → Fin p) (reg : Fin 16 ↪ Fin r)
    (bank : Fin (2 ^ a) ↪ Fin r) (ret : Fin p) (j : Label a) : Instr w p r k :=
  instructionWith loc reg (.bank bank) ret j

private theorem resize_five (op : Instr 1 p r k) : (op.resize 5).resize w = op.resize w := by
  cases op <;> try rfl
  case constant dst v pc =>
    simp [Instr.resize, Nat.mod_eq_of_lt (v.isLt.trans (by decide : 2 ^ 1 < 32))]

/-- The body can be emitted at the five-bit literal width of the actual vertex
image even when the slot exponent is greater than five. -/
theorem resize_instruction (loc : Label a → Fin p) (reg : Fin 16 ↪ Fin r)
    (bank : Fin (2 ^ a) ↪ Fin r) (ret : Fin p) (j : Label a) :
    (instruction (w := 5) (k := k) loc reg bank ret j).resize w =
      instruction loc reg bank ret j := by
  have h := resize_instructionWith (w := 5) loc reg (ChildSlots.Names.bank (k := k) bank) ret j
  change (instructionWith (w := 5) loc reg (.bank bank) ret j).resize w = _
  rw [← h, resize_five]
  exact resize_instructionWith ..

variable {M : Machine w p r k} {loc : Label a → Fin p} {reg : Fin 16 ↪ Fin r}
variable {bank : Fin (2 ^ a) ↪ Fin r} {ret : Fin p} {initPC : Fin (2 ^ a) → Fin p}
variable {X : State a g} {T : IncidenceDirectory w} {A : Arena} {older cap : ℕ} {m : Memory w}

/-- Execute the parent header and argument scan with initialized ordinal
registers. Every supplied public word remains available to other vertex code. -/
theorem native_ready (code : ∀ j, M.code (loc j) = instruction loc reg bank ret j)
    (apart : ∀ i j, bank i ≠ reg j) (rep : T.ActualColumns X m)
    (xs : List (Child X)) (src : ℕ) (c : Config w p r)
    (names : ∀ j, c.reg (bank j) = (j.val : Word w)) (hc : c.pc = headerPC loc 0)
    (stored : (directory a older cap A T).Stored m (c.reg (reg 8)))
    (row : Row m (c.reg (reg 7)).val src (xs.map fun x => (childNode X older cap x.site : Word w)))
    (strideFit : cap + 2 < 2 ^ w) (nodes : ∀ x ∈ xs, childNode X older cap x.site < 2 ^ w)
    (packets : ∀ x ∈ xs, A.base (childNode X older cap x.site) + (x.payload X).length < 2 ^ w) :
    let qs := xs.map (Child.packet X older cap)
    let es := ChildHeader.events m (c.reg (reg 7)) (c.reg (reg 8)) ++ events X T m src xs
    ∃ d, d.pc = ret ∧ d.persistent = c.persistent ∧ d.privateMem = storePackets A qs c.privateMem ∧
      (∀ endAddr, scratch endAddr d.privateMem = writePackets A qs (scratch endAddr c.privateMem)) ∧
      (∀ i, ChildHeader.Preserved reg i → i ∉ mutableRegs reg → d.reg i = c.reg i) ∧
      ChildScan.Prefix M m c d (qs.flatMap Packet.bits) es := by
  obtain ⟨hh, hl⟩ := linkedWith M loc reg (.bank bank) ret code
  exact native_stageWith hh hl apart rep xs src c names hc stored row strideFit nodes packets

/-- A short argument tape cannot return through the register-based body. -/
theorem reject_ready (code : ∀ j, M.code (loc j) = instruction loc reg bank ret j)
    (apart : ∀ i j, bank i ≠ reg j) (rep : T.ActualColumns X m)
    (xs : List (Child X)) (src : ℕ) (c : Config w p r)
    (names : ∀ j, c.reg (bank j) = (j.val : Word w)) (hc : c.pc = headerPC loc 0)
    (stored : (directory a older cap A T).Stored m (c.reg (reg 8)))
    (row : Row m (c.reg (reg 7)).val src (xs.map fun x => (childNode X older cap x.site : Word w)))
    (strideFit : cap + 2 < 2 ^ w) (nodes : ∀ x ∈ xs, childNode X older cap x.site < 2 ^ w)
    (packets : ∀ x ∈ xs, A.base (childNode X older cap x.site) + (x.payload X).length < 2 ^ w)
    (bs : List Bool) (short : bs.length < (xs.flatMap (Child.payload X)).length) :
    ¬ Returns M c m bs := by
  obtain ⟨hh, hl⟩ := linkedWith M loc reg (.bank bank) ret code
  exact reject_stageWith hh hl apart rep xs src c names hc stored row
    strideFit nodes packets bs short

private theorem reg_outside (apart : ∀ i j, bank i ≠ reg j) (j : Fin 16) :
    reg j ∉ Set.range bank := fun ⟨i, hi⟩ => apart i j hi

/-- The complete hosted stage starts with arbitrary ordinal-register contents.
It fills the bank, reads the actual descriptor and consumes the placed child
arguments. The only added events are the bank's private initialization ticks. -/
theorem native_stage (init : ChildBankInit.Linked M initPC bank (headerPC loc 0))
    (code : ∀ j, M.code (loc j) = instruction loc reg bank ret j)
    (apart : ∀ i j, bank i ≠ reg j) (rep : T.ActualColumns X m)
    (xs : List (Child X)) (src : ℕ) (c : Config w p r) (hc : c.pc = initPC 0)
    (stored : (directory a older cap A T).Stored m (c.reg (reg 8)))
    (row : Row m (c.reg (reg 7)).val src (xs.map fun x => (childNode X older cap x.site : Word w)))
    (strideFit : cap + 2 < 2 ^ w) (nodes : ∀ x ∈ xs, childNode X older cap x.site < 2 ^ w)
    (packets : ∀ x ∈ xs, A.base (childNode X older cap x.site) + (x.payload X).length < 2 ^ w) :
    let qs := xs.map (Child.packet X older cap)
    let es := List.replicate (2 ^ a) .tick ++
      (ChildHeader.events m (c.reg (reg 7)) (c.reg (reg 8)) ++ events X T m src xs)
    ∃ d, d.pc = ret ∧ d.persistent = c.persistent ∧ d.privateMem = storePackets A qs c.privateMem ∧
      (∀ endAddr, scratch endAddr d.privateMem = writePackets A qs (scratch endAddr c.privateMem)) ∧
      (∀ i, i ∉ Set.range bank → ChildHeader.Preserved reg i → i ∉ mutableRegs reg →
        d.reg i = c.reg i) ∧ ChildScan.Prefix M m c d (qs.flatMap Packet.bits) es := by
  obtain ⟨mid, entry, state, priv, names, frame, before⟩ := ChildBankInit.native init m c hc
  have keep (j : Fin 16) := frame (reg j) (reg_outside apart j)
  obtain ⟨d, pc, persistent, memory, scratchEq, unchanged, body⟩ :=
    native_ready code apart rep xs src mid names entry (keep 8 ▸ stored) (keep 7 ▸ row)
      strideFit nodes packets
  rw [keep 7, keep 8] at body
  rw [priv] at memory scratchEq
  exact ⟨d, pc, persistent.trans state, memory, scratchEq,
    fun i hi h₁ h₂ => (unchanged i h₁ h₂).trans (frame i hi), before.trans body⟩

/-- Short-tape rejection holds already at the first bank instruction. -/
theorem reject_stage (init : ChildBankInit.Linked M initPC bank (headerPC loc 0))
    (code : ∀ j, M.code (loc j) = instruction loc reg bank ret j)
    (apart : ∀ i j, bank i ≠ reg j) (rep : T.ActualColumns X m)
    (xs : List (Child X)) (src : ℕ) (c : Config w p r) (hc : c.pc = initPC 0)
    (stored : (directory a older cap A T).Stored m (c.reg (reg 8)))
    (row : Row m (c.reg (reg 7)).val src (xs.map fun x => (childNode X older cap x.site : Word w)))
    (strideFit : cap + 2 < 2 ^ w) (nodes : ∀ x ∈ xs, childNode X older cap x.site < 2 ^ w)
    (packets : ∀ x ∈ xs, A.base (childNode X older cap x.site) + (x.payload X).length < 2 ^ w)
    (bs : List Bool) (short : bs.length < (xs.flatMap (Child.payload X)).length) :
    ¬ Returns M c m bs := by
  obtain ⟨mid, entry, _, _, names, frame, before⟩ := ChildBankInit.native init m c hc
  have keep (j : Fin 16) := frame (reg j) (reg_outside apart j)
  exact fun accepted => reject_ready code apart rep xs src mid names entry (keep 8 ▸ stored)
    (keep 7 ▸ row) strideFit nodes packets bs short ((before.returns bs).mp accepted)

end PairSimulation.NodeArguments.ChildCode.RegisterBank

end VPVNP
end Computability
end OAI
