import OAI.Computability.VPVNP.PairShrinkHiddenCode
import OAI.Computability.VPVNP.PairShrinkHiddenWidth

/-!
# Reading and guessing one stored absorbed-field row

The width reader follows the dense ID to the selected term's repetition and
role payload cells. The private destination is computed from that same ID.
The finite guess loop consumes precisely the indicated number of bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkHiddenGuess

open BurstRAM PrivateRAM CompressorRecords ShrinkSliceArrays NodeArguments.ChildScan
open scoped Fin.CommRing

variable {W p r k : ℕ}

/-- Labels of the complete field scan, partitioned into its outer controls, 18 width-reader
instructions, and seven private guess instructions. -/
abbrev Stage := Control ⊕ (Fin 18 ⊕ Fin 7)

/-- Emit one row of the field scan, linking the width reader to the slot address calculation
and the private guess loop to the remaining-count decrement. -/
def instruction (pc : Stage → Fin p) (reg : Fin 22 ↪ Fin r) (done : Fin p) : Stage → Instr W p r k
  | .inl j => control (pc ∘ Sum.inl) reg (pc (.inr (.inl 0))) (pc (.inr (.inr 0))) done j
  | .inr (.inl j) => ShrinkHiddenWidth.instruction (pc ∘ Sum.inr ∘ Sum.inl) (widthRegs reg) (pc (.inl .slotOffset)) j
  | .inr (.inr j) => PrivateFields.instruction .guess (pc ∘ Sum.inr ∘ Sum.inr) (guessRegs reg) (pc (.inl .decrement)) j

theorem resize_instruction (pc : Stage → Fin p) (reg : Fin 22 ↪ Fin r) (done : Fin p) (j : Stage) :
    (instruction (W := 3) (k := k) pc reg done j).resize W = instruction pc reg done j := by
  rcases j with j | j | j
  · cases j <;> rfl
  · exact ShrinkHiddenWidth.resize_instruction ..
  · fin_cases j <;> rfl

/-- Every scan stage has its specified instruction in the machine at the supplied program
counter, using the given registers and exit address. -/
def Linked (M : Machine W p r k) (pc : Stage → Fin p) (reg : Fin 22 ↪ Fin r) (done : Fin p) :=
  ∀ j, M.code (pc j) = instruction pc reg done j

/-- Width word for the given dense hidden ID, obtained from the opposite-layout role's payload
plus the term repetition count times the selector width. -/
def Args.width (g : Args W) (m : Memory W) (id : Word W) :=
  supplyValue (supplyData (ShrinkHiddenWidth.coordinate (g.layout.toNat : Word W) id) g.selectorBits 0)
    (ShrinkHiddenWidth.rowBase g.termBase g.termStride id) m

/-- Width-reader trace for the field whose dense ID is stored at the supplied pointer. The ID
determines the term row and hidden role to probe. -/
def Args.header (g : Args W) (m : Memory W) (ptr : Word W) :=
  let id := m ptr.val
  ShrinkHiddenWidth.events m ptr (ShrinkHiddenWidth.rowBase g.termBase g.termStride id)
    (ShrinkHiddenWidth.coordinate (g.layout.toNat : Word W) id)

/-- Each pair consists of a dense hidden ID and the actual independent
bits to consume. Address and width conditions are checked against memory. -/
abbrev Row := ℕ × List Bool

/-- The external directory entry matches the field's dense ID, the term gives exactly its bit
length, and its private slot's exclusive bit end fits in a machine word. -/
def ValidAt (g : Args W) (m : Memory W) (ptr : ℕ) (e : Row) : Prop :=
  let id := m ((ptr : Word W).val)
  id.val = e.1 ∧ (g.width m id).val = e.2.length ∧ g.slot e.1+e.2.length < 2^W

/-- Each field in the list satisfies the ID, width, and slot-end checks at its successive
position in the owner's external row. -/
def ValidRows (g : Args W) (m : Memory W) (es : List Row) : Prop :=
  ∀ i : Fin es.length, ValidAt g m (g.row+i.val) es[i.val]

/-- Update private memory in row order by storing each field's bit list at the slot selected by
its dense ID. -/
def storeRows (base stride : ℕ) (rows : List Row) (old : Word W → Word W) :=
  rows.foldl (fun m e => PrivateFields.storeBits (base+e.1*stride) e.2 m) old

variable {M : Machine W p r k} {pc : Stage → Fin p} {reg : Fin 22 ↪ Fin r} {done : Fin p}

theorem controls (link : Linked M pc reg done) :
    ControlLinked M (pc ∘ Sum.inl) reg (pc (.inr (.inl 0))) (pc (.inr (.inr 0))) done := fun j => link (.inl j)

private theorem guesses (link : Linked M pc reg done) :
    PrivateFields.Linked M .guess (pc ∘ Sum.inr ∘ Sum.inr) (guessRegs reg) (pc (.inl .decrement)) :=
  fun j => link (.inr (.inr j))

theorem slot_run (link : Linked M pc reg done) (g : Args W) (m : Memory W) (c : Config W p r)
    (entry : c.pc = pc (.inl .slotOffset)) (ready : Ready g reg c) (id n : ℕ)
    (hid : (c.reg (reg 10)).val = id) (hw : (c.reg (reg 1)).val = n) :
    ∃ d, Prefix M m c d [] (List.replicate 3 .tick) ∧ d.pc = pc (.inr (.inr 0)) ∧
      d.reg (reg 2) = (g.slot id : Word W) ∧ d.reg (reg 1) = ((g.slot id+n : ℕ) : Word W) ∧
      (∀ i, i ≠ reg 1 → i ≠ reg 2 → d.reg i = c.reg i) ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  let a := c.put (pc (.inl .slotStart)) (reg 2) (c.reg (reg 10)*c.reg (reg 16))
  let b := a.put (pc (.inl .slotEnd)) (reg 2) (a.reg (reg 15)+a.reg (reg 2))
  let d := b.put (pc (.inr (.inr 0))) (reg 1) (b.reg (reg 2)+b.reg (reg 1))
  have s₁ : M.program.step c = .localStep a := by
    change (M.code c.pc).run M.publicData c = _
    rw [entry, link]; rfl
  have s₂ : M.program.step a = .localStep b := by
    change (M.code (pc (.inl .slotStart))).run M.publicData a = _
    rw [link]; rfl
  have s₃ : M.program.step b = .localStep d := by
    change (M.code (pc (.inl .slotEnd))).run M.publicData b = _
    rw [link]; rfl
  have pre : PrimedCounter.GuessWord.Prefix M c (List.replicate 3 .tick) d := .tick s₁ (.tick s₂ (.tick s₃ (.nil _)))
  have val {a : Word W} {n : ℕ} (h : a.val = n) : a = (n : Word W) := by
    subst n
    exact Fin.ext (Nat.mod_eq_of_lt a.isLt).symm
  refine ⟨d, fun fuel tail => pre.execute fuel m tail, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · simp [a,b,d,Config.put, Args.slot,ready.scratch,ready.stride,val hid]
  · simp [a,b,d,Config.put, Args.slot,ready.scratch,ready.stride,val hid,val hw]
  · intro i h1 h2; simp [a,b,d,Config.put,Function.update_of_ne h1,Function.update_of_ne h2]

private theorem stage_run (link : Linked M pc reg done) (g : Args W) (m : Memory W) (c : Config W p r)
    (ptr : ℕ) (e : Row) (entry : c.pc = pc (.inr (.inl 0))) (ready : Ready g reg c)
    (hp : c.reg (reg 5) = (ptr : Word W)) (hv : ValidAt g m ptr e) :
    ∃ d, Prefix M m c d [] (g.header m (ptr : Word W) ++ List.replicate 3 .tick) ∧
      d.pc = pc (.inr (.inr 0)) ∧ d.reg (reg 2) = (g.slot e.1 : Word W) ∧
      d.reg (reg 1) = ((g.slot e.1+e.2.length : ℕ) : Word W) ∧
      d.reg (reg 5) = c.reg (reg 5) ∧ d.reg (reg 14) = c.reg (reg 14) ∧ Frame reg c d ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  obtain ⟨u, header, atSlot, width, ident, keep, mem, persist⟩ := ShrinkHiddenWidth.native
    (M := M) (pc := pc ∘ Sum.inr ∘ Sum.inl) (reg := widthRegs reg) (done := pc (.inl .slotOffset))
    (fun j => link (.inr (.inl j))) m c entry
  have k' (i : Fin r) (h1 : i ≠ reg 1) (h10 : i ≠ reg 10) (h11 : i ≠ reg 11)
      (h12 : i ≠ reg 12) (h13 : i ≠ reg 13) : u.reg i = c.reg i := keep i h1 h10 h11 h12 h13
  have fu : Frame reg c u := fun i h => k' i (h 1 (by decide)) (h 10 (by decide))
    (h 11 (by decide)) (h 12 (by decide)) (h 13 (by decide))
  change u.reg (reg 10) = m (c.reg (reg 5)).val at ident
  change u.reg (reg 1) = supplyValue (supplyData
    (ShrinkHiddenWidth.coordinate (c.reg (reg 8)) (m (c.reg (reg 5)).val)) (c.reg (reg 9)) 0)
    (ShrinkHiddenWidth.rowBase (c.reg (reg 6)) (c.reg (reg 7)) (m (c.reg (reg 5)).val)) m at width
  rw [hp] at ident
  rw [hp, ready.layout, ready.selectors, ready.term, ready.termStride] at width
  change u.reg (reg 1) = g.width m (m (ptr : Word W).val) at width
  have header' : Prefix M m c u [] (g.header m (ptr : Word W)) := by
    change Prefix M m c u [] (ShrinkHiddenWidth.events m (c.reg (reg 5))
      (ShrinkHiddenWidth.rowBase (c.reg (reg 6)) (c.reg (reg 7)) (m (c.reg (reg 5)).val))
      (ShrinkHiddenWidth.coordinate (c.reg (reg 8)) (m (c.reg (reg 5)).val))) at header
    simpa only [Args.header, hp, ready.term, ready.termStride, ready.layout] using header
  obtain ⟨d, slot, dest, out, limit, k₂, hm, hs⟩ := slot_run link g m u atSlot (ready.frame fu) e.1 e.2.length
    ((congrArg Fin.val ident).trans hv.1) ((congrArg Fin.val width).trans hv.2.1)
  refine ⟨d, header'.trans slot, dest, out, limit, ?_, ?_, fu.trans ?_, hm.trans mem, hs.trans persist⟩
  · exact (k₂ _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans
      (k' _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
        (reg.injective.ne (by decide)) (reg.injective.ne (by decide)))
  · exact (k₂ _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans
      (k' _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
        (reg.injective.ne (by decide)) (reg.injective.ne (by decide)))
  · exact fun i hi => k₂ _ (hi 1 (by decide)) (hi 2 (by decide))

/-- Trace for one field through the width lookup, the three slot-address instructions, and the
private guesses of its bit list. -/
def fieldEvents (g : Args W) (m : Memory W) (ptr : ℕ) (e : Row) :=
  (g.header m (ptr : Word W) ++ List.replicate 3 .tick) ++ PrivateFields.events .guess e.2

theorem field_run (link : Linked M pc reg done) (g : Args W) (m : Memory W) (c : Config W p r)
    (ptr : ℕ) (e : Row) (entry : c.pc = pc (.inr (.inl 0))) (ready : Ready g reg c)
    (hp : c.reg (reg 5) = (ptr : Word W)) (hv : ValidAt g m ptr e) :
    ∃ d, Prefix M m c d e.2 (fieldEvents g m ptr e) ∧ d.pc = pc (.inl .decrement) ∧
      d.reg (reg 5) = c.reg (reg 5) ∧ d.reg (reg 14) = c.reg (reg 14) ∧ Frame reg c d ∧
      d.privateMem = PrivateFields.storeBits (g.slot e.1) e.2 c.privateMem ∧ d.persistent = c.persistent := by
  obtain ⟨u, stage, ep, dst, limit, h5, h14, fu, hm, hs⟩ := stage_run link g m c ptr e entry ready hp hv
  obtain ⟨d, guess, out⟩ := PrivateFields.guess_prefix (guesses link) u ep (g.slot e.1) e.2 dst limit
    ((ready.frame fu).one) hv.2.2
  have bits : Prefix M m u d e.2 (PrivateFields.events .guess e.2) := fun fuel tail => by
    simpa only [PrivateFields.events_bits, ite_true] using guess.execute fuel m tail
  have rest (i : Fin r) (h0 : i ≠ reg 0) (h2 : i ≠ reg 2) (h4 : i ≠ reg 4) : d.reg i = u.reg i :=
    out.frame _ h0 h2 h4
  refine ⟨d, stage.trans bits, out.pc, ?_, ?_, fu.trans ?_, ?_, out.persistent.trans hs⟩
  · exact (rest _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans h5
  · exact (rest _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans h14
  · exact fun i hi => rest i (hi 0 (by decide)) (hi 2 (by decide)) (hi 4 (by decide))
  · rw [out.privateMem, hm]

theorem field_short (link : Linked M pc reg done) (g : Args W) (m : Memory W) (c : Config W p r)
    (ptr : ℕ) (e : Row) (entry : c.pc = pc (.inr (.inl 0))) (ready : Ready g reg c)
    (hp : c.reg (reg 5) = (ptr : Word W)) (hv : ValidAt g m ptr e)
    (bits : List Bool) (short : bits.length < e.2.length) : ¬ DFS.Returns M c m bits := by
  obtain ⟨u, stage, ep, dst, limit, _, _, fu, _, _⟩ := stage_run link g m c ptr e entry ready hp hv
  intro accepts
  obtain ⟨fuel, report, ran⟩ := (stage.returns bits).mp accepts
  rw [PrivateFields.guess_short (guesses link) u ep _ _ dst limit (ready.frame fu).one hv.2.2 bits short fuel m] at ran
  contradiction

end PairSimulation.ShrinkHiddenGuess

end VPVNP
end Computability
end OAI
